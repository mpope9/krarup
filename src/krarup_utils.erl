-module(krarup_utils).

-export([build_await_expr/2,build_async_function/2,check_clauses/3]).

-include_lib("krarup.hrl").

%%------------------------------------------------------------------------------
%% APIs
%%------------------------------------------------------------------------------

-doc """
Builds an async function from the passed AST.
""".
-spec build_async_function({atom, term(), async}, term()) -> tuple().
build_async_function({atom, _, async}, Cs) ->
    Name = element(3, hd(Cs)),
    Arity = length(element(4, hd(Cs))),

    % Unique enough vars to save results.
    RegisterReturn = 'KrarupRegisterReturn',
    RegisterCaller = 'KrarupRegisterCaller',

    % Currently this only supports single head functions.
    Clauses = check_clauses(Cs, Name, Arity),
    [{clause,LnClauses,VarsClauses,What,Exprs}] = Clauses,

    ExprsRev = lists:reverse(Exprs),
    [ExprLast | ExprRevRest] = ExprsRev,

    % Save the final expression in the result register.
    LnExpr = element(2, ExprLast),
    ExprLastMatch = {match,LnExpr,{var,6,RegisterReturn},ExprLast},

    % Create new send from the result register to the caller register.
    ExprSend =
        {op,LnExpr+1,'!',
           {var,LnExpr+1,RegisterCaller},
           {tuple,LnExpr+1,
            [
             {call,LnExpr+1,{atom,LnExpr+1,self},[]},
             {var,LnExpr+1,RegisterReturn}
            ]}},
    ExprFunctionNew = lists:reverse([ExprSend,ExprLastMatch|ExprRevRest]),

    % Build anonymous function to wrap function's definition.
    ExprFun = {'fun',4, {clauses, [{clause, 4, [], [], ExprFunctionNew}]}},

    % Caller register assignment and spawn that encapulates the function's body.
    ExprMatchRegisterCall =
        {match,3,{var,3,RegisterCaller},{call,3,{atom,3,self},[]}},
    ExprSpawn = {call,4, {atom,4,spawn}, [ExprFun]},

    % Rebuild function definition.
    ExprsCallAndSpawn = [ExprMatchRegisterCall, ExprSpawn],
    ClausesNew = [{clause,LnClauses,VarsClauses,What,ExprsCallAndSpawn}],
    {function,?anno(hd(Cs)),Name,Arity,ClausesNew}.


build_await_expr({atom, _, linked}, Expr) ->

    Counter = get_counter(),
    GenTemplate = "
    begin
        KrarupRegisterValue~p = ~ts,
        link(KrarupRegisterValue~p),
        KrarupRegisterValue~p
    end.
    ",

    ExprString = erl_prettypr:format(Expr),
    FmtArgs = [Counter, ExprString, Counter, Counter],
    parse_gen(GenTemplate, FmtArgs, Counter);

build_await_expr({atom, _, await}, Expr) ->

    Counter = get_counter(),
    GenTemplate = "
    begin
        KrarupRegisterRecvFun~p = fun
            (KrarupRegisterPid~p) when is_pid(KrarupRegisterPid~p) ->
                receive
                    {KrarupRegisterPid~p, KrarupRegisterResult~p} ->
                        KrarupRegisterResult~p
                end;

            (_) ->
                error(badarg)
        end,
        KrarupRegisterValue~p = ~ts,
        case KrarupRegisterValue~p of
            KrarupRegisterMaybeList~p when is_list(KrarupRegisterValue~p) ->
                [
                    KrarupRegisterRecvFun~p(KrarupRegisterMaybePid~p)
                        || KrarupRegisterMaybePid~p <- KrarupRegisterMaybeList~p
                ];

            KrarupRegisterMaybePidInner~p ->
                KrarupRegisterRecvFun~p(KrarupRegisterMaybePidInner~p)
        end
    end.
    ",

    ExprString = erl_prettypr:format(Expr),
    FmtArgs1 = lists:duplicate(7, Counter),
    FmtArgs2 = lists:duplicate(10, Counter),
    FmtArgs = FmtArgs1 ++ [ExprString] ++ FmtArgs2,
    parse_gen(GenTemplate, FmtArgs, Counter).


check_clauses(Cs, Name, Arity) ->
    [case C of
         {clause,A,N,As,G,B} when N =:= Name, length(As) =:= Arity ->
             {clause,A,As,G,B};
         {clause,A,_N,_As,_G,_B} ->
             ret_err(A, "head mismatch")
     end || C <- Cs].

%%------------------------------------------------------------------------------
%% Helpers
%%------------------------------------------------------------------------------

% TODO: Merge with definition in the krarup_parse.yrl file.
-spec ret_err(_, _) -> no_return().
ret_err(Anno, S) ->
    %return_error(location(Anno), S).
    throw({error, {location(Anno), ?MODULE, S}}).

location(Anno) ->
    erl_anno:location(Anno).


parse_gen(GenTemplate, FmtArgs, Counter) ->
    GenCode = lists:flatten(io_lib:format(GenTemplate, FmtArgs)),

    {ok, GenTokenized, _} = erl_scan:string(GenCode),
    {ok, [GenParsed]} = erl_parse:parse_exprs(GenTokenized),
    bump_counter(Counter),
    GenParsed.

get_counter() ->
    case erlang:get(krarup_counter) of
        undefined -> 0;
        C -> C
    end.

bump_counter(Counter) ->
    erlang:put(krarup_counter, Counter + 1).
