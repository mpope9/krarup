-module(krarup_utils).

-export([build_await_expr/2]).


build_await_expr({atom, _, await}, Expr) ->

    Counter =
        case erlang:get(krarup_counter) of
            undefined -> 0;
            C -> C
        end,

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
    GenCode = lists:flatten(io_lib:format(GenTemplate, FmtArgs)),

    {ok, GenTokenized, _} = erl_scan:string(GenCode),
    {ok, [GenParsed]} = erl_parse:parse_exprs(GenTokenized),
    erlang:put(krarup_counter, Counter + 1),
    GenParsed.


%build_await_expr_old({atom, _, await}, Expr) ->
%    RegisterPid = 'KrarupRegisterPid',
%    RegisterResult = 'KrarupRegisterResult',
%    ExprCallMatch = {match,1,{var,1,RegisterPid},Expr},
%
%    ClauseInternal =
%        [{clause,5,
%          [{tuple,5,[{var,5,RegisterPid},{var,5,RegisterResult}]}],
%          [],
%          [{var,6,RegisterResult}]}],
%    ExprReceive = {'receive',1,ClauseInternal},
%
%    % Build anonymous function to wrap function's definition.
%    ExprFun = {'fun',4, {clauses, [{clause, 4, [], [], [ExprCallMatch,ExprReceive]}]}},
%
%    % Call anonymous function in-line. Hacky but works for now.
%    {call,4, ExprFun, []}.
%

