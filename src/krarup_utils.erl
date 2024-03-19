-module(krarup_utils).

-export([build_await_expr/2]).


build_await_expr({atom, _, linked}, Expr) ->

    Counter = get_counter(),
    GenTemplate = "
    fun() ->
        KrarupRegisterValue~p = ~ts,
        link(KrarupRegisterValue~p),
        KrarupRegisterValue~p
    end().
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
