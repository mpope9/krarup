
-module(krarup_project).
-behaviour(provider).

-include("krarup.hrl").

-export([init/1, do/1, format_error/1]).

-define(PROVIDER, new).

-spec init(rebar_state:t()) -> {ok, rebar_state:t()}.
init(State) ->
    {ok, State}.

-spec do(rebar_state:t()) -> {ok, rebar_state:t()} | {error, string()}.
do(State) ->
    io:format("new State: ~p~n", [State]),
    {ok, State}.

-spec format_error(any()) -> iolist().
format_error(Reason) ->
    io_lib:format("~p", [Reason]).
