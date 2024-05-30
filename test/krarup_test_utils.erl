-module(krarup_test_utils).

-export([setup/1, cleanup/1]).

-include_lib("eunit/include/eunit.hrl").

-define(COMPILER_OPTS, [binary,verbose,report_errors,report_warnings]).

setup(Mods) ->
    lists:foreach(
      fun({Krp, Erl, Mod}) ->
              ok = krarup:compile(Krp, [{ok, ok}], [], []),
              {ok, _, CodeBin} = compile:file(Erl, ?COMPILER_OPTS),
              X = code:load_binary(Mod, Erl, CodeBin),
              ?debugFmt("~p", [X])
      end, Mods).

cleanup(Files) ->
    [file:delete(File) || File <- Files].
