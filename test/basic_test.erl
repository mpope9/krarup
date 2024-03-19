%-moduledoc """
%Basic test suite for the krarup compiler.
%Tests basic functionality of compiled modules.
%""".

-module(basic_test).
-include_lib("eunit/include/eunit.hrl").

-define(BASIC_KRP, "test/krarup_basic.krp").
-define(BASIC_ERL, "test/krarup_basic.erl").
-define(COMPILER_OPTS, [binary,verbose,report_errors,report_warnings]).

basic_module_test_() ->
    
    {setup, fun setup/0, fun cleanup/1, [
      {"Tests that an async function can be awaited on.", ?_test(await_function())},
      {"Tests that pid can be awaited on.", ?_test(await_pid())},
      {"Tests that a list of pids can be awaited on.", ?_test(await_list())},
      {"Tests a list of awaits.", ?_test(list_of_await())},
      {"Tests a list of awaiting on pids.", ?_test(list_of_await_pids())},
      {"Tests awaiting on a list of pids.", ?_test(list_of_pids_await())},

      {"Tests that the linked keyword spawns and links a process.", ?_test(linked())}
    ]}.

%% Setup should compile and load the test module.
setup() ->
    ok = krarup:compile(?BASIC_KRP, [{ok, ok}], [], []),
    {ok, _, CodeBin} = compile:file(?BASIC_ERL, ?COMPILER_OPTS),
    code:load_binary(krarup_basic, ?BASIC_ERL, CodeBin),
    ok.

%% Cleanup cleans up the test module.
cleanup(_) ->
    file:delete("test/krarup_basic.erl"),
    ok.

await_function() ->
    ?assertEqual(3, krarup_basic:await_function_test(1, 2)).

await_pid() ->
    ?assertEqual(3, krarup_basic:await_pid_test(1, 2)).

await_list() ->
    ?assertEqual([3, 7], krarup_basic:await_list_test(1, 2, 3, 4)).

list_of_await() ->
    ?assertEqual([3, 7], krarup_basic:list_of_await_test(1, 2, 3, 4)).

list_of_await_pids() ->
    ?assertEqual([3, 7], krarup_basic:list_of_await_pids_test(1, 2, 3, 4)).

list_of_pids_await() ->
    ?assertEqual([3, 7], krarup_basic:list_of_pids_await_test(1, 2, 3, 4)).

linked() ->
    {_, Links} = process_info(self(), links),
    LinkCount = length(Links),
    Pid = krarup_basic:linked_test(1, 2),
    {_, LinksNew} = process_info(self(), links),
    LinkCountNew = length(LinksNew),
    ?assertEqual(LinkCount + 1, LinkCountNew),
    Pid ! msg,
    ?assertEqual(3, krarup_basic:await_pid(Pid)).

