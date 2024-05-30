-module(parser_failures_test).
-moduledoc """
Tests parser failures.
""".

-include_lib("eunit/include/eunit.hrl").

-define(EXTERNAL_KRP, "test/external_mod.krp").
-define(EXTERNAL_ERL, "test/external_mod.erl").

-define(EXTERNAL_FAILURE_KRP, "test/external_failure.krp").

failure_test_() ->

    {setup, fun setup/0, fun cleanup/1, [
        {"Tests that an external module called with `await` does not parse.",
            ?_test(await_external_failure())}]}.

%% Setup should compile and load the test module.
setup() ->
    Mods = [{?EXTERNAL_KRP, ?EXTERNAL_ERL, external_mod}],
    krarup_test_utils:setup(Mods),
    ok.

%% Cleanup cleans up the test module.
cleanup(_) ->
    krarup_test_utils:cleanup([?EXTERNAL_ERL]),
    ok.

await_external_failure() ->
    ?assertThrow(
       {error, _},
       krarup:compile(?EXTERNAL_FAILURE_KRP, [{ok, ok}], [], [])).
