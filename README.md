krarup
=====

krarup is an Erlang dialect for composing concurrent data processing flows.

For more details [see the primer](https://github.com/mpope9/krarup/blob/main/primer.md).
For examples, see [examples/](examples/).

Currently based on Erlang 27.

Install
-------
```erlang
% rebar.config

{plugins, [{krarup, {git, "https://github.com/mpope9/krarup/", {branch, "main"}}}]}.
```

This will search for `.krp` files in the `src/` directory.

Example
-------
```erlang
% src/krarup_example.krp

-module(krarup_example).

async sum(List) ->
    lists:sum(List).

main() ->
    await linked sum([1, 2, 3]).
```

Build
-----

    $ rebar3 compile
