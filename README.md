krarup
=====

krarup is an Erlang dialect for composing concurrent data processing flows.

For more details and examples, [see the primer](https://github.com/mpope9/krarup/blob/main/primer.md).

Install
-------
```erlang
% rebar.config

{deps, [krarup]}.
{plugins, [krarup]}.
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
    async linked sum([1, 2, 3]).
```

Build
-----

    $ rebar3 compile
