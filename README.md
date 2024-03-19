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

Build
-----

    $ rebar3 compile
