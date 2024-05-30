krarup is a dialect of Erlang for quickly creating highly concurrent
data processing flows with ease.

## Usage
```erlang
% src/krarup_example.krp

-module(krarup_example).

async add(A, B) ->
    A + B.

main() ->
    Result = await add(1, 2),
    io:format("Count Result: ~p~n", [Result]),

    Results2 = await [add(2, 3), add(4, 5)],
    [io:format("Count Result: ~p~n", [R]) || R <- Results2],

> krarup_example:main().
Count Result: 3
Count Result: 5
Count Result: 7
```

## Install

```erlang
% rebar.config

{plugins, [{krarup, {git, "https://github.com/mpope9/krarup/", {branch, "main"}}}]}.
```

## Primer
The Erlang language is simple.  Once fluency is achieved rather quickly
then productivity is unrivaled.

We created krarup, a new Erlang dialect and a superset of Erlang, to provide
convenience keywords take care of some common process-related boilerplate.
These keywords can be used as quick building blocks to quickly create and
prototype concurrent data processing flows that can be promoted to production.

The key additions are `async` and `await` to simplify spawning worker processes.

Not everything is required to be a `gen_server`, and often simple processes
will do the trick.  However, async task spawning in Erlang is a bit cumbersome.
A common pattern is to create a function that replies to a caller.  This is
rather explicit boilerplate and it is often wrapped in a helper function,
but the pattern still rather common.

```erlang
add(A + B) ->
    Caller = self(),
    spawn(fun() ->
        Result = A + B,
        Caller ! {self(), Result}
    end),

Pid = add(1, 2),
receive
    {Pid, Result} ->
        io:format("", [Result])
end.
```

In Elixir the story is different with the `Task` module
([example from the docs](https://hexdocs.pm/elixir/1.16.2/Task.html)):
```elixir
task = Task.async(fn -> do_some_work() end)
res = do_some_other_work()
Task.await(task)
```
This module provides great ergonomics around spawning and waiting for tasks.
However, `Elixir.Task`s come with a high level of 'safety'. Links and monitors are
automatically created and it is expected that the consequences of these, such as
linked termination without error trapping and stray messages are dealt with by the
user as development mounts.

Further the `Elixir.Task` and `Elixir.Task.Supervisor` modules are not readily
available to Erlang users and are non-trivial to integrate.  The difficultly
in using Elixir in Erlang is a well-known issue with no clear answer for
every environment.

For simple repeatable tasks new syntactic sugar can be added to Erlang which can
increase developer productivity in designing, prototyping, and iterating on
process based or data-flow based models.

The benefit of being an Erlang superset is that once sufficient complexity has
been reached and one must reach for the more 'advanced' runtime features they
are readily available, and further a complete removal of this syntactic sugar
should be trivial.  An other benefit is full interoperability throughout the
BEAM ecosystem.  It is easy to call Erlang from other languages.

However, since krarup programs are just Erlang programs a meta-layer can also be
used.  A top-level Erlang application can compose and control multiple lower-level
krarup-written applications.  krarup fits naturally into the Erlang structured
concurrently and application building story.  Further, this controller can be
any other BEAM language, if an Elixir or Gleam or LFE controller is required
then it can be used with ease.

## Language Tour

This introduces a few new keywords to the language:
### async
* Async is defined on a function's definitions.
* This signals that a function can be awaited, or it can be called directly and pid will be returned.
* Unlike other languages `async` does not 'bleed'.  Async functions can be called from non-async functions.
    * Everything in Erlang can be `async`, unlike languages that added `async` after the fact.
* A pid and not a `Future` equivalent is returned. 

### await
* `await` is used at the expression level.
* Indicates that the current expression should block for a reply.
* `await` has the built in ability to wait on multiple async-spawned results in the order that they are defined.
* `await` can be called from any function, even non-`async` functions.

#### Quick async/await Note
The semantics of `async`/`await` are notability different than other language
implementations.  `await` can be used anywhere, not just in functions defined
with `async`.  Erlang can be considered `async` by default, so function
[coloring](https://www.tedinski.com/2018/11/13/function-coloring.html) and
propagation are not required.

The ergonomics of `async`/`await` are much more friendly than other languages.

### linked
`linked` is equivalent to calling `link/1` in the calling process.

Example:
```erlang
async add(A, B) -> A + B.

main() ->
    % Links to the child process and waits for the response.
    await linked add(1, 2).
```

### monitored
### supervised
### timeout<integer()>

## Control and Data Planes
krarup by default encourages the user to define the control and data planes
of their programs separately.  To achieve this, `await` can only wait on `async`
functions defined in the current module.  We refer to the code that deals with
concurrency and data-flow definition as the 'Control Plane'.
Code that performs data manipulation and validation is refered to as
the 'Data Plane'.  The krarup programming data plane is slightly
similar to the networking concept, but less so than the Control Plane.

Here is a small example that demonstrates how the Control and Data Planes enforce
simplicity to the 'hard parts' of concurrent programming, that averages the ages
cross 3 JSON documents stored in a directory called `data_dir/`.

```erlang
% src/averager.krp
-module(averager).

async process_file(FileName) ->
    json_decoder:handle_file(FileName).

async process_results(Ages) ->
    lists:sum(Ages) / length(Ages).

main() ->
    {ok, Files} = file:list_dirs("data_dir/"),

    Ages = await [linked process_file(File) || File <- Files],
    AverageAge = await process_results(Ages).

    io:format("Average Age: ~p~n", [AverageAge]).
```

```erlang
% src/processor.erl
-module(processor).

handle_file(FileName) ->
    {ok, Binary} = file:read_file(FileName),
    JSON = json_decoder:decode(Binary),
    maps:get(age, JSON).

```

This structures krarup programs naturally into their separate concerns.  The
code that deals with concurrency structure is separate from that which handles
data processing.  The logical split encourages simple and readable code for
future readers.  Of course, nothing prevents one from adding all of the JSON
decoding and manipulation into the `process_file` directly. This does prevent
moving the concurrency story outside of the current module.


## Inconsistency In Erlang
* `!` vs `receive` vs `spawn`/`link` (operator, keyword, BIF function, BIF function).

## Consistency With Erlang

### catch: Prior Art
The use of a single keyword in front of an expression is an already supported
pattern in Erlang that krarup does not introduce. The example is `catch`:
```erlang
catch asdf.
> asdf
```

krarup is an extension of this syntax.

### Runtime Error Catching
There are multiple existing langauge elements that perform runtime checks,
especially on `pid()` inputs. For example, the `!` operator checks the lhs
at runtime:
```erlang
2> asdf ! asdf.
** exception error: bad argument
     in operator  !/2
        called as asdf ! asdf
```

krarup leans on this pattern for it's support for pid-based keywords
and extends this pattern to lists of pids.

## Why Not A New Library
A natural question that comes up is: why not just a new or existing library?
Beyond the inconsistency story, these primitives _should_
exist at the language level as they do in other languages, but probably not in
Erlang itsself.  The ergonomics of these tools being built into a language vs
having an utility library is also a major difference, they should be a natural
extension.

## Why Not An EPP
An EPP is an official proposal to add a new feature to Erlang.

We don't necessarily feel that most of krarup should necessarily belong in
Erlang.  While some of the concepts would be very welcome to be integrated
they can be done so by people more familiar with creating languages.  Parts
of krarup are quite distinct and do not feel completely natural compared
to vanilla Erlang.  So we went with an implementation instead of a proposal.

## To Dos
- [x] `linked` support.
    - [ ] Use `spawn_link` in `async` function instead of `link/1` function.
- [ ] `supervised` support.
- [ ] `monitored` support.
- [ ] More user-friendly messages during parsing.
- [ ] Better recompile detection?
- [ ] Stronger safety checks for `await`.
    * Currently only checks if the expression is a `pid()` or a `[pid()]`.
    * Could consider using a `{awaitable, pid()}` for more safety.
- [ ] Better code generation.
    * The code that is currently generated is quite heavy and a bit ugly.
- [ ] Add default timeout to match `gen_server` behavior.
- [ ] `timeout` support.
- [ ] Consider a `dispatcher` behaviour and keyword to implement some kind of pooler.
