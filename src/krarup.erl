%%%-----------------------------------------------------------------------------
%%% %CopyrightBegin%
%%%
%%% (C) 2024, Matthew Pope
%%%
%%% %CopyrightEnd%
%%%-----------------------------------------------------------------------------
-module(krarup).
%-moduledoc """
%Main Krarup compiler.
%""".

-behaviour(rebar_compiler).

-export([init/1,

         % Compiler callbacks
         context/1,
         needed_files/4,
         dependencies/3,
         compile/4,
         clean/2

         % Provider callbacks.
        ]).

-define(COMPILE_PROVIDER, compile).
-define(NEW_PROVIDER, new).

-define(NAMESPACE, krp).
%-define(DEPS, [{default, app_discovery}]).


%-spec init(rebar_state:t()) -> {ok, rebar_state:t()}.
-spec init(term()) -> {ok, term()}.
init(State) ->
    Provider = providers:create([
        {name, ?COMPILE_PROVIDER},
        {namespace, ?NAMESPACE},
        {module, ?MODULE},
        {bare, true},
        %{deps, ?DEPS},
        {example, "rebar3 krp compile"},
        {opts, []},
        {short_desc, "Krarup compiler plugin"},
        {desc, ""}
    ]),
    State1 = rebar_state:add_provider(State, Provider),

    Provider2 = providers:create([
        {name, ?NEW_PROVIDER},
        {namespace, ?NAMESPACE},
        {module, ?MODULE},
        {bare, true},
        %{deps, ?DEPS},
        {example, "rebar3 krp new"},
        {opts, []},
        {short_desc, "Krarup application generator."},
        {desc, ""}
    ]),
    State2 = rebar_state:add_provider(State1, Provider2),

    %% If needing the new compiler module to take precedence over
    %% other ones (i.e. generating .erl files from another format):
    State3 = rebar_state:prepend_compilers(State2, [krarup]),
    {ok, State3}.


%% Provider Callbacks.


%% Compiler Callbacks.

context(AppInfo) ->
    Dir = rebar_app_info:dir(AppInfo),
    Mappings = [{".erl", filename:join([Dir, "src"])}],
    #{src_dirs => ["src"],
      include_dirs => [],
      src_ext => ".krp",
      out_mappings => Mappings}.

needed_files(_, FoundFiles, Mappings, AppInfo) ->
    FirstFiles = [],

    %% Remove first files from found files
    RestFiles = [Source || Source <- FoundFiles,
                           not lists:member(Source, FirstFiles),
                           rebar_compiler:needs_compile(Source, ".erl", Mappings)],

    Opts = rebar_opts:get(rebar_app_info:opts(AppInfo), krp_opts, []),
    Opts1 = update_opts(Opts, AppInfo),

    {{FirstFiles, Opts1}, {RestFiles, Opts1}}.

dependencies(_, _, _) ->
    [].

compile(Source, [{_, _}], Config, Opts) ->
    {ok, Contents} = file:read_file(Source),
    handle_parse(scan(binary_to_list(Contents)), Source, Config, Opts).

clean(XrlFiles, _AppInfo) ->
    rebar_file_utils:delete_each(
      [rebar_utils:to_list(re:replace(F, "\\.krp$", ".erl", [unicode]))
       || F <- XrlFiles]).

%% make includefile options absolute paths
update_opts(Opts, AppInfo) ->
    OutDir = rebar_app_info:out_dir(AppInfo),
    lists:map(fun({includefile, I}) ->
                      case filename:pathtype(I) =:= relative of
                          true ->
                              {includefile, filename:join(OutDir, I)};
                          false ->
                              {includefile, I}
                      end;
                 (O) ->
                      O
              end, Opts).

handle_parse({error, {_, _, Description}},  Source, Config, Opts) ->
    rebar_compiler:error_tuple(Source, Description, "", Config, Opts);
handle_parse(Ast,  Source, Config, Opts) ->
    Generated = [[erl_prettypr:format(A), "\n"] || A <- Ast],
    OutFile = rebar_utils:to_list(re:replace(Source, "\\.krp$", ".erl", [unicode])),
    WriteResult = file:write_file(OutFile, Generated),
    handle_write(WriteResult, Source, Config, Opts).

handle_write(ok, _, _, _) ->
    ok;
handle_write({error, Reason}, Source, Config, Opts) ->
    rebar_compiler:error_tuple(Source, atom_to_list(Reason), "", Config, Opts).


% https://stackoverflow.com/a/36039818
scan(String) when is_list(String)->
    scan(String++eof,[]). %% appended eof

scan({done, Result, LeftOverChars},Acc)->
    scan_done(Result,LeftOverChars,Acc);
scan({more, Continuation},Acc)->
    scan(erl_scan:tokens(Continuation,[],1),Acc);
scan(String,Acc) ->
    scan(erl_scan:tokens([],String,1),Acc).

scan_done({error,ErrorMsg,_Location},_LeftOverChars,_Acc)->
    ErrorMsg;
scan_done({eof,_Location},_LeftOverChars,Acc)->
    Acc;
scan_done({ok,Tokens,_Location},LeftOverChars,Acc)->
    case krarup_parse:parse_form(Tokens) of
    {ok,R}->scan(LeftOverChars,Acc++[R]);
    {error,R}->scan(LeftOverChars,R)
    end.
