%% An HTTP front for lean-check (R6), so a caller on another machine needs neither Erlang distribution nor a shared
%% cookie. OTP's httpd with this module as its only handler; started by lean_check_app when the application
%% environment has http => #{port := Port, token_file := File} (off by default).
%%
%%   POST /check   {"source": "...", "theorems": [..], "timeout": Ms, "isolate": bool}
%%   POST /prove   {"statement": "...", "tactics": [..], "lemmas": [..], "per_tactic_timeout": Ms, "search_timeout": Ms,
%%                  "timeout": Ms, "counterexample": bool}
%%   GET  /status
%% JSON in, the verdict as JSON out. Authorization: Bearer <token>, the token read from token_file and compared in
%% constant time. Limits (http map): max_body (bytes, default 1 MB), max_clients (default 8), max_timeout (ms, default
%% 300000: a request's timeout is capped). A request cannot widen the trusted base: "axioms" and "native_decide" are
%% refused (400).
-module(lean_check_http).
-export([start/1, do/1, to_json/1]).

-include_lib("inets/include/httpd.hrl").

start(#{port := Port, token_file := File} = Conf) ->
    {ok, Tok} = file:read_file(File),
    persistent_term:put({?MODULE, token}, crypto:hash(sha256, string:trim(Tok))),
    persistent_term:put({?MODULE, max_timeout}, maps:get(max_timeout, Conf, 300000)),
    inets:start(httpd, [{port, Port},
                        {bind_address, maps:get(bind_address, Conf, any)},
                        {server_name, "lean_check"},
                        {server_root, "/tmp"},
                        {document_root, "/tmp"},
                        {modules, [?MODULE]},
                        {max_body_size, maps:get(max_body, Conf, 1048576)},
                        {max_clients, maps:get(max_clients, Conf, 8)},
                        {keep_alive, false}]).

%% the httpd callback
do(#mod{method = Method, request_uri = Uri, entity_body = Body, parsed_header = Headers}) ->
    {Code, Out} = case authorised(Headers) of
                      false -> {401, #{error => <<"unauthorised">>}};
                      true -> route(Method, path(Uri), Body)
                  end,
    Json = iolist_to_binary(json:encode(to_json(Out))),
    {proceed, [{response, {response, [{code, Code}, {content_type, "application/json"},
                                      {content_length, integer_to_list(byte_size(Json))}], [Json]}}]}.

path(Uri) -> hd(string:split(Uri, "?")).

authorised(Headers) ->
    case proplists:get_value("authorization", Headers) of
        "Bearer " ++ Tok ->
            crypto:hash_equals(persistent_term:get({?MODULE, token}), crypto:hash(sha256, string:trim(Tok)));
        _ -> false
    end.

route("GET", "/status", _) -> {200, lean_check:status()};
route("POST", P, Body) when P =:= "/check"; P =:= "/prove" ->
    try json:decode(iolist_to_binary(Body)) of
        #{<<"axioms">> := _} -> {400, #{error => <<"axioms cannot be widened">>}};
        #{<<"native_decide">> := _} -> {400, #{error => <<"native_decide cannot be enabled">>}};
        Req when is_map(Req) -> call(P, Req);
        _ -> {400, #{error => <<"a JSON object is expected">>}}
    catch _:_ -> {400, #{error => <<"invalid JSON">>}}
    end;
route(_, _, _) -> {404, #{error => <<"not found">>}}.

call("/check", #{<<"source">> := Src} = Req) when is_binary(Src) ->
    {200, lean_check:check(Src, opts(Req, [theorems, timeout, isolate]))};
call("/prove", #{<<"statement">> := St} = Req) when is_binary(St) ->
    {200, lean_check:prove(St, opts(Req, [tactics, lemmas, per_tactic_timeout, search_timeout, timeout, counterexample, isolate]))};
call(_, _) -> {400, #{error => <<"missing source or statement">>}}.

%% the allowed options, timeouts capped
opts(Req, Keys) ->
    Max = persistent_term:get({?MODULE, max_timeout}),
    maps:from_list([{K, cap(K, V, Max)} || K <- Keys, {ok, V} <- [maps:find(atom_to_binary(K), Req)]]).

cap(K, V, Max) when (K =:= timeout orelse K =:= per_tactic_timeout orelse K =:= search_timeout), is_integer(V) -> min(V, Max);
cap(_, V, _) -> V.

%% a verdict as JSON terms: atoms as strings, {Tag, X} as #{Tag => X}, other tuples as lists
to_json(M) when is_map(M) -> maps:from_list([{key(K), to_json(V)} || {K, V} <- maps:to_list(M)]);
to_json(L) when is_list(L) -> [to_json(X) || X <- L];
to_json({Tag, X}) when is_atom(Tag) -> #{atom_to_binary(Tag) => to_json(X)};
to_json(T) when is_tuple(T) -> [to_json(X) || X <- tuple_to_list(T)];
to_json(A) when is_atom(A), A =/= true, A =/= false, A =/= null -> atom_to_binary(A);
to_json(X) -> X.

key(K) when is_atom(K) -> atom_to_binary(K);
key(K) -> K.
