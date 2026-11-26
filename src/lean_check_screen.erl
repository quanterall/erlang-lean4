%% The screen in front of the workers: a submitted proof is untrusted input, and Lean can run code while it checks
%% (#eval, elaborators and macros, initialisers, unsafe and implemented_by definitions, foreign functions). The
%% source is stripped of comments and string literals and rejected if it uses any such construct, an import (a
%% check sees only the base environment), set_option other than the heartbeat and recursion limits, or (unless
%% allowed) native_decide. The worker's OS isolation (no network, a memory limit for the container) is the second
%% line; this screen is the first.
%%
%% It also finds the theorems a check must audit: the names after `theorem` and `lemma`, with the namespaces open
%% at that point.
-module(lean_check_screen).
-export([screen/2, theorems/1, theorem_lines/1, strip/1]).

-define(FORBIDDEN, [<<"#eval">>, <<"#exit">>, <<"#print">>, <<"run_cmd">>, <<"run_tac">>, <<"run_elab">>,
                    <<"run_meta">>, <<"elab">>, <<"elab_rules">>, <<"macro">>, <<"macro_rules">>, <<"syntax">>,
                    <<"declare_syntax_cat">>, <<"initialize">>, <<"builtin_initialize">>, <<"unsafe">>,
                    <<"implemented_by">>, <<"extern">>, <<"import">>, <<"opaque">>]).
-define(ALLOWED_OPTIONS, [<<"maxHeartbeats">>, <<"maxRecDepth">>]).

%% ok | {error, {forbidden, Construct}}; Opts: #{native_decide => true} allows native_decide
screen(Source, Opts) ->
    Words = words(strip(Source)),
    Forbidden = ?FORBIDDEN ++ case maps:get(native_decide, Opts, false) of
                                  true -> [];
                                  false -> [<<"native_decide">>]
                              end,
    case [W || W <- Words, lists:member(W, Forbidden)] of
        [W | _] -> {error, {forbidden, W}};
        [] -> options(Words)
    end.

%% set_option NAME: only the allowed ones
options([<<"set_option">>, Name | Rest]) ->
    case lists:member(Name, ?ALLOWED_OPTIONS) of
        true -> options(Rest);
        false -> {error, {forbidden, <<"set_option ", Name/binary>>}}
    end;
options([<<"set_option">>]) -> {error, {forbidden, <<"set_option">>}};
options([_ | Rest]) -> options(Rest);
options([]) -> ok.

%% the full names of the theorems and lemmas, in order
theorems(Source) -> theorems(words(strip(Source)), [], []).

theorems([], _, Acc) -> lists:reverse(Acc);
theorems([<<"namespace">>, N | Rest], Ns, Acc) -> theorems(Rest, [N | Ns], Acc);
theorems([<<"end">>, N | Rest], [N | Ns], Acc) -> theorems(Rest, Ns, Acc);
theorems([K, N | Rest], Ns, Acc) when K =:= <<"theorem">>; K =:= <<"lemma">> ->
    Full = lists:foldl(fun(P, A) -> <<P/binary, ".", A/binary>> end, N, Ns),
    theorems(Rest, Ns, [Full | Acc]);
theorems([_ | Rest], Ns, Acc) -> theorems(Rest, Ns, Acc).

%% the theorems with the line each starts on: [{FullName, Line}] (comments do not shift lines)
theorem_lines(Source) ->
    Lines = lists:enumerate(binary:split(strip(Source), <<"\n">>, [global])),
    {_, Acc} = lists:foldl(fun({L, Text}, {Ns, Acc0}) -> line_theorems(words(Text), L, Ns, Acc0) end, {[], []}, Lines),
    lists:reverse(Acc).

line_theorems([], _, Ns, Acc) -> {Ns, Acc};
line_theorems([<<"namespace">>, N | Rest], L, Ns, Acc) -> line_theorems(Rest, L, [N | Ns], Acc);
line_theorems([<<"end">>, N | Rest], L, [N | Ns], Acc) -> line_theorems(Rest, L, Ns, Acc);
line_theorems([K, N | Rest], L, Ns, Acc) when K =:= <<"theorem">>; K =:= <<"lemma">> ->
    Full = lists:foldl(fun(P, A) -> <<P/binary, ".", A/binary>> end, N, Ns),
    line_theorems(Rest, L, Ns, [{Full, L} | Acc]);
line_theorems([_ | Rest], L, Ns, Acc) -> line_theorems(Rest, L, Ns, Acc).

%% the words of the source: identifiers with dots and the commands starting with #; brackets, binders and
%% operators separate them (a name in `theorem foo (x : Nat)` is `foo`)
words(Src) ->
    Parts = re:split(Src, <<"[^A-Za-z0-9_.#'!?\\x{80}-\\x{10FFFF}]+">>, [unicode, {return, binary}]),
    [P || P <- Parts, P =/= <<>>].

%% the source without comments (-- line, /- block -/, nested) and string literals
strip(Src) when is_list(Src) -> strip(unicode:characters_to_binary(Src));
strip(Src) -> iolist_to_binary(strip(Src, 0, [])).

strip(<<>>, _, Acc) -> lists:reverse(Acc);
strip(<<"/-", Rest/binary>>, D, Acc) -> strip(Rest, D + 1, [<<" ">> | Acc]);
strip(<<"-/", Rest/binary>>, D, Acc) when D > 0 -> strip(Rest, D - 1, [<<" ">> | Acc]);
strip(<<"\n", Rest/binary>>, D, Acc) when D > 0 -> strip(Rest, D, [<<"\n">> | Acc]);    % lines are kept
strip(<<_/utf8, Rest/binary>>, D, Acc) when D > 0 -> strip(Rest, D, Acc);
strip(<<"--", Rest/binary>>, 0, Acc) ->
    case binary:split(Rest, <<"\n">>) of
        [_, After] -> strip(After, 0, [<<"\n">> | Acc]);
        [_] -> lists:reverse(Acc)
    end;
strip(<<"\"", Rest/binary>>, 0, Acc) -> strip(skip_string(Rest), 0, [<<" \"\" ">> | Acc]);
strip(<<C/utf8, Rest/binary>>, 0, Acc) -> strip(Rest, 0, [<<C/utf8>> | Acc]).

skip_string(<<"\\", _/utf8, Rest/binary>>) -> skip_string(Rest);
skip_string(<<"\"", Rest/binary>>) -> Rest;
skip_string(<<_/utf8, Rest/binary>>) -> skip_string(Rest);
skip_string(<<>>) -> <<>>.
