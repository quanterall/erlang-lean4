%% lean-check: Lean 4 proof checking for Erlang.
%%
%%   lean_check:check(Source) / check(Source, Opts) -> Verdict
%%
%% Source is Lean 4 code checked in a fresh child of the base environment (by default `import Mathlib`). The
%% verdict is a map:
%%   status     valid | invalid | timeout | unavailable
%%   reason     why it is not valid: forbidden construct, errors, sorry, missing theorem, axioms not approved,
%%              no theorem to check
%%   theorems   the theorems audited, each with its own status and errors, its axioms, and its statement as Lean
%%              elaborated it (coercions shown)
%%   errors     Lean's error messages: #{line, column, message}
%%   goals      (invalid only) what is left to prove: per error and per sorry #{line, column, error, goals => [Goal]},
%%              the goal state at that point as Lean prints it (at most 8, each clipped to 2000 characters)
%%   elapsed_ms
%% valid means: the source passed the screen, Lean reported no error and no sorry, and every theorem exists and uses
%% only the approved axioms (by default propext, Classical.choice, Quot.sound: Lean's standard ones).
%%
%% Opts: theorems => [Name] (default: every theorem and lemma in the source), timeout => Ms (default 120000),
%% axioms => [Name] (the approved axioms), native_decide => boolean() (default false: it would add Lean's compiler to
%% the trusted base), isolate => boolean() (default true: the source in its own namespace, names reported without it).
-module(lean_check).
-export([check/1, check/2, prove/2, syntax_notes/0, status/0]).

-define(APPROVED, [<<"propext">>, <<"Classical.choice">>, <<"Quot.sound">>]).

check(Source) -> check(Source, #{}).

check(Source0, Opts) ->
    Source = unicode:characters_to_binary(Source0),
    T0 = erlang:monotonic_time(millisecond),
    Timeout = maps:get(timeout, Opts, 120000),
    V = case lean_check_screen:screen(Source, Opts) of
            {error, Why} -> verdict(invalid, Why, [], [], T0);
            ok ->
                Names = [to_bin(N) || N <- maps:get(theorems, Opts, lean_check_screen:theorems(Source))],
                case Names of
                    [] -> verdict(invalid, no_theorem, [], [], T0);
                    _ -> run(Source, Names, Timeout, Opts, T0)
                end
        end,
    finish(V).

%% each check in its own namespace (isolate, default true): no name can clash with Mathlib's, and the names are
%% reported without the prefix; Lean's line numbers are shifted back by the line the namespace adds
run(Source, Names, Timeout, Opts, T0) ->
    {Wrapped, Prefix, Shift} =
        case maps:get(isolate, Opts, true) of
            true ->
                P = <<"LeanCheck.C", (integer_to_binary(erlang:unique_integer([positive])))/binary>>,
                {<<"namespace ", P/binary, "\n", Source/binary, "\nend ", P/binary, "\n">>, <<P/binary, ".">>, 1};
            false -> {Source, <<>>, 0}
        end,
    case lean_check_pool:checkout(Timeout) of
        {error, no_worker} -> verdict(unavailable, no_worker, [], [], T0);
        {ok, W} ->
            Left = max(1000, Timeout - (erlang:monotonic_time(millisecond) - T0)),
            R = lean_check_worker:run(W, Wrapped, [<<Prefix/binary, N/binary>> || N <- Names], Left),
            lean_check_pool:checkin(W),
            judge(R, Names, Opts#{source => Source, prefix => Prefix, shift => Shift}, T0)
    end.

judge({error, timeout}, _, _, T0) -> verdict(timeout, timeout, [], [], T0);
judge({error, {crashed, Why}}, _, _, T0) -> verdict(unavailable, {worker_crashed, Why}, [], [], T0);
judge({ok, #{messages := Msgs0, axioms := Axioms} = Out0}, Names, Opts, T0) ->
    #{source := Source, prefix := Prefix, shift := Shift} = Opts,
    % positions back to the user's lines; the prefix out of the texts
    Unprefix = fun(B) when Prefix =:= <<>> -> B; (B) -> binary:replace(B, Prefix, <<>>, [global]) end,
    Msgs = [M#{<<"pos">> => shift(maps:get(<<"pos">>, M, #{}), Shift), <<"data">> => Unprefix(maps:get(<<"data">>, M, <<>>))}
            || M <- Msgs0],
    Out = Out0#{tactics => [T#{<<"pos">> => shift(maps:get(<<"pos">>, T, #{}), Shift)} || T <- maps:get(tactics, Out0, [])],
                sorry_goals => [Sg#{<<"pos">> => shift(maps:get(<<"pos">>, Sg, #{}), Shift)} || Sg <- maps:get(sorry_goals, Out0, [])]},
    Approved = [to_bin(A) || A <- maps:get(axioms, Opts, ?APPROVED)],
    Errors = [#{line => maps:get(<<"line">>, maps:get(<<"pos">>, M, #{}), 0),
                column => maps:get(<<"column">>, maps:get(<<"pos">>, M, #{}), 0),
                message => maps:get(<<"data">>, M, <<>>)}
              || #{<<"severity">> := <<"error">>} = M <- Msgs],
    SorryLines = [maps:get(<<"line">>, maps:get(<<"pos">>, Sg, #{}), 0) || Sg <- maps:get(sorry_goals, Out, [])],
    Ranges = ranges(lean_check_screen:theorem_lines(Source)),
    Theorems = [theorem(N, maps:get(<<Prefix/binary, N/binary>>, Axioms, {missing, none}), Unprefix, Approved,
                        maps:get(N, Ranges, undefined), Errors, SorryLines)
                || N <- Names],
    Reason = if
                 Errors =/= [] -> errors;
                 SorryLines =/= [] -> sorry;
                 true ->
                     case [N || #{name := N, axioms := missing} <- Theorems] of
                         [M | _] -> {missing_theorem, M};
                         [] ->
                             case [{N, A} || #{name := N, axioms := As} <- Theorems, is_list(As), A <- As,
                                             not lists:member(A, Approved)] of
                                 [] -> none;
                                 Bad -> {axioms_not_approved, Bad}
                             end
                     end
             end,
    Infos = [D || #{<<"severity">> := <<"info">>, <<"data">> := D} <- Msgs],
    case Reason of
        none -> (verdict(valid, none, Theorems, [], T0))#{infos => Infos};
        _ -> (verdict(invalid, Reason, Theorems, Errors, T0))#{goals => goals(Msgs, Out),
                                                               hints => lean_check_hints:hints(Source, Errors),
                                                               infos => Infos}
    end.

shift(#{<<"line">> := L} = Pos, Shift) -> Pos#{<<"line">> => max(1, L - Shift)};
shift(Pos, _) -> Pos.

%% the lines each theorem spans: from its first line to the line before the next theorem
ranges(Lines) ->
    Sorted = lists:keysort(2, Lines),
    Ends = [L - 1 || {_, L} <- tl(Sorted ++ [{x, 1 bsl 30}])],
    maps:from_list([{N, {L, E}} || {{N, L}, E} <- lists:zip(Sorted, Ends)]).

%% one theorem's own verdict (R7) and its statement as Lean elaborated it (R4)
theorem(Name, {Axioms, Statement}, Unprefix, Approved, Range, Errors, SorryLines) ->
    In = fun(L) -> case Range of {A, B} -> L >= A andalso L =< B; undefined -> true end end,
    Own = [E || #{line := L} = E <- Errors, In(L)],
    Status = if
                 Own =/= [] -> invalid;
                 Axioms =:= missing -> invalid;
                 true ->
                     case lists:any(In, SorryLines) orelse [A || A <- Axioms, not lists:member(A, Approved)] =/= [] of
                         true -> invalid;
                         false -> valid
                     end
             end,
    #{name => Name, axioms => Axioms, status => Status, errors => Own,
      statement => case Statement of none -> none; _ -> Unprefix(Statement) end}.

%% record the check (counts, times) and log one line without the source
finish(#{status := St, reason := R, elapsed_ms := Ms, theorems := Ts} = V) ->
    lean_check_pool:record(St, Ms),
    logger:info("lean_check ~p ~0p ~b ms ~0p", [St, R, Ms, [N || #{name := N} <- Ts]]),
    V.

%% the open goals of an invalid verdict: for each error, the goals of the tactic at its position (or, for "unsolved
%% goals", those Lean prints in the message), then the goal of each sorry; at most ?MAX_GOALS entries, each goal
%% clipped to ?GOAL_CHARS characters
-define(MAX_GOALS, 8).
-define(GOAL_CHARS, 2000).
goals(Msgs, Out) ->
    Tactics = maps:get(tactics, Out, []),
    At = fun(Pos) -> [G || #{<<"pos">> := P, <<"goals">> := G} <- Tactics, P =:= Pos] end,
    FromErrors =
        [begin
             Pos = maps:get(<<"pos">>, M, #{}),
             Data = maps:get(<<"data">>, M, <<>>),
             [First | Rest] = binary:split(Data, <<"\n">>),
             Gs = case {At(Pos), First} of
                      {[G | _], _} -> [G];
                      {[], <<"unsolved goals">>} -> split_goals(Rest);
                      _ -> []
                  end,
             #{line => maps:get(<<"line">>, Pos, 0), column => maps:get(<<"column">>, Pos, 0),
               error => clip(First), goals => [clip(G) || G <- Gs]}
         end || #{<<"severity">> := <<"error">>} = M <- Msgs],
    FromSorries = [#{line => maps:get(<<"line">>, maps:get(<<"pos">>, S0, #{}), 0),
                     column => maps:get(<<"column">>, maps:get(<<"pos">>, S0, #{}), 0),
                     error => <<"sorry">>, goals => [clip(maps:get(<<"goal">>, S0, <<>>))]}
                   || S0 <- maps:get(sorry_goals, Out, [])],
    lists:sublist(FromErrors ++ FromSorries, ?MAX_GOALS).

%% the goals in the rest of an "unsolved goals" message: separated by blank lines
split_goals([]) -> [];
split_goals(Lines) ->
    [G || G <- binary:split(iolist_to_binary(lists:join(<<"\n">>, Lines)), <<"\n\n">>, [global]), G =/= <<>>].

clip(B) when byte_size(B) =< ?GOAL_CHARS -> B;
clip(B) -> <<(string:slice(B, 0, ?GOAL_CHARS))/binary, "…"/utf8>>.

verdict(Status, Reason, Theorems, Errors, T0) ->
    #{status => Status, reason => Reason, theorems => Theorems, errors => Errors,
      elapsed_ms => erlang:monotonic_time(millisecond) - T0}.

%% the pool: workers, free, busy, waiting callers
status() -> lean_check_pool:status().

%%% Proof search (prove/2)

-define(DEFAULT_TACTICS, [<<"rfl">>, <<"decide">>, <<"norm_num">>, <<"simp">>, <<"ring">>, <<"omega">>, <<"linarith">>,
                          <<"nlinarith">>, <<"positivity">>, <<"field_simp; ring">>,
                          % for implications: the hypotheses introduced first
                          <<"intros; linarith">>, <<"intros; nlinarith">>, <<"exact?">>]).
-define(ALLOWED_TACTICS, ?DEFAULT_TACTICS ++ [<<"aesop">>, <<"simp_all">>, <<"gcongr">>, <<"tauto">>, <<"apply?">>]).
-define(SEARCH, [<<"exact?">>, <<"apply?">>]).

%% prove(Statement, Opts): Statement is a theorem without its proof ("theorem t (n : ℕ) : Even (n * (n + 1))"); the
%% tactics are tried in order, each within per_tactic_timeout (default 20000 ms), all within timeout (default 120000),
%% and the first that proves it is the proof. A search tactic's suggestion ("Try this: exact ...") becomes the proof
%% and is checked again on its own, so a valid verdict rests on an ordinary proof. The verdict is check/2's, with
%% proof, source and tried => [#{tactic, result, ms}]; when nothing proves it: invalid, reason no_proof_found.
%% Opts: tactics => [..] (from the allowed set only), lemmas => [Term] (hint terms, e.g. <<"sq_nonneg (x - 3)">>: then
%% nlinarith, linarith and simp are also tried with them), per_tactic_timeout (default 20000), search_timeout (exact?,
%% apply?; default 90000), timeout (default 120000; with exact? in the list it may need 180000), counterexample => true (when
%% nothing proves it, Mathlib's plausible looks for a counterexample: counterexample => <<"x := 1/2">>; the verdict
%% stays invalid), and check/2's options.
prove(Statement0, Opts) ->
    Statement = string:trim(unicode:characters_to_binary(Statement0)),
    T0 = erlang:monotonic_time(millisecond),
    Lemmas = [to_bin(L) || L <- maps:get(lemmas, Opts, [])],
    Tactics0 = [to_bin(T) || T <- maps:get(tactics, Opts, ?DEFAULT_TACTICS)],
    % with lemmas (hint terms such as sq_nonneg (x - 3)): nlinarith, linarith and simp with them, before the search
    Tactics = case Lemmas of
                  [] -> Tactics0;
                  _ ->
                      L = iolist_to_binary(lists:join(<<", ">>, Lemmas)),
                      With = [<<"nlinarith [", L/binary, "]">>, <<"intros; nlinarith [", L/binary, "]">>,
                              <<"linarith [", L/binary, "]">>, <<"simp [", L/binary, "]">>],
                      {Before, After} = lists:splitwith(fun(T) -> not lists:member(T, ?SEARCH) end, Tactics0),
                      Before ++ With ++ After
              end,
    case {binary:match(Statement, <<":=">>), [T || T <- Tactics0, not lists:member(T, ?ALLOWED_TACTICS)]} of
        {{_, _}, _} -> verdict(invalid, statement_has_proof, [], [], T0);
        {_, [Bad | _]} -> verdict(invalid, {tactic_not_allowed, Bad}, [], [], T0);
        {nomatch, []} ->
            case lean_check_screen:screen(Statement, Opts) of
                {error, Why} -> verdict(invalid, Why, [], [], T0);
                ok -> attempt(Statement, Tactics, Opts, T0, [])
            end
    end.

attempt(Statement, [], Opts, T0, Tried) ->
    V = (verdict(invalid, no_proof_found, [], [], T0))#{tried => lists:reverse(Tried)},
    case maps:get(counterexample, Opts, false) of
        true -> counterexample(Statement, Opts, V);
        false -> V
    end;
attempt(Statement, [Tac | Rest], Opts, T0, Tried) ->
    Left = maps:get(timeout, Opts, 120000) - (erlang:monotonic_time(millisecond) - T0),
    case Left =< 0 of
        true -> (verdict(invalid, no_proof_found, [], [], T0))#{tried => lists:reverse([#{tactic => Tac, result => skipped, ms => 0} | Tried])};
        false ->
            % a search (exact?, apply?) needs longer than one tactic: about 30 s for Even (n * (n + 1)) on full Mathlib
            Budget = min(Left, case lists:member(Tac, ?SEARCH) of
                                   true -> maps:get(search_timeout, Opts, 90000);
                                   false -> maps:get(per_tactic_timeout, Opts, 20000)
                               end),
            Src = <<Statement/binary, " := by\n  ", Tac/binary>>,
            T1 = erlang:monotonic_time(millisecond),
            V = check(Src, (maps:without([tactics], Opts))#{timeout => Budget}),
            Ms = erlang:monotonic_time(millisecond) - T1,
            case {lists:member(Tac, ?SEARCH), maps:get(status, V)} of
                {false, valid} ->
                    V#{proof => <<"by ", Tac/binary>>, source => Src,
                       tried => lists:reverse([#{tactic => Tac, result => proved, ms => Ms} | Tried])};
                {true, valid} ->
                    % the search's suggestion, checked again on its own
                    case suggestion(V) of
                        none -> attempt(Statement, Rest, Opts, T0, [#{tactic => Tac, result => no_suggestion, ms => Ms} | Tried]);
                        Sug ->
                            Src2 = <<Statement/binary, " := by\n  ", Sug/binary>>,
                            V2 = check(Src2, (maps:without([tactics], Opts))#{timeout => Budget}),
                            Ms2 = erlang:monotonic_time(millisecond) - T1,
                            case maps:get(status, V2) of
                                valid -> V2#{proof => <<"by ", Sug/binary>>, source => Src2,
                                             tried => lists:reverse([#{tactic => Tac, result => proved, suggestion => Sug, ms => Ms2} | Tried])};
                                _ -> attempt(Statement, Rest, Opts, T0, [#{tactic => Tac, result => suggestion_failed, suggestion => Sug, ms => Ms2} | Tried])
                            end
                    end;
                {_, St} -> attempt(Statement, Rest, Opts, T0, [#{tactic => Tac, result => case St of timeout -> timeout; _ -> failed end, ms => Ms} | Tried])
            end
    end.

%% R8: Mathlib's plausible (random testing) on the statement; a counterexample it finds goes into the verdict, which
%% stays invalid
counterexample(Statement, Opts, V) ->
    Src = <<Statement/binary, " := by\n  plausible">>,
    C = check(Src, (maps:without([tactics], Opts))#{timeout => maps:get(per_tactic_timeout, Opts, 20000)}),
    Texts = [M || #{message := M} <- maps:get(errors, C, [])],
    case [T || T <- Texts, binary:match(T, <<"Found a counter-example!">>) =/= nomatch] of
        [T | _] ->
            [_, After] = binary:split(T, <<"Found a counter-example!">>),
            Lines = [string:trim(L) || L <- binary:split(After, <<"\n">>, [global])],
            Kept = lists:takewhile(fun(L) -> binary:match(L, <<"issue:">>) =:= nomatch end, [L || L <- Lines, L =/= <<>>]),
            V#{counterexample => iolist_to_binary(lists:join(<<", ">>, Kept))};
        [] -> V
    end.

%% "Try this: exact Nat.even_mul_succ_self n" from a search tactic's info message
suggestion(V) ->
    Infos = maps:get(infos, V, []),
    case [string:trim(Rest) || I <- Infos, [_, Rest] <- [binary:split(I, <<"Try this:">>)]] of
        [S | _] -> untag(hd(binary:split(S, <<"\n">>)));
        [] -> none
    end.

%% Mathlib v4.36.0 tags a suggestion with how it was found: "[apply] exact Nat.even_mul_succ_self n"
untag(<<"[", _/binary>> = S) ->
    case binary:split(S, <<"] ">>) of
        [_, Rest] -> string:trim(Rest);
        _ -> S
    end;
untag(S) -> S.

%% a short note on the notation of the pinned versions, for a model's tool description (kept with the pins)
syntax_notes() -> lean_check_hints:notes().

to_bin(X) when is_binary(X) -> X;
to_bin(X) when is_atom(X) -> atom_to_binary(X);
to_bin(X) when is_list(X) -> unicode:characters_to_binary(X).
