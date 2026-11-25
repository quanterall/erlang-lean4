%% lean-check: Lean 4 proof checking for Erlang.
%%
%%   lean_check:check(Source) / check(Source, Opts) -> Verdict
%%
%% Source is Lean 4 code checked in a fresh child of the base environment (by default `import Mathlib`). The
%% verdict is a map:
%%   status     valid | invalid | timeout | unavailable
%%   reason     why it is not valid: forbidden construct, errors, sorry, missing theorem, axioms not approved,
%%              no theorem to check
%%   theorems   the theorems audited, each with its axioms
%%   errors     Lean's error messages: #{line, column, message}
%%   elapsed_ms
%% valid means: the source passed the screen, Lean reported no error and no sorry, and every theorem exists and uses
%% only the approved axioms (by default propext, Classical.choice, Quot.sound: Lean's standard ones).
%%
%% Opts: theorems => [Name] (default: every theorem and lemma in the source), timeout => Ms (default 120000),
%% axioms => [Name] (the approved axioms), native_decide => boolean() (default false: it would add Lean's compiler to
%% the trusted base).
-module(lean_check).
-export([check/1, check/2, status/0]).

-define(APPROVED, [<<"propext">>, <<"Classical.choice">>, <<"Quot.sound">>]).

check(Source) -> check(Source, #{}).

check(Source0, Opts) ->
    Source = unicode:characters_to_binary(Source0),
    T0 = erlang:monotonic_time(millisecond),
    Timeout = maps:get(timeout, Opts, 120000),
    case lean_check_screen:screen(Source, Opts) of
        {error, Why} -> verdict(invalid, Why, [], [], T0);
        ok ->
            Names = [to_bin(N) || N <- maps:get(theorems, Opts, lean_check_screen:theorems(Source))],
            case Names of
                [] -> verdict(invalid, no_theorem, [], [], T0);
                _ -> run(Source, Names, Timeout, Opts, T0)
            end
    end.

run(Source, Names, Timeout, Opts, T0) ->
    case lean_check_pool:checkout(Timeout) of
        {error, no_worker} -> verdict(unavailable, no_worker, [], [], T0);
        {ok, W} ->
            Left = max(1000, Timeout - (erlang:monotonic_time(millisecond) - T0)),
            R = lean_check_worker:run(W, Source, Names, Left),
            lean_check_pool:checkin(W),
            judge(R, Names, Opts, T0)
    end.

judge({error, timeout}, _, _, T0) -> verdict(timeout, timeout, [], [], T0);
judge({error, {crashed, Why}}, _, _, T0) -> verdict(unavailable, {worker_crashed, Why}, [], [], T0);
judge({ok, #{messages := Msgs, sorries := Sorries, axioms := Axioms}}, Names, Opts, T0) ->
    Approved = [to_bin(A) || A <- maps:get(axioms, Opts, ?APPROVED)],
    Errors = [#{line => maps:get(<<"line">>, maps:get(<<"pos">>, M, #{}), 0),
                column => maps:get(<<"column">>, maps:get(<<"pos">>, M, #{}), 0),
                message => maps:get(<<"data">>, M, <<>>)}
              || #{<<"severity">> := <<"error">>} = M <- Msgs],
    Theorems = [#{name => N, axioms => maps:get(N, Axioms, missing)} || N <- Names],
    Reason = if
                 Errors =/= [] -> errors;
                 Sorries > 0 -> sorry;
                 true ->
                     case [N || #{name := N, axioms := missing} <- Theorems] of
                         [M | _] -> {missing_theorem, M};
                         [] ->
                             case [{N, A} || #{name := N, axioms := As} <- Theorems, A <- As,
                                             not lists:member(A, Approved)] of
                                 [] -> none;
                                 Bad -> {axioms_not_approved, Bad}
                             end
                     end
             end,
    case Reason of
        none -> verdict(valid, none, Theorems, [], T0);
        _ -> verdict(invalid, Reason, Theorems, Errors, T0)
    end.

verdict(Status, Reason, Theorems, Errors, T0) ->
    #{status => Status, reason => Reason, theorems => Theorems, errors => Errors,
      elapsed_ms => erlang:monotonic_time(millisecond) - T0}.

%% the pool: workers, free, busy, waiting callers
status() -> lean_check_pool:status().

to_bin(X) when is_binary(X) -> X;
to_bin(X) when is_atom(X) -> atom_to_binary(X);
to_bin(X) when is_list(X) -> unicode:characters_to_binary(X).
