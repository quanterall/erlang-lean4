%% lean-check against Lean 4 and Mathlib (inside the lean-check image; skipped where /repl is absent). The negative
%% fixtures are the verification gate's self-test (names prefixed lc_ so none clashes with Mathlib's) (erlang-lean4 FS v0.08, VG-7): each must be rejected.
-module(lean_check_tests).
-include_lib("eunit/include/eunit.hrl").

available() -> filelib:is_regular("/repl/.lake/build/bin/repl").

lean_test_() ->
    case available() of
        false -> [];
        true ->
            {setup,
             fun() -> application:set_env(lean_check, workers, 1),
                      application:set_env(lean_check, max_checks, 1000),
                      {ok, _} = application:ensure_all_started(lean_check),
                      wait_ready(900)
             end,
             fun(_) -> application:stop(lean_check) end,
             {inorder, [{timeout, 300, fun valid/0}, {timeout, 300, fun invalid/0}, {timeout, 300, fun timeout_and_restart/0}]}}
    end.

wait_ready(0) -> error(no_worker_ready);
wait_ready(N) ->
    case lean_check:status() of
        #{free := F} when F > 0 -> ok;
        _ -> timer:sleep(1000), wait_ready(N - 1)
    end.

c(Src) -> lean_check:check(Src, #{timeout => 120000}).

valid() ->
    [begin
         V = c(Src),
         ?assertMatch({valid, Src}, {maps:get(status, V), Src})
     end || Src <- [
        <<"theorem lc_two_plus_two : 2 + 2 = 4 := rfl"/utf8>>,
        <<"theorem lc_sq (a b : ℚ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring"/utf8>>,
        <<"theorem lc_frac : (1 : ℚ) / 3 + 1 / 6 = 1 / 2 := by norm_num"/utf8>>,
        <<"namespace Pq\ntheorem lc_inner (n : ℕ) : n + 0 = n := by simp\nend Pq"/utf8>>,
        % classical logic is allowed: Classical.choice is approved
        <<"theorem lc_em' (p : Prop) : p ∨ ¬p := Classical.em p"/utf8>>]],
    V = c(<<"theorem lc_sq (a b : ℚ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring"/utf8>>),
    [#{name := <<"lc_sq"/utf8>>, axioms := Ax}] = maps:get(theorems, V),
    ?assert(lists:all(fun(A) -> lists:member(A, [<<"propext"/utf8>>, <<"Classical.choice"/utf8>>, <<"Quot.sound"/utf8>>]) end, Ax)).

invalid() ->
    Cases = [
        % VG-7 negative fixtures
        {<<"theorem lc_broken : 1 = := rfl"/utf8>>, errors},
        {<<"theorem lc_gap (a : ℕ) : a * 0 = 0 := by sorry"/utf8>>, sorry},
        {<<"axiom bad : False\ntheorem lc_uses_bad : 1 = 2 := bad.elim"/utf8>>, axioms_not_approved},
        {<<"@[implemented_by id] def f (n : ℕ) : ℕ := n\ntheorem lc_t : f 1 = 1 := rfl"/utf8>>, forbidden},
        {<<"#eval (1 : ℕ)\ntheorem lc_t : True := trivial"/utf8>>, forbidden},
        {<<"import Mathlib.Tactic\ntheorem lc_t : True := trivial"/utf8>>, forbidden},
        {<<"theorem lc_t : 2 ^ 10 = 1024 := by native_decide"/utf8>>, forbidden},
        % a false statement, a missing theorem, nothing to check
        {<<"theorem lc_wrong : (2 : ℕ) + 2 = 5 := by norm_num"/utf8>>, errors},
        {<<"def x : ℕ := 1"/utf8>>, no_theorem}],
    [begin
         V = c(Src),
         ?assertEqual({Src, invalid}, {Src, maps:get(status, V)}),
         ?assertEqual({Src, Want}, {Src, kind(maps:get(reason, V))})
     end || {Src, Want} <- Cases],
    % a theorem lc_asked for that the source does not define
    V = lean_check:check(<<"theorem lc_here : True := trivial"/utf8>>, #{theorems => [<<"lc_elsewhere"/utf8>>]}),
    ?assertEqual({missing_theorem, <<"lc_elsewhere"/utf8>>}, maps:get(reason, V)),
    % native_decide when allowed: then Lean's compiler is in the trusted base, and its axiom shows it
    V2 = lean_check:check(<<"theorem lc_p : 2 ^ 10 = 1024 := by native_decide"/utf8>>, #{native_decide => true}),
    ?assertEqual(invalid, maps:get(status, V2)),
    ?assertMatch({axioms_not_approved, _}, maps:get(reason, V2)).

kind({forbidden, _}) -> forbidden;
kind({axioms_not_approved, _}) -> axioms_not_approved;
kind({missing_theorem, _}) -> missing_theorem;
kind(R) -> R.

%% a check that cannot finish in time: timeout, the worker restarted, the next check served
timeout_and_restart() ->
    % a proof that never ends: repeat a step that always succeeds, with no heartbeat limit
    Slow = <<"set_option maxHeartbeats 0 in\ntheorem lc_slow : True := by\n  repeat (have : 1 = 1 := rfl)\n  trivial"/utf8>>,
    V = lean_check:check(Slow, #{timeout => 3000}),
    ?assertEqual(timeout, maps:get(status, V)),
    wait_ready(900),
    ?assertEqual(valid, maps:get(status, c(<<"theorem lc_after : 1 + 1 = 2 := rfl"/utf8>>))).
