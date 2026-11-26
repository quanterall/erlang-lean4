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
             {inorder, [{timeout, 300, fun valid/0}, {timeout, 300, fun invalid/0},
                        {timeout, 300, fun r1_goals/0}, {timeout, 900, fun r2_prove/0}, {timeout, 300, fun r3_hints/0},
                        {timeout, 300, fun r4_statement/0}, {timeout, 300, fun r5_isolate/0},
                        {timeout, 300, fun r7_per_theorem/0}, {timeout, 600, fun r6_http/0}, {timeout, 60, fun r9_status/0},
                        {timeout, 300, fun timeout_and_restart/0}]}}
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
        <<"theorem lc_em' (p : Prop) : p ∨ ¬p := Classical.em p"/utf8>>,
        % a reflective certificate (PqcfCert, in the base environment): (x0 + x1)^2 = x0^2 + 2 x0 x1 + x1^2
        <<"theorem lc_cert : ∀ ρ : ℕ → ℚ, PqcfCert.eval ρ (.pow (.add (.v 0) (.v 1)) 2) = PqcfCert.eval ρ (.add (.add (.pow (.v 0) 2) (.mul (.c 2) (.mul (.v 0) (.v 1)))) (.pow (.v 1) 2)) := fun ρ => PqcfCert.cert _ _ (by decide +kernel) ρ"/utf8>>]],
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
        {<<"def x : ℕ := 1"/utf8>>, no_theorem},
        % a false identity: the canonical forms differ, decide fails
        {<<"theorem lc_cert_wrong : ∀ ρ : ℕ → ℚ, PqcfCert.eval ρ (.pow (.add (.v 0) (.v 1)) 2) = PqcfCert.eval ρ (.add (.add (.pow (.v 0) 2) (.mul (.c 3) (.mul (.v 0) (.v 1)))) (.pow (.v 1) 2)) := fun ρ => PqcfCert.cert _ _ (by decide +kernel) ρ"/utf8>>, errors}],
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

%%% The eagent team's requests (REQUESTS-erlang-lean4.md, 26 Nov 2026), each with its "done when"

has(Bin, Part) -> binary:match(Bin, Part) =/= nomatch.

%% R1: a failing linarith and a sorry return their goals
r1_goals() ->
    V = c(<<"theorem lc_r1 (x : ℝ) (h : 2 ≤ x) : 2 * x ≤ x ^ 2 := by\n  linarith"/utf8>>),
    [#{error := E, goals := [G]} | _] = maps:get(goals, V),
    ?assert(has(E, <<"linarith failed">>)),
    ?assert(has(G, <<"⊢ 2 * x ≤ x ^ 2"/utf8>>)),
    V2 = c(<<"theorem lc_r1b (n : ℕ) : Even (n * (n + 1)) := by\n  induction n with\n  | zero => simp\n  | succ k ih => sorry"/utf8>>),
    ?assertEqual(sorry, maps:get(reason, V2)),
    [#{error := <<"sorry">>, goals := [G2]}] = maps:get(goals, V2),
    ?assert(has(G2, <<"⊢ Even ((k + 1) * (k + 1 + 1))"/utf8>>)).

%% R2: proofs from the statement alone; a false statement ends invalid with what was tried, and a counterexample
r2_prove() ->
    P = fun(St, O) -> lean_check:prove(St, O#{timeout => 300000}) end,
    V1 = P(<<"theorem lc_r2a (n : ℕ) : Even (n * (n + 1))"/utf8>>, #{}),
    ?assertEqual(valid, maps:get(status, V1)),
    ?assert(has(maps:get(proof, V1), <<"by exact">>)),
    V3 = P(<<"theorem lc_r2c (q₁ q₂ : ℝ) : q₁ ≤ q₂ → 3 * q₁ + 50 ≤ 3 * q₂ + 50"/utf8>>, #{}),
    ?assertEqual(valid, maps:get(status, V3)),
    % x^2 - 6x + 10 > 0 needs the square (x - 3)^2: with it as a lemma
    V2 = P(<<"theorem lc_r2b (x : ℝ) : x ^ 2 - 6 * x + 10 > 0"/utf8>>, #{lemmas => [<<"sq_nonneg (x - 3)">>],
                                                                       tactics => [<<"positivity">>]}),
    ?assertEqual(valid, maps:get(status, V2)),
    V4 = P(<<"theorem lc_r2d (n : ℕ) : n * n ≠ 4"/utf8>>, #{tactics => [<<"norm_num">>, <<"omega">>, <<"simp">>], counterexample => true}),
    ?assertEqual({invalid, no_proof_found}, {maps:get(status, V4), maps:get(reason, V4)}),
    ?assertEqual(3, length(maps:get(tried, V4))),
    ?assertEqual(<<"n := 2">>, maps:get(counterexample, V4)),
    % only allowed tactics, no proof in the statement
    ?assertMatch(#{reason := {tactic_not_allowed, _}}, P(<<"theorem lc_x : True"/utf8>>, #{tactics => [<<"exact (sorry)">>]})),
    ?assertMatch(#{reason := statement_has_proof}, P(<<"theorem lc_x : True := trivial"/utf8>>, #{})).

%% R3: the old sum notation gets a hint; the syntax notes cover the starting list
r3_hints() ->
    V = c(<<"theorem lc_r3 (n : ℕ) : ∑ i in Finset.range (n + 1), i = n * (n + 1) / 2 := by\n  sorry"/utf8>>),
    ?assert(lists:any(fun(#{use := U}) -> has(U, <<"∈"/utf8>>) end, maps:get(hints, V))),
    N = lean_check:syntax_notes(),
    ?assert(byte_size(N) < 1500),
    [?assert(has(N, X)) || X <- [<<"∑ i ∈"/utf8>>, <<"fun x =>">>, <<"by">>, <<"Nat.">>, <<"intro">>, <<"obtain">>, <<"·"/utf8>>]].

%% R4: the statement as Lean elaborated it: natural-number subtraction visible with its types
r4_statement() ->
    V = c(<<"theorem lc_r4 (a b : ℕ) (h : b ≤ a) : a - b + b = a := by omega"/utf8>>),
    [#{statement := St}] = maps:get(theorems, V),
    ?assertEqual(<<"∀ (a b : ℕ), b ≤ a → a - b + b = a"/utf8>>, St),
    V2 = c(<<"theorem lc_r4b (n : ℕ) : (n : ℝ) + 1 > 0 := by positivity"/utf8>>),
    [#{statement := St2}] = maps:get(theorems, V2),
    ?assert(has(St2, <<"↑n"/utf8>>)).

%% R5: names cannot clash with Mathlib's
r5_isolate() ->
    V = c(<<"theorem sq (a b : ℚ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring"/utf8>>),
    ?assertEqual(valid, maps:get(status, V)),
    ?assertMatch([#{name := <<"sq">>}], maps:get(theorems, V)),
    V2 = lean_check:check(<<"theorem sq (a b : ℚ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring"/utf8>>, #{isolate => false}),
    ?assertEqual(invalid, maps:get(status, V2)).

%% R7: a verdict per theorem
r7_per_theorem() ->
    V = c(<<"theorem lc_r7a : 1 + 1 = 2 := rfl\ntheorem lc_r7b : 2 + 2 = 5 := by norm_num\ntheorem lc_r7c : 3 = 3 := rfl"/utf8>>),
    ?assertEqual(invalid, maps:get(status, V)),
    ?assertEqual([{<<"lc_r7a">>, valid}, {<<"lc_r7b">>, invalid}, {<<"lc_r7c">>, valid}],
                 [{N, St} || #{name := N, status := St} <- maps:get(theorems, V)]).

%% R6: the HTTP front, on the loopback, with a bearer token
r6_http() ->
    {ok, _} = application:ensure_all_started(inets),
    File = "/tmp/lean_check_token", ok = file:write_file(File, <<"secret-token\n">>),
    {ok, Pid} = lean_check_http:start(#{port => 28765, token_file => File, bind_address => {127, 0, 0, 1}, max_timeout => 200000}),
    Url = fun(P) -> "http://127.0.0.1:28765" ++ P end,
    Auth = [{"authorization", "Bearer secret-token"}],
    Post = fun(P, H, Body) -> {ok, {{_, Code, _}, _, Resp}} = httpc:request(post, {Url(P), H, "application/json", json:encode(Body)}, [{timeout, 300000}], [{body_format, binary}]), {Code, json:decode(Resp)} end,
    {401, _} = Post("/check", [], #{source => <<"theorem lc_h : 1 = 1 := rfl">>}),
    {401, _} = Post("/check", [{"authorization", "Bearer wrong"}], #{source => <<"theorem lc_h : 1 = 1 := rfl">>}),
    {200, #{<<"status">> := <<"valid">>}} = Post("/check", Auth, #{source => <<"theorem lc_h : 1 = 1 := rfl">>}),
    {200, #{<<"status">> := <<"valid">>, <<"proof">> := _}} = Post("/prove", Auth, #{statement => <<"theorem lc_hp (a b : ℕ) : a + b = b + a"/utf8>>, tactics => [<<"omega">>]}),
    {400, _} = Post("/check", Auth, #{source => <<"theorem lc_h : 1 = 1 := rfl">>, axioms => [<<"sorryAx">>]}),
    {400, _} = Post("/check", Auth, #{nothing => 1}),
    {ok, {{_, 200, _}, _, St}} = httpc:request(get, {Url("/status"), Auth}, [], [{body_format, binary}]),
    ?assertMatch(#{<<"checks">> := _}, json:decode(St)),
    inets:stop(httpd, Pid).

%% R9: what the service reports about itself
r9_status() ->
    S = lean_check:status(),
    [?assert(maps:is_key(K, S)) || K <- [checks, valid, invalid, timeout, mean_ms, p95_ms, worker_restarts, since_loaded_ms]],
    ?assert(maps:get(checks, S) > 0).
