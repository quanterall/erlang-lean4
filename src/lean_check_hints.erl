%% Help with current syntax (R3): what to write instead of notation that is outdated at the pinned versions (Lean
%% v4.36.0, Mathlib v4.36.0), found in a source, and a short note on the current notation. Kept with the version
%% pins: when they change, this list and the note change with them.
-module(lean_check_hints).
-export([hints/2, notes/0]).

%% {Regex, Found, Use, Why}: Found is what the hint names, Use what to write instead
patterns() ->
    [{"[∑∏][^,\\n]*?\\sin\\s", "∑ x in s, ∏ x in s", "∑ x ∈ s, ∏ x ∈ s",
      "Mathlib now writes big operators with ∈"},
     {"(λ|\\bfun)\\s+[^,=\\n]*,", "λ x, / fun x,", "fun x =>", "Lean 4 lambdas use =>"},
     {"\\bbegin\\b", "begin ... end", "by (and indented tactics)", "Lean 3 tactic blocks"},
     {"\\b(nat|real|int|rat|finset|list|set|complex|polynomial)\\.[a-z_]", "nat., real., ..",
      "Nat., Real., Int., Rat., Finset., List., Set., Complex., Polynomial.",
      "Lean 3 lower-case namespaces; Lean 4 capitalises them"},
     {"\\bassume\\b", "assume", "intro", "Lean 3 tactic"},
     {"\\bcases\\s+\\S+\\s+with\\b", "cases h with a b", "obtain ⟨a, b⟩ := h (or rcases h with ⟨a, b⟩)",
      "Lean 3 syntax for cases"},
     {"\\{\\s*(norm_num|simp|linarith|ring|exact|apply|nlinarith|positivity)", "{ tac }",
      "· tac (a focusing dot)", "Lean 3 focusing braces"},
     {"\\bat\\s+\\*\\s*⊢", "at * ⊢", "at *", "in Lean 4 * already includes the goal"}].

%% the hints for a source: one per pattern found, with the line of its first occurrence
hints(Source, _Errors) ->
    lists:append([case re:run(Source, Re, [unicode, ucp]) of
                      {match, [{Off, _} | _]} ->
                          Line = 1 + length(binary:matches(binary:part(Source, 0, Off), <<"\n">>)),
                          [#{line => Line, found => b(F), use => b(U), why => b(W)}];
                      nomatch -> []
                  end || {Re, F, U, W} <- patterns()]).

b(S) -> unicode:characters_to_binary(S).

notes() ->
    unicode:characters_to_binary(
      "Lean 4 (v4.36.0) and Mathlib (v4.36.0) notation:\n"
      "- theorem name (x : ℝ) (h : 0 ≤ x) : statement := by tactics   (no begin/end; tactics indented under by)\n"
      "- fun x => e  (not λ x, e);  ∀ x, P x;  ∃ x, P x;  ¬ P;  P ∧ Q;  P ∨ Q;  P → Q;  P ↔ Q\n"
      "- big operators: ∑ i ∈ Finset.range (n + 1), f i   and   ∏ i ∈ s, f i   (∈, not in)\n"
      "- names are capitalised: Nat.succ, Real.sqrt, Finset.sum_range_succ, Int.emod  (not nat., real.)\n"
      "- intro x (not assume);  obtain ⟨a, b⟩ := h  or  rcases h with ⟨a, b⟩  (not cases h with a b)\n"
      "- focus a goal with ·  (not { tac });  cases n with | zero => .. | succ k => ..\n"
      "- induction n with | zero => tac | succ k ih => tac\n"
      "- useful closers: norm_num, simp, ring, field_simp, linarith, nlinarith, positivity, omega, decide, exact?\n"
      "- types: (2 : ℝ), (n : ℕ); ℕ subtraction truncates at 0; division on ℕ is integer division\n"
      "- Even n, Odd n;  n % 2 = 0;  Nat.Prime p;  |x| for abs;  x⁻¹;  Real.sqrt x;  x ^ 2\n").
