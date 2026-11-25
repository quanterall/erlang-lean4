# lean-check guide (erlang-lean4)

## 1. Goals

lean-check turns Lean 4 into a service an Erlang system can call: it takes a Lean statement with its proof and
returns a verdict saying whether Lean's kernel accepts the proof, from which axioms, and if not, why not.

| goal | what it means |
| --- | --- |
| **G1. Certified results for PQCF** | PQCF (the Photonic Quantum Computing Framework, a symbolic and numeric engine) is fast and its solvers are not verified. For an exact result it writes a Lean statement a reader can check by eye and a proof Lean checks by machine: the factors multiply back to the polynomial, the solution satisfies the linear system. PQCF stays the solver; Lean becomes the judge. |
| **G2. Proof checking as an OTP service** | A supervised pool of Lean workers with Mathlib loaded, bounded time per check, killed and restarted on a timeout, structured results (status, reason, errors with positions, axioms). Callable in-node or from another node over Erlang distribution. |
| **G3. A checker for reasoning loops (later)** | A model proposes a formal statement and proof, lean-check checks it, the errors go back to the model. The same verdict serves both uses; the loop itself is future work (section 8). |
| **G4. Honest assurance** | A verdict says exactly what was proved and from what: the axioms used, the trusted base (Lean's kernel, Mathlib, this toolchain), and nothing about whether the statement says what its author meant. |

Non-goals for now: verifying the Erlang or Rust code of PQCF (only results are certified, one at a time); running
Lean inside the BEAM (in-process verified kernels are a separate, later track, the subject of the erlang-lean4
specification); proving that a result is complete or optimal where only its soundness is certified (for example
that a gcd is the *greatest* common divisor, or that factors are irreducible).

## 2. Concepts

- **Statement**: the Lean proposition, e.g. `∀ x y : ℚ, x^4 - y^4 = (x - y)(x + y)(x^2 + y^2)`. It is what is
  claimed, and the part a person must read.
- **Proof**: the Lean tactic script or term that proves it (`by ring`, `by norm_num`). Nobody needs to read it: Lean
  checks it.
- **Base environment**: what every check may use: Lean 4 and Mathlib (`import Mathlib`), loaded once per worker.
  Each check runs in a fresh child of it and cannot see other checks.
- **Verdict**: `valid` when Lean reported no error and no `sorry` and every theorem exists and depends only on the
  approved axioms (Lean's standard `propext`, `Classical.choice`, `Quot.sound`).
- **Trusted base**: what a `valid` verdict rests on without being checked here: Lean's kernel, Mathlib's
  definitions, the Lean toolchain and the REPL, the approved axioms.

## 3. Using it from Erlang

```erlang
{ok, _} = application:ensure_all_started(lean_check),
V = lean_check:check(<<"theorem t (a b : ℚ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring"/utf8>>),
valid = maps:get(status, V).
```

The verdict is a map (README, "The verdict"). Options: `theorems`, `timeout`, `axioms`, `native_decide`.

From another node (the usual deployment: lean-check in its own container, the caller elsewhere):

```erlang
V = erpc:call('lean_check@lc', lean_check, check, [Source, #{timeout => 120000}]).
```

## 4. Using it from PQCF

PQCF's module `pq_lean` writes the certificates and calls lean-check: in the same node when `lean_check` is loaded,
else on a lean-check node (`checker => {node, Node}`), else it only returns the source (`checker => none`). PQCF
has no build dependency on lean-check.

The examples below are real output of PQCF's `examples/lean/run.sh` (a PQCF node and a lean-check node on an
internal Docker network, 25 Nov 2026).

**A factorisation.** `pq_lean:factor(E, Opts)` factors E with `pq_symbolic:factor/1` and certifies that the factors
multiply back to E, as polynomials over ℚ:

```lean
theorem pqcf_factor (x y : ℚ) :
    (((x ^ 4) + ((-1) * (y ^ 4))) : ℚ) = (1 * ((1 * x) + ((-1) * y)) * ((1 * x) + (1 * y)) * ((1 * (x ^ 2)) + (1 * (y ^ 2)))) := by
  ring
```
```
-> valid (450 ms), axioms [{<<"pqcf_factor">>, [<<"propext">>, <<"Classical.choice">>, <<"Quot.sound">>]}]
```

**A gcd with its cofactors.** `pq_lean:gcd(A, B, Opts)` certifies that the gcd G divides both, with the cofactors
A' = A/G and B' = B/G (that G is the greatest is not certified yet: section 8):

```lean
theorem pqcf_gcd (x : ℚ) :
    (((x ^ 3) + ((-1) * x)) : ℚ) = ((1 + (1 * x)) * (((-1) * x) + (1 * (x ^ 2)))) ∧ (((x ^ 2) + (2 * x) + 1) : ℚ) = ((1 + (1 * x)) * (1 + (1 * x))) := by
  constructor <;> ring
```
```
-> valid (380 ms)
```

**An exact solution of a linear system.** `pq_lean:linear(Rows, X, Opts)`, Rows = `[{[a_i1, .., a_in], b_i}]`,
certifies that X satisfies every row, in exact rationals. For 3x + 2y = 1, x - 4y = 5/2 and x = 9/14, y = -13/28:

```lean
theorem pqcf_linear :
    (((3 * ((9 : ℚ) / 14)) + (2 * ((-13 : ℚ) / 28))) : ℚ) = 1 ∧ (((1 * ((9 : ℚ) / 14)) + ((-4) * ((-13 : ℚ) / 28))) : ℚ) = ((5 : ℚ) / 2) := by
  norm_num
```
```
-> valid (604 ms)
```

**A wrong result is rejected.** With one sign changed in the solution (y = 13/28), Lean reduces the statement to
`False` and the verdict says so:

```
-> invalid, errors
  unsolved goals
⊢ False
```

(While preparing this example the first solution written down was itself wrong, x = 3/7, y = -1/2; lean-check
rejected it the same way.)

## 5. Deployment

- Image: `docker build -t lean-check docker` (11.8 GB: Lean, the REPL, Mathlib's prebuilt cache). Pinned versions:
  README.
- A node: `erl -sname lean_check -setcookie <secret>` with the application started; callers on the same Erlang
  cluster use `erpc`. Run it on an internal network (`docker network create --internal`), as `examples/lean/run.sh`
  in PQCF does: no outside access for the workers.
- Memory: each worker holds Mathlib (several GB resident when used); size `workers` to the machine.
- Start-up: a worker is ready after importing Mathlib (seconds on a warm cache). `lean_check:status()` reports
  free and busy workers.

## 6. Security

A submission is untrusted code: Lean can execute code while checking (README, "Untrusted input"). The screen
rejects the constructs that run or inject code; the container (no network, memory limit) is the second line; a
timeout kills the REPL process. The screen is a deny-list and may be incomplete: do not run lean-check with access
to secrets or networks it does not need.

## 7. Limits

- Statements must be read. A proof proves its statement; a wrong or weak statement is still proved.
- Checking time grows with the size of the expressions: `ring` and `norm_num` on large polynomials or large linear
  systems can take seconds to minutes; set `timeout` accordingly.
- `native_decide` is off by default; allowing it adds Lean's compiler to the trusted base, and its axiom
  (`Lean.ofReduceBool`) is then reported and must be approved explicitly.
- Theorem names must not clash with Mathlib's (a check runs in Mathlib's namespace); PQCF uses a `pqcf_` prefix.

## 8. Roadmap

1. More PQCF certificates: the gcd's greatestness (a Bezout certificate: u A + v B = G), identities PQCF compares
   with other programs today (Wigner symbols, colour factors, beta-function coefficients), exact steady states.
2. Interval certificates for PQCF's high-precision numerics (an enclosure with its bound, checked in Lean).
3. The reasoning-loop API: a check that returns the remaining goals in a form a model can use, with budgets.
4. Operations: environment snapshots to start workers faster, metrics, a CI gate with the negative fixtures on
   every toolchain change.
