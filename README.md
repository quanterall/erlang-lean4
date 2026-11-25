# erlang-lean4

Lean 4 for Erlang/OTP systems. The first part, and the one implemented here, is **lean-check**: proof checking as an
OTP service, a supervised pool of Lean REPL workers with Mathlib behind one function. A later part is in-process
verified kernels (small proven Lean functions called from the BEAM at microsecond latency); it is not implemented
yet.

## lean-check

Lean 4 proof checking for Erlang/OTP: a supervised pool of Lean REPL workers with Mathlib, behind one function.

```erlang
1> lean_check:check(<<"theorem sq (a b : ℚ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring"/utf8>>).
#{status => valid, reason => none, errors => [], elapsed_ms => 412,
  theorems => [#{name => <<"sq">>, axioms => [<<"propext">>, <<"Classical.choice">>, <<"Quot.sound">>]}]}
```

## Goals

- **Certified results for PQCF.** [PQCF](https://github.com/quanterall/pqcf) is a fast, unverified symbolic and
  numeric engine. For an exact result it writes a Lean statement a reader can check by eye and a proof Lean checks
  by machine (`pq_lean`: factorisations, gcds, solutions of linear systems). PQCF stays the solver; Lean is the judge.
- **Proof checking as an OTP service.** A supervised pool of Lean workers with Mathlib, bounded time per check,
  structured verdicts; in-node or from another node over Erlang distribution.
- **A checker for reasoning loops** (later): a statement and a proof go in, a verdict with Lean's errors comes out.
- **Honest assurance.** A verdict states the axioms used and rests on a named trusted base; it says nothing about
  whether a statement says what its author meant.

The full guide, with the PQCF examples and their real output: [docs/guide.md](docs/guide.md).

## Example from PQCF

```erlang
%% PQCF factors x^4 - y^4 and asks lean-check to certify that the factors multiply back
{ok, E} = pq_symbolic:parse(<<"x^4 - y^4">>),
{ok, #{source := Lean, verdict := #{status := valid}}} = pq_lean:factor(E, #{checker => {node, 'lean_check@lc'}}).
```

```lean
theorem pqcf_factor (x y : ℚ) :
    (((x ^ 4) + ((-1) * (y ^ 4))) : ℚ) = (1 * ((1 * x) + ((-1) * y)) * ((1 * x) + (1 * y)) * ((1 * (x ^ 2)) + (1 * (y ^ 2)))) := by
  ring
```

## The verdict

`lean_check:check(Source, Opts)` checks Lean 4 source in a fresh child of the base environment (`import Mathlib`)
and returns a map:

| key | value |
| --- | --- |
| `status` | `valid`, `invalid`, `timeout` or `unavailable` |
| `reason` | `none`, or why not: `{forbidden, Construct}`, `errors`, `sorry`, `{missing_theorem, Name}`, `{axioms_not_approved, [{Theorem, Axiom}]}`, `no_theorem`, `timeout`, `no_worker`, `{worker_crashed, Why}` |
| `theorems` | each theorem checked, with the axioms it depends on (`#print axioms`) |
| `errors` | Lean's errors: `#{line, column, message}` |
| `elapsed_ms` | wall time |

`valid` means: the source passed the screen; Lean reported no error and no `sorry`; every theorem exists and depends
only on the approved axioms (by default Lean's standard `propext`, `Classical.choice`, `Quot.sound`).

Options: `theorems => [Name]` (default: every `theorem` and `lemma` in the source, with their namespaces),
`timeout => Ms` (default 120000), `axioms => [Name]` (the approved axioms), `native_decide => true` (default false:
it adds Lean's compiler to the trusted base, and the axiom it introduces then has to be approved too).

**What `valid` means and what it does not.** Lean checked that the proof proves the statement, from the approved
axioms, with Lean's kernel, Mathlib and this toolchain as the trusted base. It says nothing about whether the
statement says what its author meant: a wrong or weak statement can be proved correctly. Statements need to be read.

## Untrusted input

A submitted proof is untrusted: Lean can run code while it checks a file. Two lines of defence:

1. **The screen** (`lean_check_screen`): comments and string literals are removed, then the source is rejected if it
   contains a construct that runs or injects code (`#eval`, `#exit`, `#print`, `run_cmd`, `run_tac`, `run_elab`,
   `run_meta`, `elab`, `elab_rules`, `macro`, `macro_rules`, `syntax`, `declare_syntax_cat`, `initialize`,
   `builtin_initialize`, `unsafe`, `implemented_by`, `extern`, `opaque`), an `import` (a check sees only the base
   environment), `set_option` other than `maxHeartbeats` and `maxRecDepth`, or `native_decide` unless allowed.
   This is a deny-list: it narrows what a submission can do, it is not a sandbox.
2. **The container**: run lean-check with no network (`--network none`), a memory limit and a read-only root
   filesystem where possible. A worker that exceeds its time is killed (`kill -9` of the REPL) and restarted.

## Architecture

- `lean_check_worker`: one [Lean REPL](https://github.com/leanprover-community/repl) per worker, behind a port. It
  imports Mathlib once (seconds to minutes) and keeps that environment as the base; each check runs in a fresh child
  of it, so checks never see each other. It restarts after `max_checks` checks (the REPL keeps every environment).
- `lean_check_pool`: hands checks to free workers; callers queue when all are busy.
- `lean_check_sup`: restarts workers that die or time out.

Configuration (application environment): `workers` (default 1; each holds Mathlib in memory), `env_dir` (`/env`),
`repl` (`/repl/.lake/build/bin/repl`), `header` (`import Mathlib`), `start_timeout`, `max_checks`.

## Versions (pinned)

| component | version |
| --- | --- |
| Erlang/OTP | 27 (`erlang:27-slim`, Debian 12, by digest) |
| Lean | v4.36.0 |
| Mathlib | tag v4.36.0, commit fc4f59e577feb1a4956671bc04ac18aaaf8cd842 |
| Lean REPL | tag v4.36.0, commit 1b9fdf8ab81e52ba8651207c07e405129de2ffbe |

## Build and test

```sh
docker build -t lean-check docker          # Lean, the REPL and Mathlib's prebuilt cache: several GB, 10-30 minutes
sh tools/test.sh                           # the screen's tests and the Lean tests, inside the image
```

The Lean tests include the negative fixtures a proof-checking gate must reject (a parse error, `sorry`, a theorem
resting on a non-approved axiom, `implemented_by`, `#eval`, `import`, `native_decide`, a false statement, a missing
theorem) and a timeout with the worker's restart.

## Licence

Apache 2.0.
