import Mathlib

/-!
# Reflective certificates for polynomial identities

`PqcfCert.cert a b h ρ` proves `eval ρ a = eval ρ b` from `h : norm a = norm b`, where `norm` expands a polynomial
expression into a canonical list of terms (integer coefficient, exponent vector). The soundness theorem is proved
here once; a certificate for a particular identity then only needs `norm a = norm b`, which Lean's kernel decides by
evaluation (`decide +kernel`). This scales to polynomials with thousands of terms, where the `ring` tactic, which
builds a proof term step by step, does not.

Every function here is structurally recursive, so the kernel can evaluate it directly.
-/

namespace PqcfCert

/-- Polynomial expressions: integer constants, variables `v i`, sums, products, powers. -/
inductive E where
  | c : Int → E
  | v : Nat → E
  | add : E → E → E
  | mul : E → E → E
  | pow : E → Nat → E
  deriving Repr

section
variable {R : Type*} [CommRing R]

/-- The value of an expression in a commutative ring, variable `i` taking the value `ρ i`. -/
def eval (ρ : ℕ → R) : E → R
  | .c n => (n : R)
  | .v i => ρ i
  | .add a b => eval ρ a + eval ρ b
  | .mul a b => eval ρ a * eval ρ b
  | .pow a k => eval ρ a ^ k

/-- Exponent vectors: entry `k` is the exponent of variable `k`; missing entries are 0. -/
def addExp : List ℕ → List ℕ → List ℕ
  | [], b => b
  | x :: a, [] => x :: a
  | x :: a, y :: b => (x + y) :: addExp a b

/-- The value of the monomial with exponent vector `es`, its first entry for variable `k`. -/
def evalMono (ρ : ℕ → R) : ℕ → List ℕ → R
  | _, [] => 1
  | k, e :: es => ρ k ^ e * evalMono ρ (k + 1) es

theorem evalMono_addExp (ρ : ℕ → R) : ∀ (k : ℕ) (a b : List ℕ),
    evalMono ρ k (addExp a b) = evalMono ρ k a * evalMono ρ k b
  | k, [], b => by simp [addExp, evalMono]
  | k, x :: a, [] => by simp [addExp, evalMono]
  | k, x :: a, y :: b => by
      simp only [addExp, evalMono, evalMono_addExp ρ (k + 1) a b, pow_add]
      ring

/-- A term: an integer coefficient and an exponent vector. -/
abbrev Term := Int × List ℕ

def evalT (ρ : ℕ → R) (t : Term) : R := (t.1 : R) * evalMono ρ 0 t.2

/-- The value of a list of terms: their sum. -/
def evalL (ρ : ℕ → R) (l : List Term) : R := (l.map (evalT ρ)).sum

def mulT (s t : Term) : Term := (s.1 * t.1, addExp s.2 t.2)

def mulL : List Term → List Term → List Term
  | [], _ => []
  | s :: p, q => q.map (mulT s) ++ mulL p q

def powL (p : List Term) : ℕ → List Term
  | 0 => [(1, [])]
  | k + 1 => mulL (powL p k) p

def varExp : ℕ → List ℕ
  | 0 => [1]
  | i + 1 => 0 :: varExp i

/-- Expansion into a list of terms (not yet canonical). -/
def expand : E → List Term
  | .c n => [(n, [])]
  | .v i => [(1, varExp i)]
  | .add a b => expand a ++ expand b
  | .mul a b => mulL (expand a) (expand b)
  | .pow a k => powL (expand a) k

theorem evalMono_varExp (ρ : ℕ → R) : ∀ (i k : ℕ), evalMono ρ k (varExp i) = ρ (k + i)
  | 0, k => by simp [varExp, evalMono]
  | i + 1, k => by
      simp only [varExp, evalMono, pow_zero, one_mul, evalMono_varExp ρ i (k + 1)]
      congr 1
      omega

theorem evalL_append (ρ : ℕ → R) (a b : List Term) : evalL ρ (a ++ b) = evalL ρ a + evalL ρ b := by
  simp [evalL]

theorem evalT_mulT (ρ : ℕ → R) (s t : Term) : evalT ρ (mulT s t) = evalT ρ s * evalT ρ t := by
  simp only [evalT, mulT, evalMono_addExp]
  push_cast
  ring

theorem evalL_map_mulT (ρ : ℕ → R) (s : Term) : ∀ q : List Term,
    evalL ρ (q.map (mulT s)) = evalT ρ s * evalL ρ q
  | [] => by simp [evalL]
  | t :: q => by
      have ih := evalL_map_mulT ρ s q
      simp only [evalL, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, evalT_mulT]
      ring

theorem evalL_mulL (ρ : ℕ → R) : ∀ p q : List Term, evalL ρ (mulL p q) = evalL ρ p * evalL ρ q
  | [], q => by simp [mulL, evalL]
  | s :: p, q => by
      rw [mulL, evalL_append, evalL_map_mulT, evalL_mulL ρ p q]
      simp only [evalL, List.map_cons, List.sum_cons]
      ring

theorem evalL_powL (ρ : ℕ → R) (p : List Term) : ∀ k : ℕ, evalL ρ (powL p k) = evalL ρ p ^ k
  | 0 => by simp [powL, evalL, evalT, evalMono]
  | k + 1 => by rw [powL, evalL_mulL, evalL_powL ρ p k, pow_succ]

theorem evalL_expand (ρ : ℕ → R) : ∀ e : E, evalL ρ (expand e) = eval ρ e
  | .c n => by simp [expand, evalL, evalT, evalMono, eval]
  | .v i => by simp [expand, evalL, evalT, evalMono_varExp, eval]
  | .add a b => by rw [expand, evalL_append, evalL_expand ρ a, evalL_expand ρ b, eval]
  | .mul a b => by rw [expand, evalL_mulL, evalL_expand ρ a, evalL_expand ρ b, eval]
  | .pow a k => by rw [expand, evalL_powL, evalL_expand ρ a, eval]

/-- Lexicographic order on exponent vectors (as a Bool, for the kernel). -/
def leExp : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: a, y :: b => if x < y then true else if x = y then leExp a b else false

def ins (t : Term) : List Term → List Term
  | [] => [t]
  | s :: l => if leExp t.2 s.2 then t :: s :: l else s :: ins t l

def isort : List Term → List Term
  | [] => []
  | t :: l => ins t (isort l)

theorem ins_perm (t : Term) : ∀ l : List Term, (ins t l).Perm (t :: l)
  | [] => by simp [ins]
  | s :: l => by
      unfold ins
      split
      · exact List.Perm.refl _
      · exact ((ins_perm t l).cons s).trans (List.Perm.swap t s l)

theorem isort_perm : ∀ l : List Term, (isort l).Perm l
  | [] => by simp [isort]
  | t :: l => by
      rw [isort]
      exact (ins_perm t (isort l)).trans ((isort_perm l).cons t)

theorem evalL_perm (ρ : ℕ → R) {a b : List Term} (h : a.Perm b) : evalL ρ a = evalL ρ b := by
  simp only [evalL]
  exact (h.map _).sum_eq

/-- Adjacent terms with equal exponent vectors merged (the list is sorted, so equal ones are adjacent). -/
def mergeAux : Term → List Term → List Term
  | acc, [] => [acc]
  | acc, t :: l => if acc.2 = t.2 then mergeAux (acc.1 + t.1, acc.2) l else acc :: mergeAux t l

def merge : List Term → List Term
  | [] => []
  | t :: l => mergeAux t l

theorem evalL_mergeAux (ρ : ℕ → R) : ∀ (l : List Term) (acc : Term),
    evalL ρ (mergeAux acc l) = evalT ρ acc + evalL ρ l
  | [], acc => by simp [mergeAux, evalL]
  | t :: l, acc => by
      unfold mergeAux
      split
      · next h =>
          rw [evalL_mergeAux ρ l]
          simp only [evalL, evalT, List.map_cons, List.sum_cons, h]
          push_cast
          ring
      · rw [evalL, List.map_cons, List.sum_cons, ← evalL, evalL_mergeAux ρ l t]
        simp only [evalL, List.map_cons, List.sum_cons]

theorem evalL_merge (ρ : ℕ → R) : ∀ l : List Term, evalL ρ (merge l) = evalL ρ l
  | [] => rfl
  | t :: l => by rw [merge, evalL_mergeAux]; simp [evalL]

/-- Terms with coefficient 0 dropped. -/
def dropZero : List Term → List Term
  | [] => []
  | t :: l => if t.1 = 0 then dropZero l else t :: dropZero l

theorem evalL_dropZero (ρ : ℕ → R) : ∀ l : List Term, evalL ρ (dropZero l) = evalL ρ l
  | [] => rfl
  | t :: l => by
      unfold dropZero
      split
      · next h => rw [evalL_dropZero ρ l]; simp [evalL, evalT, h]
      · rw [evalL, List.map_cons, List.sum_cons, ← evalL, evalL_dropZero ρ l]
        simp [evalL]

/-- The canonical form: expanded, sorted, equal monomials merged, zeros dropped. -/
def norm (e : E) : List Term := dropZero (merge (isort (expand e)))

theorem evalL_norm (ρ : ℕ → R) (e : E) : evalL ρ (norm e) = eval ρ e := by
  rw [norm, evalL_dropZero, evalL_merge, evalL_perm ρ (isort_perm _), evalL_expand]

/-- The certificate: equal canonical forms give equal values, in every commutative ring, for every assignment. -/
theorem cert (a b : E) (h : norm a = norm b) (ρ : ℕ → R) : eval ρ a = eval ρ b := by
  rw [← evalL_norm ρ a, ← evalL_norm ρ b, h]

end

end PqcfCert

-- a small check: (x0 + x1)^2 = x0^2 + 2 x0 x1 + x1^2
example (ρ : ℕ → ℚ) :
    PqcfCert.eval ρ (.pow (.add (.v 0) (.v 1)) 2) =
      PqcfCert.eval ρ (.add (.add (.pow (.v 0) 2) (.mul (.c 2) (.mul (.v 0) (.v 1)))) (.pow (.v 1) 2)) :=
  PqcfCert.cert _ _ (by decide +kernel) ρ
