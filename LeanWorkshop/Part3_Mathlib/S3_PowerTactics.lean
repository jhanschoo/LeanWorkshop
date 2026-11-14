/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Algebra.Ring.Real
import Aesop
import Mathlib.Basic.Real.Basic

/-!
# Part 3.3: Tactics in Mathlib

After you know the basics (`rw`, `apply`, `exact`, `intro`, `cases`), Mathlib's automation tactics
eliminate pages of routine algebra, inequality chasing, and logical bookkeeping.

---

## 1. The Simplifier (`simp`, `simp only`, `dsimp`, `@[simp]`)

- `simp` repeatedly rewrites the goal using all lemmas tagged `@[simp]` (from the bottom up).
- `simp [h1, h2]` adds extra local hypotheses or lemmas to the rewrite set.
- `simp at h` (or `simp at h ⊢` / `simp at *`) simplifies hypotheses as well.
- `dsimp` simplifies only by definitional equality (unfolding definitions and β-reducing).
- `@[simp]` registers a theorem or equation lemma for automatic use by `simp`.

**Mathlib rule of thumb:** A bare `simp` is fine when it **closes** the goal. If `simp` leaves
goals behind, run `simp?` and replace `simp` with `simp only [...]` so later `@[simp]` additions
cannot break downstream tactic steps.
-/

namespace LeanWorkshop.Part3

/-- A tiny wrapper function to illustrate `@[simp]` and `dsimp`. -/
def addZeroTag (n : ℕ) : ℕ :=
  n + 0

@[simp]
lemma addZeroTag_eq (n : ℕ) : addZeroTag n = n :=
  Nat.add_zero n

example (n : ℕ) : addZeroTag (n + 0) = n := by
  simp

example (xs : List ℕ) (h : xs = []) : xs.length + 0 = 0 := by
  simp [h]

/-!
---

## 2. Algebraic Normalizers (`ring`, `abel`, `group`)

- `ring` proves polynomial identities in any commutative semiring or ring (`ℕ`, `ℤ`, `ℚ`, `ℝ`).
- `abel` proves additive identities in any additive commutative monoid or group.
- `group` proves identities in any (possibly non-commutative) multiplicative group.

Note: `ring`, `abel`, and `group` ignore local hypotheses—first rewrite with `rw [h]` if a
hypothesis relates the variables (or use `grind` in Section 6, whose ring solver uses local
equations automatically)!
-/

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

example {A : Type*} [AddCommGroup A] (a b : A) : a + b - a = b := by
  abel

example {G : Type*} [Group G] (a b : G) : a * b * b⁻¹ * a⁻¹ = 1 := by
  group

/-!
---

## 3. Linear & Numerical Decision Procedures

(`linarith`, `omega`, `lia`, `norm_num`, `positivity`)

| Tactic | Domain | Best For |
| :--- | :--- | :--- |
| `linarith` | Linear arithmetic over `ℤ`, `ℚ`, `ℝ` | Combining linear inequalities & equations |
| `omega` | Presburger arithmetic over `ℕ`, `ℤ` | Discrete bounds, `%`, `/`, `ℕ` subtraction |
| `lia` | Complete LIA over `ℤ`, `ℕ` | Model-based solver (`=`, `≤`, `≠`, `∣`); wraps `grind` |
| `norm_num` | Concrete numerical expressions | Evaluating `2 ^ 10 = 1024`, fractions, `<` |
| `positivity` | Sign (`0 < _`, `0 ≤ _`, `_ ≠ 0`) | Combining squares, sums, products, `|x|` |

-/

example {x y : ℝ} (h1 : x + 2 * y ≤ 5) (h2 : 3 * x - y ≤ 1) : 7 * x ≤ 7 := by
  linarith

example {a b : ℕ} (h : a < b + 1) : a ≤ b := by
  omega

example {x y : ℤ} : 2 * x + 3 * y = 0 → 1 ≤ x → y < 1 := by
  lia

example : (3 : ℝ) / 4 + 5 / 4 = 2 := by
  norm_num

example (a b : ℝ) : 0 < a ^ 2 + b ^ 2 + 1 := by
  positivity

/-!
---

## 4. Extensionality, Monotonicity & Function Properties

(`ext` / `funext`, `gcongr`, `fun_prop`)

- `funext x` / `ext`: reduces equality of functions or structures to pointwise/fieldwise equality.
- `gcongr`: "generalized congruence"—peels matching outer operations off `<`, `≤`, or `=` goals
  (e.g. `a + c ≤ b + d` becomes `a ≤ b` and `c ≤ d`).
- `fun_prop`: Mathlib's function-property tactic (`Mathlib.Tactic.FunProp`) for goals like
  `Continuous f`, `Differentiable ℝ f`, `ContDiff`, or `Measurable`. It decomposes composite
  lambdas into elementary functions tagged `@[fun_prop]` and supports `fun_prop (disch := ...)`
  for side conditions such as `x ≠ 0`.
-/

example : (fun x : ℝ ↦ x + 1) = (fun x : ℝ ↦ 1 + x) := by
  funext x
  ring

example {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) : a + 2 * c ≤ b + 2 * d := by
  gcongr

example : Continuous (fun x : ℝ ↦ x ^ 2 + 3 * x + 1) := by
  fun_prop

/-!
---

## 5. Negation & Contraposition (`push Not`, `contrapose!`)

- `push Not`: drives `¬` inward across `∀`, `∃`, `∧`, `∨`, `≤`, and `<` (replaces older `push_neg`).
- `contrapose!` `h`: contraposes a hypothesis `h` with the goal and runs `push Not` on both.
-/

example {P : ℕ → Prop} (h : ¬ ∀ n, P n) : ∃ n, ¬ P n := by
  push Not at h
  exact h

example {x y : ℝ} (h : x ≤ y → x ≤ 5) (hy : 5 < x) : y < x := by
  contrapose! hy
  exact h hy

/-!
---

## 6. Proof Search & SMT-Style Automation (`aesop`, `grind`)

- `aesop`: white-box best-first proof search combining `intro`, `cases`, `simp`, `apply`, and
  `@[aesop]` rules.
- `grind`: Lean 4's modern SMT-inspired tactic ("virtual whiteboard"). Every discovered equality,
  inequality, or logical fact is shared across cooperating engines:
  - **Congruence closure**: tracks equalities across function applications (`a = b` gives
    `f a = f b`).
  - **E-matching**: instantiates `@[grind]` theorems or extra lemmas passed via `grind [h]`
    modulo known equalities.
  - **Case splitting**: splits on `if`/`match`/disjunctions when needed.
  - **Satellite theory solvers**: runs `lia` (linear integer arithmetic), `ring` (Gröbner bases for
    commutative rings *including* local hypotheses), and `linarith` (linear ordered modules).
-/

example (P Q R : Prop) : (P ∧ Q → R) → P → Q → R := by
  aesop

-- `grind` combines congruence closure across function applications:
example (f : ℕ → ℕ) (a b c : ℕ) (h1 : a = b) (h2 : f b = c) : f a + 1 = c + 1 := by
  grind

-- Unlike standalone `ring`, `grind`'s ring solver uses local hypotheses directly:
example (x y : ℝ) (h1 : x + y = 5) (h2 : x - y = 1) : x ^ 2 - y ^ 2 = 5 := by
  grind

/-!
---

## 7. Exercises

Use the power tactics from this module to solve each goal concisely.
(Reference solutions are in `LeanWorkshop/Solutions/Part3_Mathlib/S3_PowerTactics.lean`.)
-/

/-- **Exercise 1:** Expand `(x + y) ^ 3` over `ℝ`. -/
theorem ex1_ring_identity (x y : ℝ) :
    (x + y) ^ 3 = x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3 := by
  sorry

/-- **Exercise 2:** Deduce an upper bound on `x` from linear constraints. -/
theorem ex2_linarith_bound {x y : ℝ} (h1 : 2 * x + y ≤ 10) (h2 : x - y ≤ 2) : x ≤ 4 := by
  sorry

/-- **Exercise 3:** Prove nonnegativity of `x ^ 2 + y ^ 2 + 1`. -/
theorem ex3_positivity_bound (x y : ℝ) : 0 ≤ x ^ 2 + y ^ 2 + 1 := by
  sorry

/-- **Exercise 4:** Use monotonicity (`gcongr`) when `hc : 0 ≤ c`. -/
theorem ex4_gcongr_ineq {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) : a * c + 5 ≤ b * c + 5 := by
  sorry

/-- **Exercise 5:** Prove the contrapositive using `contrapose!` (or `linarith`). -/
theorem ex5_contrapose {n : ℤ} (h : 3 * n + 1 ≤ 10 → n ≤ 2) (hn : 2 < n) : 10 < 3 * n + 1 := by
  sorry

/-- **Exercise 6:** Solve modular arithmetic on `ℕ` using `omega` or `lia`. -/
theorem ex6_omega_parity {n : ℕ} (h : n % 2 = 1) : (n + 3) % 2 = 0 := by
  sorry

/-- **Exercise 7:** Prove continuity of a polynomial function on `ℝ` using `fun_prop`. -/
theorem ex7_fun_prop_continuous : Continuous (fun x : ℝ ↦ (x - 1) ^ 2 + 5 * x) := by
  sorry

/-- **Exercise 8:** Combine congruence closure and algebraic hypotheses using `grind`. -/
theorem ex8_grind_congr (f : ℝ → ℝ) (x y : ℝ) (hxy : x + y = 4) (hf : f 16 = 0) :
    f ((x + y) ^ 2) = 0 := by
  sorry

end LeanWorkshop.Part3
