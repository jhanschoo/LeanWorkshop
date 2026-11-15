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
import Mathlib.Tactic.GCongr
import Mathlib.Basic.Real.Basic

/-!
# Part 4.2: Outlining and Incremental Formalization

Real mathematical formalization—whether manual or AI-assisted—is **not** one-shot tactic
generation, and non-trivial proofs rarely fit inside a single theorem with inline `have` steps.
Instead, use a multi-stage **Plan → Outline → Flesh Out & Revise** workflow:

1. **Plan definitions & structure:** Design the core `structure` or `def`, place helper predicates
   and API in a dedicated `namespace` (enabling dot notation), and group shared parameters with
   `section` + `variable`.
2. **Outline top-down with `sorry`-stubbed lemmas:** State intermediate `lemma`s with `:= by sorry`
   and write the proof of the target theorem *first* so Lean verifies the dependency graph and
   lemma signatures before you invest time proving helpers.
3. **Flesh out incrementally & revise:** Prove helper lemmas bottom-up. When friction appears
   (awkward division guards, missing `@[simp]` lemmas, or unresolved implicit binders), revise the
   intermediate statements and re-check the whole chain.

---

## 1. Stage 1: Planning the Structure, Namespace, and Definitions

**Mathematical Goal:** Given a contraction mapping $T : \mathbb{R} \to \mathbb{R}$ with contraction
factor $c \in [0, 1)$, prove the **a-posteriori residual error bound**
$$(1 - c)|x - x^*| \le |x - T(x)|$$
and deduce **uniqueness of fixed points**.

We package the contraction axioms into `structure ContractionMap`, then open
`namespace ContractionMap` so callers can write `T.IsFixedPt`, `T.slack`, and `T.fixedPt_unique`.
-/

namespace LeanWorkshop.Part4

/-- A contraction mapping on `ℝ` with Lipschitz factor `factor ∈ [0, 1)`. -/
structure ContractionMap where
  /-- The underlying map `ℝ → ℝ`. -/
  toFun : ℝ → ℝ
  /-- The contraction factor `c ∈ [0, 1)`. -/
  factor : ℝ
  /-- Nonnegativity of the contraction factor. -/
  factor_nonneg : 0 ≤ factor
  /-- Strict upper bound `factor < 1`. -/
  factor_lt_one : factor < 1
  /-- Global Lipschitz contraction inequality. -/
  lip : ∀ x y : ℝ, |toFun x - toFun y| ≤ factor * |x - y|

namespace ContractionMap

/-- Predicate stating that `x` is a fixed point of `T`. -/
def IsFixedPt (T : ContractionMap) (x : ℝ) : Prop :=
  T.toFun x = x

/-- The contraction slack `1 - T.factor`, strictly positive for every contraction. -/
def slack (T : ContractionMap) : ℝ :=
  1 - T.factor

/-!
---

## 2. Stage 2 & 3: Top-Down Lemma Outlining, Revision, and Fleshing Out

In Stage 2, you first write the helper signatures with `:= by sorry` and prove `fixedPt_unique`
from those stubs alone, checking that binders and dependency flow compile before any helper proofs:

```lean
lemma slack_pos : 0 < T.slack := by sorry
lemma dist_fixed_step (x : ℝ) {x_star : ℝ} (h_fix : T.IsFixedPt x_star) :
    |T.toFun x - x_star| ≤ T.factor * |x - x_star| := by sorry
lemma slack_mul_dist_le_residual (x : ℝ) {x_star : ℝ} (h_fix : T.IsFixedPt x_star) :
    T.slack * |x - x_star| ≤ |x - T.toFun x| := by sorry

theorem fixedPt_unique {x_star y_star : ℝ} ... := by ... -- proved using the stubs above!
```

Outlining early also exposes **statement revisions** before any proof effort is wasted:
- **Cleared denominators vs. division:** Writing `T.slack * |x - x_star| ≤ |x - T.toFun x|`
  instead of `|x - x_star| ≤ |x - T.toFun x| / (1 - T.factor)` avoids `1 - c ≠ 0` division
  side-conditions and lets `linarith` combine the bound directly with `abs_sub_le`.
- **Explicit vs. implicit binders:** In `dist_fixed_step`, `h_fix : T.IsFixedPt x_star` mentions
  `x_star` (which can be `{x_star : ℝ}` implicit) but does not mention `x`. Keeping `(x : ℝ)`
  explicit lets callers write `T.dist_fixed_step x h_fix` cleanly without unresolved metavariables.

Below is the Stage 3 fleshed-out, `sorry`-free `BasicAPI` section using shared
`variable (T : ContractionMap)`.
-/

section BasicAPI

variable (T : ContractionMap)

/-- Unfolding lemma for `T.IsFixedPt x`, registered with `@[simp]` for automation. -/
@[simp]
lemma isFixedPt_iff {x : ℝ} : T.IsFixedPt x ↔ T.toFun x = x :=
  Iff.rfl

/-- Every contraction has strictly positive slack `0 < 1 - T.factor`. -/
lemma slack_pos : 0 < T.slack := by
  unfold slack
  linarith [T.factor_lt_one]

/-- One application of `T` shrinks distance to any fixed point `x_star` by `T.factor`. -/
lemma dist_fixed_step (x : ℝ) {x_star : ℝ} (h_fix : T.IsFixedPt x_star) :
    |T.toFun x - x_star| ≤ T.factor * |x - x_star| := by
  have h_lip := T.lip x x_star
  rwa [h_fix] at h_lip

/-- A-posteriori residual bound: `(1 - c) * |x - x_star| ≤ |x - T x|`. -/
lemma slack_mul_dist_le_residual (x : ℝ) {x_star : ℝ} (h_fix : T.IsFixedPt x_star) :
    T.slack * |x - x_star| ≤ |x - T.toFun x| := by
  have h_tri : |x - x_star| ≤ |x - T.toFun x| + |T.toFun x - x_star| :=
    abs_sub_le x (T.toFun x) x_star
  have h_step : |T.toFun x - x_star| ≤ T.factor * |x - x_star| :=
    T.dist_fixed_step x h_fix
  unfold slack
  linarith

/-- Uniqueness of fixed points: any two fixed points of `T` must be equal. -/
theorem fixedPt_unique {x_star y_star : ℝ}
    (hx : T.IsFixedPt x_star) (hy : T.IsFixedPt y_star) : x_star = y_star := by
  have h_res : T.slack * |x_star - y_star| ≤ |x_star - T.toFun x_star| :=
    T.slack_mul_dist_le_residual x_star hy
  rw [hx, sub_self, abs_zero] at h_res
  have h_nonneg : 0 ≤ T.slack * |x_star - y_star| := by
    have := T.slack_pos
    positivity
  have h_zero : |x_star - y_star| = 0 := by
    cases mul_eq_zero.mp (le_antisymm h_res h_nonneg) with
    | inl h_s => linarith [T.slack_pos]
    | inr h_d => exact h_d
  exact sub_eq_zero.mp (abs_eq_zero.mp h_zero)

/-!
---

## 3. Exercises: Extending the `ContractionMap` Development

Notice that these exercises live inside `section BasicAPI` and `namespace ContractionMap`, so
`T : ContractionMap` is already in scope and earlier lemmas (`T.dist_fixed_step`,
`T.slack_mul_dist_le_residual`, `T.fixedPt_unique`) can be called with dot notation.
(Reference solutions are in
`LeanWorkshop/Solutions/Part4_Autoformalization/S2_ProofSketching.lean`.)
-/

/-- **Exercise 1a (Helper lemma):** Prove the Lipschitz bound for composing two contraction maps.
Notice how factoring this out keeps downstream two-step bounds clean. -/
lemma ex1a_comp_lip (T₁ T₂ : ContractionMap) (x y : ℝ) :
    |T₁.toFun (T₂.toFun x) - T₁.toFun (T₂.toFun y)| ≤ (T₁.factor * T₂.factor) * |x - y| := by
  sorry

/-- **Exercise 1b (Deduce from helper):** Prove the two-step contraction bound for
`T.toFun (T.toFun x)` using either `ex1a_comp_lip T T` or `T.dist_fixed_step` + `gcongr`. -/
lemma ex1b_dist_two_steps (x : ℝ) {x_star : ℝ} (h_fix : T.IsFixedPt x_star) :
    |T.toFun (T.toFun x) - x_star| ≤ T.factor ^ 2 * |x - x_star| := by
  sorry

/-- **Exercise 2:** Prove the one-step-ahead residual bound
`T.slack * |T.toFun x - x_star| ≤ T.factor * |x - T.toFun x|`
by combining `T.dist_fixed_step` and `T.slack_mul_dist_le_residual`. -/
lemma ex2_slack_mul_dist_next_le (x : ℝ) {x_star : ℝ} (h_fix : T.IsFixedPt x_star) :
    T.slack * |T.toFun x - x_star| ≤ T.factor * |x - T.toFun x| := by
  sorry

/-- Concrete contraction map `x ↦ x / 2 + 1` with factor `1 / 2`. -/
noncomputable def halfShift : ContractionMap where
  toFun x := x / 2 + 1
  factor := 1 / 2
  factor_nonneg := by norm_num
  factor_lt_one := by norm_num
  lip x y := by
    have h : x / 2 + 1 - (y / 2 + 1) = (1 / 2 : ℝ) * (x - y) := by ring
    rw [h, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- **Exercise 3:** Show that `2` is the unique fixed point of `halfShift` using
`halfShift.fixedPt_unique`. -/
theorem ex3_halfShift_unique_fixedPt {y_star : ℝ} (hy : halfShift.IsFixedPt y_star) :
    y_star = 2 := by
  sorry

end BasicAPI

end ContractionMap

end LeanWorkshop.Part4
