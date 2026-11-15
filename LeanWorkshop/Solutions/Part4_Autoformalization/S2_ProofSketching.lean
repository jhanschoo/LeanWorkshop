/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import LeanWorkshop.Part4_Autoformalization.S2_ProofSketching

/-!
# Solutions — Part 4.2: Outlining and Incremental Formalization

Complete, `sorry`-free reference solutions for
`LeanWorkshop.Part4_Autoformalization.S2_ProofSketching`.
-/

namespace LeanWorkshop.Solutions.Part4

open LeanWorkshop.Part4
open ContractionMap

section BasicAPI

variable (T : ContractionMap)

/-- **Exercise 1a:** Prove the Lipschitz bound for composing two contractions via `gcongr`. -/
lemma ex1a_comp_lip (T₁ T₂ : ContractionMap) (x y : ℝ) :
    |T₁.toFun (T₂.toFun x) - T₁.toFun (T₂.toFun y)| ≤ (T₁.factor * T₂.factor) * |x - y| := by
  have h1 : |T₁.toFun (T₂.toFun x) - T₁.toFun (T₂.toFun y)| ≤
      T₁.factor * |T₂.toFun x - T₂.toFun y| := T₁.lip (T₂.toFun x) (T₂.toFun y)
  have h2 : |T₂.toFun x - T₂.toFun y| ≤ T₂.factor * |x - y| := T₂.lip x y
  have h3 : T₁.factor * |T₂.toFun x - T₂.toFun y| ≤
      T₁.factor * (T₂.factor * |x - y|) := by
    have := T₁.factor_nonneg
    gcongr
  linarith

/-- **Exercise 1b:** Specialize `ex1a_comp_lip` to `T` and `x_star` to deduce the two-step bound.
-/
lemma ex1b_dist_two_steps (x : ℝ) {x_star : ℝ} (h_fix : T.IsFixedPt x_star) :
    |T.toFun (T.toFun x) - x_star| ≤ T.factor ^ 2 * |x - x_star| := by
  have h_comp := ex1a_comp_lip T T x x_star
  have h_fix' : T.toFun x_star = x_star := h_fix
  rw [h_fix', h_fix', ← sq T.factor] at h_comp
  exact h_comp

/-- **Exercise 2:** Combine `T.dist_fixed_step` and `T.slack_mul_dist_le_residual`. -/
lemma ex2_slack_mul_dist_next_le (x : ℝ) {x_star : ℝ} (h_fix : T.IsFixedPt x_star) :
    T.slack * |T.toFun x - x_star| ≤ T.factor * |x - T.toFun x| := by
  have h_step : |T.toFun x - x_star| ≤ T.factor * |x - x_star| :=
    T.dist_fixed_step x h_fix
  have h_res : T.slack * |x - x_star| ≤ |x - T.toFun x| :=
    T.slack_mul_dist_le_residual x h_fix
  have h1 : T.slack * |T.toFun x - x_star| ≤ T.slack * (T.factor * |x - x_star|) := by
    have := T.slack_pos.le
    gcongr
  have h2 : T.factor * (T.slack * |x - x_star|) ≤ T.factor * |x - T.toFun x| := by
    have := T.factor_nonneg
    gcongr
  linarith

/-- **Exercise 3:** Show `2` is a fixed point of `halfShift` and apply `fixedPt_unique`. -/
theorem ex3_halfShift_unique_fixedPt {y_star : ℝ} (hy : halfShift.IsFixedPt y_star) :
    y_star = 2 := by
  have h2 : halfShift.IsFixedPt 2 := by
    simp [halfShift]
    norm_num
  exact halfShift.fixedPt_unique hy h2

end BasicAPI

end LeanWorkshop.Solutions.Part4
