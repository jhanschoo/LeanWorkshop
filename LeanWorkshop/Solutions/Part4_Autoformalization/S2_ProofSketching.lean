/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import LeanWorkshop.Part4_Autoformalization.S2_ProofSketching

/-!
# Solutions for Part 4.2: Outlining and Incremental Formalization
-/

namespace LeanWorkshop.Part4.Solutions

open LeanWorkshop.Part4
open ContractionMap

section BasicAPI

variable (T : ContractionMap)

/-- **Exercise 1:** Prove the two-step contraction bound using `T.dist_fixed_step` and `gcongr`. -/
lemma ex1_dist_two_steps (x : ℝ) {x_star : ℝ} (h_fix : T.IsFixedPt x_star) :
    |T.toFun (T.toFun x) - x_star| ≤ T.factor ^ 2 * |x - x_star| := by
  have h1 : |T.toFun (T.toFun x) - x_star| ≤ T.factor * |T.toFun x - x_star| :=
    T.dist_fixed_step (T.toFun x) h_fix
  have h2 : |T.toFun x - x_star| ≤ T.factor * |x - x_star| :=
    T.dist_fixed_step x h_fix
  have h_mul : T.factor * |T.toFun x - x_star| ≤ T.factor * (T.factor * |x - x_star|) := by
    have := T.factor_nonneg
    gcongr
  linarith [sq T.factor]

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

end LeanWorkshop.Part4.Solutions
