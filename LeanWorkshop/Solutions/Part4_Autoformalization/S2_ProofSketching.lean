/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Basic.Real.Basic

/-!
# Solutions for Part 4.2: Proof Sketching (Draft, Sketch, Prove)
-/

namespace LeanWorkshop.Part4.Solutions

/-- **Exercise 1:** Prove the sum-of-squares steps with `positivity` and `ring`. -/
theorem ex1_sum_of_squares_bound (a b c : ℝ) :
    a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have h1 : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by
    positivity
  have h2 :
      (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 =
        2 * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)) := by
    ring
  linarith

/-- **Exercise 2:** Discharge the interval subgoals from `hx` and `hy`. -/
theorem ex2_abs_bound_sketch {x y : ℝ} (hx : -2 ≤ x ∧ x ≤ 2) (hy : -3 ≤ y ∧ y ≤ 3) :
    2 * x - y ≤ 7 := by
  have hx_upper : 2 * x ≤ 4 := by
    linarith [hx.2]
  have hy_lower : -3 ≤ y :=
    hy.1
  linarith

/-- **Exercise 3:** Factor the cubic, prove each factor nonnegative, and combine. -/
theorem ex3_cubic_factor_sketch {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ x ^ 3 - x ^ 2 - x + 1 := by
  have h_factor : x ^ 3 - x ^ 2 - x + 1 = (x - 1) ^ 2 * (x + 1) := by
    ring
  have h_sq : 0 ≤ (x - 1) ^ 2 := by
    positivity
  have h_pos : 0 ≤ x + 1 := by
    linarith
  rw [h_factor]
  exact mul_nonneg h_sq h_pos

end LeanWorkshop.Part4.Solutions
