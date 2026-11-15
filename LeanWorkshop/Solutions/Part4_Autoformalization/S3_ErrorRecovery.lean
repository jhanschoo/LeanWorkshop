/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Order.Monotone.Basic
import Mathlib.Basic.Real.Basic

/-!
# Solutions for Part 4.3: Steering AI Agents & Guarding Against Modern Failure Modes
-/

namespace LeanWorkshop.Part4.Solutions

/-- **Exercise 1:** Complete the square with `0 ≤ (x + 1 / 2) ^ 2` instead of the false subgoal. -/
theorem ex1_fix_false_subgoal (x : ℝ) : -1 / 4 ≤ x ^ 2 + x := by
  have h_sq : 0 ≤ (x + 1 / 2) ^ 2 := sq_nonneg (x + 1 / 2)
  linarith

/-- **Exercise 2:** Compose and add `Monotone` proofs directly via Mathlib's API. -/
theorem ex2_use_mathlib_monotone {f g : ℝ → ℝ} (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun x ↦ f (g x) + f x) :=
  (hf.comp hg).add hf

/-- **Exercise 3a:** Prove `a ≤ (a + b) / 2` from `a ≤ b`. -/
theorem ex3_avg_ge_min {a b : ℝ} (hab : a ≤ b) : a ≤ (a + b) / 2 := by
  linarith

/-- **Exercise 3b:** Instantiate `ex3_avg_ge_min` on `a = 3, b = 7` to rule out vacuity. -/
theorem ex3_sanity_check : (3 : ℝ) ≤ (3 + 7) / 2 :=
  ex3_avg_ge_min (by norm_num)

end LeanWorkshop.Part4.Solutions
