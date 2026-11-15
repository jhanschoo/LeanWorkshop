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

/-- **Exercise 3a:** Contradict `f 0 + 1 ≤ f 0` using `hf 0 0`. -/
theorem ex3a_vacuous_hyp_impossible : ¬ (∃ f : ℝ → ℝ, ∀ x y : ℝ, f x + 1 ≤ f y) := by
  rintro ⟨f, hf⟩
  linarith [hf 0 0]

/-- **Exercise 3b:** Combine steps `0 → 1` and `1 → 2` via `linarith`. -/
theorem ex3b_step_bound_fixed (f : ℝ → ℝ) (h : ∀ x y : ℝ, x + 1 ≤ y → f x + 1 ≤ f y) :
    f 0 + 2 ≤ f 2 := by
  linarith [h 0 1 (by norm_num), h 1 2 (by norm_num)]

/-- **Exercise 3c:** Instantiate `ex3b_step_bound_fixed` on `id` to confirm non-vacuity. -/
theorem ex3c_step_bound_sanity : (0 : ℝ) + 2 ≤ 2 :=
  ex3b_step_bound_fixed id (fun _ _ h ↦ h)

end LeanWorkshop.Part4.Solutions
