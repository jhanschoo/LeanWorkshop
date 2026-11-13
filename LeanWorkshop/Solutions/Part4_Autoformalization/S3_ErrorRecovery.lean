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
import Mathlib.Data.Nat.Basic

/-!
# Solutions for Part 4.3: Diagnosing and Recovering from Common Errors
-/

namespace LeanWorkshop.Part4.Solutions

/-- **Exercise 1:** Replace hallucinated `Nat.add_comm_right` with `Nat.add_right_comm`. -/
theorem ex1_fix_hallucinated_lemma (a b c : ℕ) : a + b + c = a + c + b :=
  Nat.add_right_comm a b c

/-- **Exercise 2:** Flip the rewrite direction with `rw [← h]`, then `ring`. -/
theorem ex2_fix_rw_direction {x y : ℝ} (h : x + 3 = y) : 2 * y = 2 * x + 6 := by
  rw [← h]
  ring

/-- **Exercise 3:** `x ^ 2` appears identically on both sides, so `linarith` cancels it. -/
theorem ex3_fix_nonlinear_linarith {x y : ℝ} (h : x ≤ y) :
    x + x ^ 2 ≤ y + x ^ 2 + 1 := by
  linarith

/-- **Exercise 4:** Substitute `h` with `rw [h]` before calling `ring`. -/
theorem ex4_fix_ring_with_hyp {a b : ℝ} (h : a = 2 * b + 1) :
    a ^ 2 - 4 * b ^ 2 = 4 * b + 1 := by
  rw [h]
  ring

end LeanWorkshop.Part4.Solutions
