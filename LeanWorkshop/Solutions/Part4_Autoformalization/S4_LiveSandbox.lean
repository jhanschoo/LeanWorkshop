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
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Basic
import LeanWorkshop.Part4_Autoformalization.S4_LiveSandbox

/-!
# Solutions for Part 4.4: Live Autoformalization Sandbox
-/

namespace LeanWorkshop.Part4.Solutions

open LeanWorkshop.Part4

/-- **Challenge 1:** Algebraic identity over `ℤ` via `ring`. -/
theorem challenge1_consecutive_squares (n : ℤ) : (n + 1) ^ 2 - n ^ 2 = 2 * n + 1 := by
  ring

/-- **Challenge 2:** Convex combination bounds via `mul_nonneg` and `linarith`. -/
theorem challenge2_weighted_average {a b w : ℝ}
    (hab : a ≤ b) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    a ≤ (1 - w) * a + w * b ∧ (1 - w) * a + w * b ≤ b := by
  have h1 : 0 ≤ w * (b - a) := mul_nonneg hw0 (by linarith)
  have h2 : 0 ≤ (1 - w) * (b - a) := mul_nonneg (by linarith) (by linarith)
  constructor <;> linarith

/-- **Challenge 3:** Gauss's summation formula by induction and `ring`. -/
theorem challenge3_gauss_sum (n : ℕ) : 2 * sumUpTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumUpTo, Nat.mul_add, ih]
    ring

/-- **Challenge 4:** 2D Cauchy-Schwarz via Lagrange's identity and `sq_nonneg`. -/
theorem challenge4_cauchy_schwarz_2d (a1 a2 b1 b2 : ℝ) :
    (a1 * b1 + a2 * b2) ^ 2 ≤ (a1 ^ 2 + a2 ^ 2) * (b1 ^ 2 + b2 ^ 2) := by
  have h_id :
      (a1 ^ 2 + a2 ^ 2) * (b1 ^ 2 + b2 ^ 2) - (a1 * b1 + a2 * b2) ^ 2 =
        (a1 * b2 - a2 * b1) ^ 2 := by
    ring
  have h_sq : 0 ≤ (a1 * b2 - a2 * b1) ^ 2 := sq_nonneg (a1 * b2 - a2 * b1)
  linarith

end LeanWorkshop.Part4.Solutions
