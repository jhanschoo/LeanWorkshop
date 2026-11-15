/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Solutions — Part 4.1: Statement Translation (Autoformalization)

Complete, `sorry`-free reference solutions for
`LeanWorkshop.Part4_Autoformalization.S1_StatementTranslation`.
-/

namespace LeanWorkshop.Solutions.Part4

/-- **Exercise 1a:** Refute naive `ℕ` subtraction cancellation with `a = 2, b = 5`. -/
theorem ex1a_refute_naive_sub : ¬ (∀ a b : ℕ, a - b + b = a) := by
  intro h
  have hfalse : (2 : ℕ) - 5 + 5 = 2 := h 2 5
  omega

/-- **Exercise 1b:** Cancel `b` when `b ≤ a` using `omega`. -/
theorem ex1b_nat_sub_cancel {a b : ℕ} (h : b ≤ a) : a - b + b = a := by
  omega

/-- **Exercise 2a:** Refute naive division cancellation at `x = 1, y = 0, z = 0`. -/
theorem ex2a_refute_naive_div : ¬ (∀ x y z : ℝ, x / y = z → x = z * y) := by
  intro h
  have hfalse : (1 : ℝ) = 0 * 0 := h 1 0 0 (by norm_num)
  linarith

/-- **Exercise 2b:** Rewrite `z` using `h` and apply Mathlib's `div_mul_cancel₀`. -/
theorem ex2b_div_eq_mul {x y z : ℝ} (hy : y ≠ 0) (h : x / y = z) : x = z * y := by
  rw [← h, div_mul_cancel₀ x hy]

/-- **Exercise 2c:** Concrete non-vacuity sanity check instantiating `ex2b_div_eq_mul`. -/
theorem ex2c_div_sanity : (6 : ℝ) = 2 * 3 :=
  ex2b_div_eq_mul (x := 6) (y := 3) (z := 2) (by norm_num) (by norm_num)

/-- **Exercise 3:** Apply `hf.injective` directly from `StrictMono`. -/
theorem ex3_strictMono_eq_imp_eq {f : ℝ → ℝ} (hf : StrictMono f) {x y : ℝ}
    (h : f x = f y) : x = y :=
  hf.injective h

end LeanWorkshop.Solutions.Part4
