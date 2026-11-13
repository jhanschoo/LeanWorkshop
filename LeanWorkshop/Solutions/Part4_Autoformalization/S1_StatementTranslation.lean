/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Use
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Prime.Basic

/-!
# Solutions for Part 4.1: Statement Translation (Autoformalization)
-/

namespace LeanWorkshop.Part4.Solutions

/-- **Exercise 1:** Cancel `b` when `b ≤ a` using `omega`. -/
theorem ex1_nat_sub_cancel {a b : ℕ} (h : b ≤ a) : a - b + b = a := by
  omega

/-- **Exercise 2:** Midpoint lies between `x` and `y` via `linarith`. -/
theorem ex2_real_average {x y : ℝ} (h : x ≤ y) :
    x ≤ (x + y) / 2 ∧ (x + y) / 2 ≤ y := by
  constructor <;> linarith

/-- **Exercise 3:** Square of `2 * k + 1` is `2 * (2 * k ^ 2 + 2 * k) + 1`. -/
theorem ex3_odd_square {n : ℤ} (k : ℤ) (hn : n = 2 * k + 1) :
    ∃ m : ℤ, n ^ 2 = 2 * m + 1 := by
  use 2 * k ^ 2 + 2 * k
  rw [hn]
  ring

/-- **Exercise 4:** Cast `m ≤ n` to `ℝ` with `Nat.cast_le`, then finish with `linarith`. -/
theorem ex4_coercion_mono {m n : ℕ} (h : m ≤ n) : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
  have h' : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr h
  linarith

end LeanWorkshop.Part4.Solutions
