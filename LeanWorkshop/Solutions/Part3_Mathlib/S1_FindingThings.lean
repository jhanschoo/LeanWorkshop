/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Order.Basic

/-!
# Solutions — Part 3.1: Finding Things in Mathlib and Community Resources

Complete, `sorry`-free reference solutions for
`LeanWorkshop.Part3_Mathlib.S1_FindingThings`.
-/

namespace LeanWorkshop.Solutions.Part3

/-- **Exercise 1:** Re-associate `a + (a + b)` using `Nat.add_assoc`. -/
theorem ex1_absorb (a b : ℕ) : a + (a + b) = a + a + b :=
  (Nat.add_assoc a a b).symm

/-- **Exercise 2:** Convert `a < b + 1` to `a ≤ b` using `Nat.le_of_lt_succ`. -/
theorem ex2_le_of_lt_add_one {a b : ℕ} (h : a < b + 1) : a ≤ b :=
  Nat.le_of_lt_succ h

/-- **Exercise 3:** Cancel `- b + b` on `ℤ` using `Int.sub_add_cancel`. -/
theorem ex3_sub_add_cancel (a b : ℤ) : a - b + b = a :=
  Int.sub_add_cancel a b

/-- **Exercise 4:** Show `a ≤ max a b` using `le_max_left`. -/
theorem ex4_le_max_left (a b : ℕ) : a ≤ max a b :=
  le_max_left a b

end LeanWorkshop.Solutions.Part3
