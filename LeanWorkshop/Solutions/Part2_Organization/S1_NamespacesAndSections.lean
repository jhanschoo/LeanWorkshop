/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Data.Nat.Basic
import LeanWorkshop.Part2_Organization.S1_NamespacesAndSections

/-!
# Solutions — Part 2.1: Namespaces and Sections

Complete, `sorry`-free reference solutions corresponding to
`LeanWorkshop.Part2_Organization.S1_NamespacesAndSections`.
-/

namespace LeanWorkshop.Solutions.Part2

open LeanWorkshop.Part2

namespace TempConv

/-- **Exercise 1a:** Define integer temperature conversion from Celsius to Kelvin (`c + 273`). -/
def toKelvin (c : ℕ) : ℕ :=
  c + 273

/-- **Exercise 1b:** Prove that `0` degrees Celsius is `273` Kelvin. -/
theorem toKelvin_zero : toKelvin 0 = 273 := by
  rfl

end TempConv

open Geometry in
/-- **Exercise 2:** Use `open Geometry in` (or qualified names) to prove that a square of side `3`
has `area 3 + perimeter 3 = 21`. -/
theorem ex2_square_three : area 3 + perimeter 3 = 21 := by
  rfl

section ExerciseSection

variable (a b c : ℕ)

/-- **Exercise 3:** Using the section variables `a`, `b`, and `c`, prove
`(a + b) + c = (a + c) + b`. -/
theorem ex3_add_rearrange : a + b + c = a + c + b := by
  exact Nat.add_right_comm a b c

end ExerciseSection

end LeanWorkshop.Solutions.Part2
