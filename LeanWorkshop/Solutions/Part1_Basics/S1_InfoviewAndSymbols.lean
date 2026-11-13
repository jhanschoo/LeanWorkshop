/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Basic.Real.Basic

/-!
# Solutions — Part 1.1: The Infoview and Symbol Input

Complete, `sorry`-free reference solutions for
`LeanWorkshop.Part1_Basics.S1_InfoviewAndSymbols`.
-/

namespace LeanWorkshop.Solutions.Part1

/-- **Exercise 1:** Define a function that maps a natural number `n` to `n * n + 1`. -/
def ex1_squarePlusOne (n : ℕ) : ℕ :=
  n * n + 1

/-- **Exercise 2:** Prove that for every natural number `n`, `n + 0 = n`. -/
theorem ex2_add_zero : ∀ n : ℕ, n + 0 = n := by
  intro n
  rfl

/-- **Exercise 3:** Swap the components of a conjunction `P ∧ Q`. -/
theorem ex3_swap_and (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.2
  · exact h.1

/-- **Exercise 4:** Chain two equality rewrites `h1 : a = b` and `h2 : b = c` to prove
`a + 2 = c + 2`. -/
theorem ex4_rewrite_chain (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a + 2 = c + 2 := by
  rw [h1, h2]

end LeanWorkshop.Solutions.Part1
