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
# Solutions — Part 3.2: Mathlib Nomenclature and Dot Notation

Complete, `sorry`-free reference solutions for
`LeanWorkshop.Part3_Mathlib.S2_Nomenclature`.
-/

namespace LeanWorkshop.Solutions.Part3

/-- **Exercise 1:** Combine `a ≤ b` and `b < c` via `lt_of_le_of_lt`. -/
theorem ex1_predict_name {a b c : ℤ} (h1 : a ≤ b) (h2 : b < c) : a < c :=
  lt_of_le_of_lt h1 h2

/-- **Exercise 2:** Right-distributivity via `add_mul`. -/
theorem ex2_predict_distrib (a b c : ℤ) : (a + b) * c = a * c + b * c :=
  add_mul a b c

/-- **Exercise 3:** Sum of positive integers via `add_pos`. -/
theorem ex3_predict_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  add_pos ha hb

/-- **Exercise 4:** Chain equalities using `.trans` and `.symm`. -/
theorem ex4_dot_chain {a b c : ℕ} (h1 : a = b) (h2 : c = b) : a = c :=
  h1.trans h2.symm

/-- **Exercise 5:** Extract `≤` and `≠` from `a < b` via `.le` and `.ne`. -/
theorem ex5_lt_imp_le_and_ne {a b : ℕ} (h : a < b) : a ≤ b ∧ a ≠ b :=
  ⟨h.le, h.ne⟩

end LeanWorkshop.Solutions.Part3
