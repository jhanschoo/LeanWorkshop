/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linter.Lint
import Mathlib.Data.Nat.Basic

/-!
# Solutions for Part 3.4: Mathlib Style Guide and Linters
-/

namespace LeanWorkshop.Part3.Solutions

/-- **Exercise 1:** Prove functional equality using `funext` and `Nat.add_zero`. -/
theorem ex1_clean_lambda : (fun n : ℕ ↦ n + 0) = (fun n : ℕ ↦ n) := by
  funext n
  exact Nat.add_zero n

/-- **Exercise 2:** Prove a conjunction using `constructor` and `·` bullets. -/
theorem ex2_clean_bullets (P Q R : Prop) (hpq : P → Q) (hpr : P → R) (hp : P) : Q ∧ R := by
  constructor
  · exact hpq hp
  · exact hpr hp

/-- **Exercise 3:** Universe-polymorphic identity holds definitionally by `rfl`. -/
theorem ex3_polymorphic_id {α : Type*} (x : α) : id x = x :=
  rfl

#lint

end LeanWorkshop.Part3.Solutions
