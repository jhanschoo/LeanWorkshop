/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Use
import Mathlib.Data.Nat.Basic
import LeanWorkshop.Part1_Basics.S2_BasicProofs

/-!
# Solutions — Part 1.2: Basic Mathematical Proofs

Complete, `sorry`-free reference solutions for
`LeanWorkshop.Part1_Basics.S2_BasicProofs`.
-/

namespace LeanWorkshop.Solutions.Part1

open LeanWorkshop.Part1

/-- **Exercise 1:** Prove `R` from `hp : P`, `hpq : P ∧ Q → R`, and `hq : Q`. -/
theorem ex1_and_imp (P Q R : Prop) (hp : P) (hq : Q) (hpq : P ∧ Q → R) : R := by
  apply hpq
  constructor
  · exact hp
  · exact hq

/-- **Exercise 2:** Prove that `∧` distributes over `∨` from the left. -/
theorem ex2_and_or_distrib (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro h
    rcases h with ⟨hp, hq | hr⟩
    · left
      exact ⟨hp, hq⟩
    · right
      exact ⟨hp, hr⟩
  · intro h
    rcases h with ⟨hp, hq⟩ | ⟨hp, hr⟩
    · exact ⟨hp, Or.inl hq⟩
    · exact ⟨hp, Or.inr hr⟩

/-- **Exercise 3:** Prove that `14` is even by providing an explicit witness `k` with `use`. -/
theorem ex3_fourteen_even : ∃ k : ℕ, 14 = 2 * k := by
  use 7

/-- **Exercise 4:** Prove by induction on `n` that `double n = n + n`. -/
theorem ex4_double_eq_add_self (n : ℕ) : double n = n + n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [double, ih]
    rw [← Nat.add_assoc (n + 1)]
    rw [Nat.add_right_comm n 1 n, Nat.add_assoc (n + n) 1 1]

end LeanWorkshop.Solutions.Part1
