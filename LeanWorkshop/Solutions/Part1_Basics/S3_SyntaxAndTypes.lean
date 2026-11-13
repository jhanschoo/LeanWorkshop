/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Group.Defs
import LeanWorkshop.Part1_Basics.S3_SyntaxAndTypes

/-!
# Solutions — Part 1.3: Basic Mathematical Syntax and Types

Complete, `sorry`-free reference solutions for
`LeanWorkshop.Part1_Basics.S3_SyntaxAndTypes`.
-/

namespace LeanWorkshop.Solutions.Part1

open LeanWorkshop.Part1

/-- **Exercise 1:** Define the quadratic expression `a * x ^ 2 + b * x + c` over the integers `ℤ`.
-/
def ex1_quad (a b c x : ℤ) : ℤ :=
  a * x ^ 2 + b * x + c

/-- **Exercise 2:** Define polymorphic function composition `(g ∘ f) x = g (f x)`. -/
def ex2_myComp {α β γ : Type*} (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

/-- **Exercise 3:** Prove that `monoidSquare (1 : M) = 1` in any `Monoid M`. -/
theorem ex3_monoidSquare_one {M : Type*} [Monoid M] : monoidSquare (1 : M) = 1 := by
  unfold monoidSquare
  rw [mul_one]

/-- **Exercise 4:** Give a direct term-mode proof of the transitivity of implication. -/
theorem ex4_imp_trans {P Q R : Prop} : (P → Q) → (Q → R) → P → R :=
  fun hpq hqr hp ↦ hqr (hpq hp)

/-- **Exercise 5:** Use `exact h _ _` together with an inline `(by ...)` block to prove
`f (x + 0) = f x` from `h : ∀ a b : ℕ, a = b → f a = f b`. -/
theorem ex5_inline_by (f : ℕ → ℕ) (h : ∀ a b : ℕ, a = b → f a = f b) (x : ℕ) :
    f (x + 0) = f x := by
  exact h _ _ (by rfl)

end LeanWorkshop.Solutions.Part1
