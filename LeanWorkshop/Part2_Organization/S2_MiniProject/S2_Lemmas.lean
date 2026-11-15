/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import LeanWorkshop.Part2_Organization.S2_MiniProject.S1_Defs

/-!
# Part 2.2b: MiniProject — API Lemmas (`Point2D`)

This module imports `S1_Defs.lean` and builds a reusable, typeclass-generic **API layer** over
`Point2D α`:
1. **`@[simp]` annotations** on coordinate projections and typeclass bridges (`zero_def`,
   `add_def`) so `simp` unfolds `0`, `+`, `origin`, `add`, and `swap` on `.x` and `.y`.
2. **Algebraic lemmas with `ext` & proof irrelevance**: notice that `ext <;> rfl` and `ext <;> simp`
   only produce **two** coordinate goals (`.x` and `.y`), because `Point2D.ext` ignores the `Prop`
   field `nonneg_sum` by proof irrelevance!
3. **Dot notation** inside `namespace Point2D` (`p.swap_swap`, `p.add_origin`, `p.normSq_swap`).
-/

namespace LeanWorkshop.Part2.Point2D

section OrderedAddCommMonoid

variable {α : Type*} [AddCommMonoid α] [Preorder α]

/-! ### 1. Coordinate & Typeclass `@[simp]` Lemmas -/

@[simp]
theorem zero_def : (0 : Point2D α) = origin :=
  rfl

@[simp]
theorem add_def [IsOrderedAddMonoid α] (p q : Point2D α) : p + q = p.add q :=
  rfl

@[simp]
theorem origin_x : (origin : Point2D α).x = 0 :=
  rfl

@[simp]
theorem origin_y : (origin : Point2D α).y = 0 :=
  rfl

@[simp]
theorem add_x [IsOrderedAddMonoid α] (p q : Point2D α) : (p.add q).x = p.x + q.x :=
  rfl

@[simp]
theorem add_y [IsOrderedAddMonoid α] (p q : Point2D α) : (p.add q).y = p.y + q.y :=
  rfl

@[simp]
theorem swap_x (p : Point2D α) : p.swap.x = p.y :=
  rfl

@[simp]
theorem swap_y (p : Point2D α) : p.swap.y = p.x :=
  rfl

/-! ### 2. Bundled Invariant & Algebraic Lemmas (Supporting Dot Notation) -/

/-- Expose the bundled invariant `0 ≤ p.x + p.y` as a dot-notation lemma. -/
theorem nonneg_sum_coords (p : Point2D α) : 0 ≤ p.x + p.y :=
  p.nonneg_sum

/-- Swapping coordinates twice returns the original point (`p.swap.swap = p`).
Thanks to proof irrelevance, `ext` only asks for `.x` and `.y`—not `nonneg_sum`! -/
@[simp]
theorem swap_swap (p : Point2D α) : p.swap.swap = p := by
  ext <;> rfl

/-- Adding `origin` on the right leaves `p` unchanged (`p.add origin = p`). -/
@[simp]
theorem add_origin [IsOrderedAddMonoid α] (p : Point2D α) : p.add origin = p := by
  ext <;> simp

/-- Adding `origin` on the left leaves `p` unchanged (`origin.add p = p`). -/
@[simp]
theorem origin_add [IsOrderedAddMonoid α] (p : Point2D α) : origin.add p = p := by
  ext <;> simp

/-- Adding `0` on the right leaves `p` unchanged (`p + 0 = p`). -/
theorem add_zero_point [IsOrderedAddMonoid α] (p : Point2D α) : p + 0 = p := by
  simp

/-- Adding `0` on the left leaves `p` unchanged (`0 + p = p`). -/
theorem zero_add_point [IsOrderedAddMonoid α] (p : Point2D α) : 0 + p = p := by
  simp

end OrderedAddCommMonoid

section Semiring

variable {α : Type*} [Semiring α] [Preorder α] (p : Point2D α)

/-- The squared norm of `origin` is `0`. -/
@[simp]
theorem normSq_origin : (origin : Point2D α).normSq = 0 := by
  simp [normSq]

/-- Swapping coordinates preserves the squared Euclidean norm. -/
theorem normSq_swap : p.swap.normSq = p.normSq := by
  unfold normSq
  simp [add_comm]

end Semiring

end LeanWorkshop.Part2.Point2D
