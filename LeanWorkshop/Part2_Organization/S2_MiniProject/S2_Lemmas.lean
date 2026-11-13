/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import LeanWorkshop.Part2_Organization.S2_MiniProject.S1_Defs

/-!
# Part 2.2b: MiniProject — API Lemmas (`Point2D`)

This module imports `S1_Defs.lean` and builds a reusable **API layer** over `Point2D`:
1. Coordinate projection `@[simp]` lemmas so the simplifier (`simp`) knows how `origin`, `add`, and
   `swap` act on `.x` and `.y`.
2. Algebraic properties inside `namespace Point2D`, enabling **dot notation** (`p.swap_swap`,
   `p.add_origin`, `p.normSq_swap`).
-/

namespace LeanWorkshop.Part2.Point2D

variable (p q : Point2D)

/-! ### 1. Coordinate `@[simp]` Lemmas -/

@[simp]
theorem origin_x : origin.x = 0 := by
  rfl

@[simp]
theorem origin_y : origin.y = 0 := by
  rfl

@[simp]
theorem add_x : (p.add q).x = p.x + q.x := by
  rfl

@[simp]
theorem add_y : (p.add q).y = p.y + q.y := by
  rfl

@[simp]
theorem swap_x : p.swap.x = p.y := by
  rfl

@[simp]
theorem swap_y : p.swap.y = p.x := by
  rfl

/-! ### 2. Structural & Algebraic Lemmas (Supporting Dot Notation) -/

/-- Swapping coordinates twice returns the original point (`p.swap.swap = p`). -/
@[simp]
theorem swap_swap : p.swap.swap = p := by
  ext <;> rfl

/-- Adding `origin` on the right leaves `p` unchanged (`p.add origin = p`). -/
@[simp]
theorem add_origin : p.add origin = p := by
  ext <;> simp

/-- Adding `origin` on the left leaves `p` unchanged (`origin.add p = p`). -/
@[simp]
theorem origin_add : origin.add p = p := by
  ext <;> simp

/-- The squared norm of `origin` is `0`. -/
@[simp]
theorem normSq_origin : origin.normSq = 0 := by
  rfl

/-- Swapping coordinates preserves the squared Euclidean norm. -/
theorem normSq_swap : p.swap.normSq = p.normSq := by
  unfold normSq
  simp [Int.add_comm]

end LeanWorkshop.Part2.Point2D
