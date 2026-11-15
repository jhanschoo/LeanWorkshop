/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import LeanWorkshop.Part2_Organization.S2_MiniProject.S1_Defs
import LeanWorkshop.Part2_Organization.S2_MiniProject.S2_Lemmas
import LeanWorkshop.Part2_Organization.S3_ProjectStructure

/-!
# Solutions — Part 2.3: Project Structure and Imports

Complete, `sorry`-free reference solutions corresponding to
`LeanWorkshop.Part2_Organization.S3_ProjectStructure`.
-/

namespace LeanWorkshop.Solutions.Part2.Point2D

open LeanWorkshop.Part2
open LeanWorkshop.Part2.Point2D

variable {α : Type*} [AddCommMonoid α] [Preorder α] [IsOrderedAddMonoid α]

/-- **Exercise 1a:** Shift both coordinates of `p` by `c ≥ 0` while preserving `0 ≤ x + y`. -/
def shiftDiag (c : α) (hc : 0 ≤ c) (p : Point2D α) : Point2D α :=
  ⟨p.x + c, p.y + c, by
    rw [add_add_add_comm]
    exact add_nonneg p.nonneg_sum (add_nonneg hc hc)⟩

/-- **Exercise 1b:** Shifting by `0` leaves `p` unchanged (using `ext` + proof irrelevance). -/
theorem shiftDiag_zero (p : Point2D α) : shiftDiag 0 le_rfl p = p := by
  ext <;> simp [shiftDiag]

/-- **Exercise 2:** Componentwise addition `+` on `Point2D α` is commutative. -/
theorem add_comm_point (p q : Point2D α) : p + q = q + p := by
  ext <;> simp [add_comm]

/-- **Exercise 3:** Swapping coordinates distributes over `+`. -/
theorem swap_add (p q : Point2D α) : (p + q).swap = p.swap + q.swap := by
  ext <;> simp

end LeanWorkshop.Solutions.Part2.Point2D
