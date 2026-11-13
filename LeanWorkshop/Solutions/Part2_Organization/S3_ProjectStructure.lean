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

/-- **Exercise 1a:** Define scalar multiplication `scale (k : ℤ) (p : Point2D)` that multiplies
both coordinates of `p` by `k`. -/
def scale (k : ℤ) (p : Point2D) : Point2D :=
  ⟨k * p.x, k * p.y⟩

/-- **Exercise 1b:** Prove that scaling `p` by `1` returns `p`. -/
theorem scale_one (p : Point2D) : scale 1 p = p := by
  ext <;> simp [scale]

/-- **Exercise 2:** Prove that componentwise addition `Point2D.add` is commutative. -/
theorem add_comm_point (p q : Point2D) : p.add q = q.add p := by
  ext <;> simp [Int.add_comm]

/-- **Exercise 3:** Prove that swapping coordinates distributes over `Point2D.add`. -/
theorem swap_add (p q : Point2D) : (p.add q).swap = p.swap.add q.swap := by
  ext <;> simp

end LeanWorkshop.Solutions.Part2.Point2D
