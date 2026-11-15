/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import LeanWorkshop.Part2_Organization.S2_MiniProject.S1_Defs
import LeanWorkshop.Part2_Organization.S2_MiniProject.S2_Lemmas

/-!
# Part 2.3: Project Structure and Imports

In this module we zoom out from single files to see how a Lean 4 repository is organized, built,
and connected across multiple modules.

---

## 1. How Lean 4 Maps Module Names to File Paths

In Lean 4, module imports follow a strict 1-to-1 filesystem convention relative to the project
root:

- `import LeanWorkshop`
  maps to `LeanWorkshop.lean` (root barrel file)
- `import LeanWorkshop.Part1_Basics.S1_InfoviewAndSymbols`
  maps to `LeanWorkshop/Part1_Basics/S1_InfoviewAndSymbols.lean`
- `import LeanWorkshop.Part2_Organization.S2_MiniProject.S1_Defs`
  maps to `LeanWorkshop/Part2_Organization/S2_MiniProject/S1_Defs.lean`

Key rules:
1. **`import` statements must appear at the very top of a file** (immediately after the copyright
   comment and before any `/-! ... -/` module docstring or commands).
2. **Transitive imports:** Because `S2_Lemmas.lean` already imports `S1_Defs.lean`, importing
   `S2_Lemmas` transitively brings `S1_Defs` into scope as well.
3. **Identifier naming:** Module path segments should be valid Lean identifiers (starting with a
   letter, like `Part2_Organization` or `S1_Defs`). Names starting with a digit (e.g. `01_Defs`)
   must be escaped with French quotes: `import LeanWorkshop.«01_Defs»`.

---

## 2. Understanding `lakefile.toml`, `lean-toolchain`, and `lake-manifest.json`

Every Lake project has three configuration files at its root:

1. **`lean-toolchain`**
   - Contains a single line (e.g. `leanprover/lean4:v4.36.0-rc2`).
   - Read automatically by `elan` to select the exact Lean compiler binary for the workspace.
2. **`lakefile.toml`** (or `lakefile.lean`)
   - Declares package metadata (`name = "LeanWorkshop"`), compiler/linter flags under
     `[leanOptions]` (`pp.unicode.fun = true`, `relaxedAutoImplicit = false`,
     `weak.linter.mathlibStandardSet = true`), external dependencies under `[[require]]`
     (`mathlib`), and build targets under `[[lean_lib]]`.
3. **`lake-manifest.json`**
   - Automatically generated lockfile pinning the exact Git commit SHA of every dependency
     (`mathlib`, `batteries`, `aesop`, `Qq`, `proofwidgets`, …).
   - Ensures reproducible builds across machines and works hand-in-hand with
     `lake exe cache get` to fetch precompiled `.olean` caches.

---

## 3. Using the `S2_MiniProject` Modules Together (Dot Notation & Instances in Action)

Because `Point2D` and its lemmas live in `namespace LeanWorkshop.Part2.Point2D`, any term
`p : Point2D` supports **projection (dot) notation** as well as the `Zero` and `Add` instances:
- Writing `p.swap` is shorthand for `Point2D.swap p`.
- Writing `p + 0` uses the `Add Point2D` and `Zero Point2D` typeclass instances.
- Writing `p.normSq_swap` is shorthand for `Point2D.normSq_swap p`.
-/

namespace LeanWorkshop.Part2

/-- A sample lattice point `(3, 4)` satisfying `0 ≤ 3 + 4`. -/
def samplePoint : Point2D :=
  ⟨3, 4, by decide⟩

#eval samplePoint.swap                    -- { x := 4, y := 3, ... }
#eval samplePoint.normSq                  -- 25
#eval (samplePoint + ⟨1, -1, by decide⟩)  -- { x := 4, y := 3, ... }

-- Using dot notation, typeclass instances, and `@[simp]` lemmas from `S2_Lemmas.lean`:
example (p : Point2D) : (p + 0).swap.swap = p := by
  simp

example (p : Point2D) : p.swap.normSq = p.normSq :=
  -- Dot notation applies `Point2D.normSq_swap` directly to `p : Point2D`!
  p.normSq_swap

/-!
---

## 4. Exercises

Replace each `sorry` below with a valid definition or proof using the `Point2D` API from
`S2_MiniProject`.
(Reference solutions are in `LeanWorkshop/Solutions/Part2_Organization/S3_ProjectStructure.lean`.)
-/

namespace Point2D

/-- **Exercise 1a:** Define diagonal shift `shiftDiag (n : ℕ) (p : Point2D)` that adds `(n : ℤ)`
to both coordinates of `p`.
Hint: Construct the result with `⟨p.x + n, p.y + n, by ...⟩` and prove the invariant using
`have := p.nonneg_sum; omega`. -/
def shiftDiag (n : ℕ) (p : Point2D) : Point2D :=
  sorry

/-- **Exercise 1b:** Prove that shifting `p` by `0` returns `p`.
Hint: Use `ext <;> simp [shiftDiag]`, noting that proof irrelevance handles `nonneg_sum`
automatically! -/
theorem shiftDiag_zero (p : Point2D) : shiftDiag 0 p = p := by
  sorry

/-- **Exercise 2:** Prove that componentwise addition `p + q` is commutative.
Hint: Start with `ext`, then simplify with `simp [Int.add_comm]`. -/
theorem add_comm_point (p q : Point2D) : p + q = q + p := by
  sorry

/-- **Exercise 3:** Prove that swapping coordinates distributes over `+`.
Hint: `ext <;> simp` uses the `@[simp]` lemmas from `S2_Lemmas.lean` on both coordinates! -/
theorem swap_add (p q : Point2D) : (p + q).swap = p.swap + q.swap := by
  sorry

end Point2D

end LeanWorkshop.Part2
