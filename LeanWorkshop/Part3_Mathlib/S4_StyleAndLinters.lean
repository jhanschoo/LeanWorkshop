/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linter.Lint
import Mathlib.Data.Nat.Basic

/-!
# Part 3.4: Mathlib Style Guide and Linters

Consistent style makes Mathlib readable across thousands of contributors and allows automated
linters to catch subtle bugs (like typos in implicit variable names or broken `@[simp]` rules)
before code is ever merged.

---

## 1. Naming Conventions

| Kind | Style | Example |
| :--- | :--- | :--- |
| Terms of `Prop` (theorems, lemmas, proof variables) | `snake_case` | `add_comm`, `le_of_lt` |
| Types, structures, classes, inductive types | `UpperCamelCase` | `Point2D`, `RingHom` |
| Data definitions & functions returning values | `lowerCamelCase` | `doubleList`, `normSq` |

Rule of thumb: **capitalize Types (`Type*`), camelCase functions, `snake_case` proofs!**
-/

namespace LeanWorkshop.Part3

/-- An `UpperCamelCase` structure wrapping a natural number bound. -/
structure UpperBound where
  /-- The stored upper bound value. -/
  val : ℕ

/-- A `lowerCamelCase` function returning a value. -/
def doubleBound (b : UpperBound) : ℕ :=
  2 * b.val

/-- A `snake_case` theorem stating a `Prop`. -/
theorem doubleBound_even_mod (b : UpperBound) : doubleBound b % 2 = 0 := by
  dsimp [doubleBound]
  omega

/-!
---

## 2. Formatting & Syntax Standards

Mathlib enforces these syntactic rules via automated style linters:

1. **Line length ≤ 100 characters:** Keep every code and comment line at 100 columns or fewer
   (`linter.style.longLine`).
2. **2-space indentation:** Keep `:= by` on the declaration header line (or indented if wrapped),
   and indent tactic lines by 2 spaces.
3. **Middle dot `·` (`\cdot`) for subgoal bullets:** Never use ASCII `.` for tactic focusing
   (`linter.style.cdot`).
4. **Unicode lambda `fun x ↦ ...` (`\mapsto`):** Never use `λ` (`linter.style.lambdaSyntax`).
5. **`Type*` for universe polymorphism:** Prefer `{α : Type*}` over `{α : Type _}`.
-/

/-- Example showing Mathlib-compliant `fun x ↦ ...` and `·` bullet syntax. -/
theorem clean_style_demo (P Q : Prop) (hp : P) (hq : Q) :
    P ∧ Q ∧ (fun n : ℕ ↦ n) 0 = 0 := by
  refine ⟨hp, ?_, ?_⟩
  · exact hq
  · rfl

/-!
---

## 3. Documentation (`/-! ... -/` vs `/-- ... -/`)

- `/-! ... -/` is a **module docstring** or section heading placed immediately after `import`
  lines or between sections.
- `/-- ... -/` is a **declaration docstring** attached directly to the `def`, `theorem`,
  `structure`, or `class` below it (visible on hover in VS Code and in Mathlib4 Docs).

Never place a `/-- ... -/` docstring before `open ... in` or `namespace ...`—put attributes and
scoped `open ... in` modifiers *before* the docstring, or attach the docstring directly to the
declaration itself.

---

## 4. Project Configuration & `#lint`

Look at `lakefile.toml` in the root of this repository:

- `relaxedAutoImplicit = false`: Prevents accidental typos (like writing `n + m` when only `n`
  was declared) from silently turning `m` into an implicit variable!
- `weak.linter.mathlibStandardSet = true`: Runs Mathlib's style and correctness linters (`header`,
  `longLine`, `cdot`, `lambdaSyntax`, `unusedVariables`, `simpNF`, …) on every `lake build`.
- `import Mathlib.Tactic` is disallowed in Mathlib files: import only the specific tactic modules
  you need (e.g. `Mathlib.Tactic.Ring`, `Mathlib.Tactic.Linarith`).

You can also run `#lint` interactively inside a file to check docstrings, unused arguments, and
`simp` normal form rules on declarations above it:
-/

-- Run Mathlib linters on the declarations above:
#lint

/-!
---

## 5. Exercises

Complete each exercise while keeping `lake build` free of all style and linter warnings!
(Reference solutions are in `LeanWorkshop/Solutions/Part3_Mathlib/S4_StyleAndLinters.lean`.)
-/

/-- **Exercise 1:** Prove functional equality using `funext` and clean lambda syntax. -/
theorem ex1_clean_lambda : (fun n : ℕ ↦ n + 0) = (fun n : ℕ ↦ n) := by
  sorry

/-- **Exercise 2:** Prove a conjunction using `constructor` and `·` bullets (never `.`). -/
theorem ex2_clean_bullets (P Q R : Prop) (hpq : P → Q) (hpr : P → R) (hp : P) : Q ∧ R := by
  sorry

/-- **Exercise 3:** Prove universe-polymorphic identity `{α : Type*}`. -/
theorem ex3_polymorphic_id {α : Type*} (x : α) : id x = x := by
  sorry

end LeanWorkshop.Part3
