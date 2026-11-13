/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Data.Nat.Basic

/-!
# Part 2.1: Namespaces and Sections

As a mathematical development grows, we need tools to organize declarations, avoid naming
collisions, and factor out repeated parameters. Lean 4 provides **namespaces**, **sections**,
**variable declarations**, and **visibility modifiers** for this purpose.

---

## 1. Namespaces (`namespace ... end`, Hierarchical Names, Avoiding Collisions)

In a large library like Mathlib, dozens of types have operations named `add`, `map`, or `length`.
**Namespaces** group declarations under a hierarchical prefix (such as `Nat.add_comm` vs.
`Int.add_comm`).
-/

namespace LeanWorkshop.Part2

namespace Geometry

/-- Perimeter of a square with side length `s`. -/
def perimeter (s : ℕ) : ℕ :=
  4 * s

/-- Area of a square with side length `s`. -/
def area (s : ℕ) : ℕ :=
  s * s

-- Inside `namespace Geometry`, we can refer to `perimeter` and `area` without a prefix:
theorem perimeter_zero : perimeter 0 = 0 := by
  rfl

end Geometry

-- Outside `namespace Geometry`, we refer to declarations by their qualified names:
#eval Geometry.perimeter 5
#eval Geometry.area 5
#check Geometry.perimeter_zero

-- You can also place a single declaration directly into a namespace by prefixing its name:
/-- Squared diagonal of a square of side `s`, added directly to the `Geometry` namespace. -/
def Geometry.diagSq (s : ℕ) : ℕ :=
  2 * Geometry.area s

#eval Geometry.diagSq 5

/-!
---

## 2. Opening Namespaces (`open`, `open ... in`, Selective `open`, `open scoped`, `export`)

Writing full prefixes everywhere can become verbose. The `open` command brings names from a
namespace into the current scope:

- **`open Foo in <cmd>`**: Opens `Foo` *only* for the single following command or declaration.
  (Preferred in Mathlib when you only need a namespace briefly!)
- **`open Foo`**: Opens `Foo` for the remainder of the current `section`, `namespace`, or file.
- **`open Foo (a b)`**: Brings *only* `Foo.a` and `Foo.b` into scope.
- **`open Foo hiding c`**: Brings everything in `Foo` *except* `Foo.c` into scope.
- **`open scoped Foo`**: Activates *only* `scoped` notations/attributes from `Foo` without bringing
  all of its declaration names into unqualified scope.
- **`export Foo (a b)`**: Re-exports `Foo.a` and `Foo.b` as permanent aliases in the current
  namespace.
-/

-- `open ... in` scopes the open to a single command:
open Geometry in
#eval perimeter 7 + area 7

-- Selective open (`open Geometry (perimeter)`):
section SelectiveOpen

open Geometry (perimeter)

example : perimeter 3 = 12 := by
  rfl

end SelectiveOpen

-- Scoped notation (`scoped notation` + `open scoped`):
namespace DoubleNotation

/-- Scoped notation `⟪n⟫` for `2 * n`, active only when `DoubleNotation` is opened. -/
scoped notation "⟪" n "⟫" => 2 * n

end DoubleNotation

open scoped DoubleNotation in
example (n : ℕ) : ⟪n⟫ = n + n := by
  exact Nat.two_mul n

/-!
---

## 3. Sections and Variable Scoping (`section ... end` and `variable`)

When several theorems share the same parameters or typeclass assumptions, declare them once with
`variable` inside a `section ... end` block:

- **`section Name ... end Name`** bounds the lifetime of `variable`, `open`, and `set_option`
  commands **without** adding a namespace prefix to declaration names.
- **Automatic inclusion:** Lean only inserts a `variable` into a `def` or `theorem` if that
  variable (or another variable whose type depends on it) is actually referenced!
-/

section SharedVariables

variable (x y z : ℕ) (f : ℕ → ℕ)

-- Only `x` and `y` appear here, so `add_comm_xy` takes only `(x y : ℕ)`—not `z` or `f`!
/-- Specialization of addition commutativity using section variables `x` and `y`. -/
theorem add_comm_xy : x + y = y + x := by
  exact Nat.add_comm x y

-- Only `x` and `f` appear here:
/-- Applying `f` to `x + 0` yields `f x`. -/
theorem apply_add_zero : f (x + 0) = f x := by
  rfl

end SharedVariables

-- Outside `section SharedVariables`, inspect the generated signatures:
#check add_comm_xy    -- (x y : ℕ) → x + y = y + x
#check apply_add_zero -- (x : ℕ) → (f : ℕ → ℕ) → f (x + 0) = f x

/-!
---

## 4. Visibility Modifiers (`protected` and `private`)

- **`protected`**: A `protected` declaration inside `namespace Foo` **must still be referred to as
  `Foo.bar`** (or via dot notation) even after `open Foo`. Mathlib uses `protected` extensively
  (e.g. `protected theorem Nat.add_comm`) so that `open Nat` does not shadow generic lemmas like
  `add_comm`.
- **`private`**: A `private` declaration is only visible inside the current `.lean` file—useful for
  internal helper lemmas.
-/

namespace Counter

/-- Internal step size, invisible outside this file. -/
private def step : ℕ :=
  1

/-- Public function incrementing `n` by `step`. -/
def tick (n : ℕ) : ℕ :=
  n + step

/-- Protected theorem: still requires `Counter.tick_eq` even when `Counter` is opened. -/
protected theorem tick_eq (n : ℕ) : tick n = n + 1 := by
  rfl

end Counter

open Counter in
example (n : ℕ) : tick n = n + 1 := by
  -- `tick` is available unqualified, while `Counter.tick_eq` keeps its prefix:
  exact Counter.tick_eq n

/-!
---

## 5. Exercises

Replace each `sorry` below with a valid implementation or proof.
(Reference solutions are in
`LeanWorkshop/Solutions/Part2_Organization/S1_NamespacesAndSections.lean`.)
-/

namespace TempConv

/-- **Exercise 1a:** Define integer temperature conversion from Celsius to Kelvin (`c + 273`). -/
def toKelvin (c : ℕ) : ℕ :=
  sorry

/-- **Exercise 1b:** Prove that `0` degrees Celsius is `273` Kelvin. -/
theorem toKelvin_zero : toKelvin 0 = 273 := by
  sorry

end TempConv

/-- **Exercise 2:** Use `open Geometry in` (or qualified names) to prove that a square of side `3`
has `area 3 + perimeter 3 = 21`. -/
theorem ex2_square_three : Geometry.area 3 + Geometry.perimeter 3 = 21 := by
  sorry

section ExerciseSection

variable (a b c : ℕ)

/-- **Exercise 3:** Using the section variables `a`, `b`, and `c`, prove
`(a + b) + c = (a + c) + b`. Hint: Look at `Nat.add_right_comm`. -/
theorem ex3_add_rearrange : a + b + c = a + c + b := by
  sorry

end ExerciseSection

end LeanWorkshop.Part2
