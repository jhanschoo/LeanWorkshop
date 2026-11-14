/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Data.Int.Basic

/-!
# Part 2.2a: MiniProject — Bundled Structures, Constructors, Annotations & Instances

In well-structured Lean projects (including Mathlib), core **data structures and definitions** live
in dedicated `Defs.lean` files, separate from the larger body of theorems (`Lemmas.lean`).

This module defines `Point2D`—a point on the 2D integer lattice `ℤ × ℤ` satisfying the half-plane
invariant `0 ≤ x + y`—to showcase five foundational Lean 4 concepts:
1. **Bundled structures** (data fields + `Prop` invariants).
2. **Annotations** (`@[ext]`, `deriving`, and `@[simp]` in `S2_Lemmas.lean`).
3. **Anonymous constructor syntax (`⟨...⟩`)** vs. named fields `{ ... }`.
4. **Proof irrelevance** on `Prop` fields and `@[ext]`.
5. **Typeclass instantiation** (`instance` for `Zero`, `Add`, and `Inhabited`).

---

## 1. Bundled Structures and Annotations (`@[ext]`, `deriving`)

A `structure` in Lean can bundle **data** (`x, y : ℤ`) together with **properties** that every
valid value must carry (`nonneg_sum : 0 ≤ x + y`).

- The **`@[ext]` annotation** is an *attribute* telling Lean to auto-generate the extensionality
  lemma `Point2D.ext`, which turns `p = q` into fieldwise equalities.
- The **`deriving DecidableEq, Repr`** clause asks Lean to automatically synthesize equality
  decision (`=`) and printing (`#eval`) instances for `Point2D`.
-/

namespace LeanWorkshop.Part2

/-- A point `(x, y)` on the integer lattice `ℤ × ℤ` satisfying `0 ≤ x + y`. -/
@[ext]
structure Point2D where
  /-- Horizontal coordinate. -/
  x : ℤ
  /-- Vertical coordinate. -/
  y : ℤ
  /-- Invariant: the point lies in the half-plane `0 ≤ x + y`. -/
  nonneg_sum : 0 ≤ x + y
  deriving DecidableEq, Repr

/-!
---

## 2. Anonymous Constructor Syntax (`⟨...⟩`) vs. Named Fields

There are three equivalent ways to build a value of a single-constructor `structure`:
1. **Named field syntax:** `{ x := 0, y := 0, nonneg_sum := by decide }`
2. **Explicit constructor:** `Point2D.mk 0 0 (by decide)`
3. **Anonymous constructor syntax (`⟨...⟩`):** `⟨0, 0, by decide⟩` (type `\<` and `\>`)

Lean accepts `⟨...⟩` whenever it already knows the target single-constructor type (for example,
from a function return type `: Point2D` or an explicit annotation `(⟨3, 4, by decide⟩ : Point2D)`).
-/

namespace Point2D

/-- The origin `(0, 0)`, constructed with named fields `{ ... }`. -/
def origin : Point2D :=
  { x := 0, y := 0, nonneg_sum := by decide }

/-- Same origin written with the explicit `Point2D.mk` constructor. -/
def originMk : Point2D :=
  Point2D.mk 0 0 (by decide)

/-- Same origin written with anonymous constructor syntax `⟨...⟩`. -/
def originAnon : Point2D :=
  ⟨0, 0, by decide⟩

/-- Componentwise addition, preserving `0 ≤ x + y` via `omega`. -/
def add (p q : Point2D) : Point2D :=
  ⟨p.x + q.x, p.y + q.y, by have := p.nonneg_sum; have := q.nonneg_sum; omega⟩

/-- Reflection across `y = x` (swapping `x` and `y` coordinates). -/
def swap (p : Point2D) : Point2D :=
  ⟨p.y, p.x, by have := p.nonneg_sum; omega⟩

/-- Squared Euclidean norm `x² + y²` of a lattice point. -/
def normSq (p : Point2D) : ℤ :=
  p.x * p.x + p.y * p.y

/-!
---

## 3. Structures and Proof Irrelevance

In Lean's type theory, **every two proofs `h₁ h₂ : P` of a proposition `P : Prop` are
definitionally equal** (`h₁ = h₂` holds by `rfl`). This principle is called **proof irrelevance**.

Because `nonneg_sum` has type `0 ≤ x + y : Prop`:
1. Two `Point2D` values with the same `.x` and `.y` coordinates are **definitionally equal** even if
   their invariant fields were constructed by completely different proof scripts!
2. When `@[ext]` generates `Point2D.ext`, it only asks you to prove `p.x = q.x` and `p.y = q.y`—the
   `nonneg_sum` proof field is discharged automatically by proof irrelevance!
-/

-- Different proof methods (`decide` vs `omega`) yield the exact same `Point2D` up to `rfl`!
example : (⟨3, 4, by decide⟩ : Point2D) = ⟨3, 4, by omega⟩ :=
  rfl

-- Notice `Point2D.ext` only mentions `p.x = q.x` and `p.y = q.y`:
#check @Point2D.ext

/-!
---

## 4. Typeclass Instantiation (`instance`)

A **typeclass** (such as `Zero`, `Add`, or `Inhabited`) is a `structure` marked `@[class]` whose
values Lean searches for automatically inside `[ ... ]` brackets. Using **`instance`**, we teach
Lean how to use `0` and `+` on `Point2D`:

- `where` style lists each class field by name (great for readability).
- `:= ⟨...⟩` uses anonymous constructor syntax on single-field classes like `Add` and `Inhabited`.
-/

/-- Register `0 : Point2D` via the `Zero` typeclass (`where` syntax). -/
instance : Zero Point2D where
  zero := origin

/-- Register `p + q` via the `Add` typeclass (`⟨...⟩` anonymous constructor syntax). -/
instance : Add Point2D :=
  ⟨add⟩

/-- Register a default inhabited element via `Inhabited`. -/
instance : Inhabited Point2D :=
  ⟨0⟩

#eval (0 : Point2D) + ⟨3, 4, by decide⟩

end Point2D

end LeanWorkshop.Part2
