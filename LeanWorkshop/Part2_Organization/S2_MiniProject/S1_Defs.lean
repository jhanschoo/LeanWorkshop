/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Data.Int.Basic

/-!
# Part 2.2a: MiniProject — Definitions (`Point2D`)

In well-structured Lean projects (including Mathlib), core **data structures and definitions** are
placed in dedicated `Defs.lean` files, separate from the larger body of theorems (`Lemmas.lean`).

This module defines `Point2D`—a point on the 2D integer lattice `ℤ × ℤ`—along with basic operations
in the `Point2D` namespace.
-/

namespace LeanWorkshop.Part2

/-- A point `(x, y)` on the two-dimensional integer lattice `ℤ × ℤ`.
The `@[ext]` attribute automatically generates the extensionality theorem `Point2D.ext`, which says
two points are equal if and only if their `x` and `y` coordinates are equal. -/
@[ext]
structure Point2D where
  /-- Horizontal coordinate. -/
  x : ℤ
  /-- Vertical coordinate. -/
  y : ℤ
  deriving DecidableEq, Repr

namespace Point2D

/-- The origin `(0, 0)` of the integer lattice. -/
def origin : Point2D :=
  ⟨0, 0⟩

/-- Componentwise addition of two lattice points. -/
def add (p q : Point2D) : Point2D :=
  ⟨p.x + q.x, p.y + q.y⟩

/-- Reflection across the line `y = x` (swapping `x` and `y` coordinates). -/
def swap (p : Point2D) : Point2D :=
  ⟨p.y, p.x⟩

/-- Squared Euclidean norm `x² + y²` of a lattice point. -/
def normSq (p : Point2D) : ℤ :=
  p.x * p.x + p.y * p.y

end Point2D

end LeanWorkshop.Part2
