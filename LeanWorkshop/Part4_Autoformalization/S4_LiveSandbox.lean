/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Basic

/-!
# Part 4.4: Live Autoformalization Sandbox

This file is designed for **Mode 2 (Live Demo)** alongside `S5_WorkflowGuide.md`.
Each challenge gives an informal mathematical problem together with a compiled Lean 4 `theorem`
signature (`:= by sorry`). Try solving them with an AI assistant or interactively in the Infoview!

(Complete reference solutions live in
`LeanWorkshop/Solutions/Part4_Autoformalization/S4_LiveSandbox.lean`.)
-/

namespace LeanWorkshop.Part4

/-- **Challenge 1 (Warmup — Algebraic Identity):**
Informal statement:
*"For any integer $n$, the difference of consecutive squares $(n + 1)^2 - n^2$ equals $2n + 1$."*
-/
theorem challenge1_consecutive_squares (n : ℤ) : (n + 1) ^ 2 - n ^ 2 = 2 * n + 1 := by
  sorry

/-- **Challenge 2 (Intermediate — Convex Combination Bounds):**
Informal statement:
*"If $a \le b$ are real numbers and $w \in [0, 1]$, then the weighted average $(1 - w)a + wb$
lies between $a$ and $b$."*
-/
theorem challenge2_weighted_average {a b w : ℝ}
    (hab : a ≤ b) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    a ≤ (1 - w) * a + w * b ∧ (1 - w) * a + w * b ≤ b := by
  sorry

/-- Recursive sum `sumUpTo n = 0 + 1 + ⋯ + n`. -/
def sumUpTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumUpTo n + (n + 1)

/-- **Challenge 3 (Intermediate — Induction):**
Informal statement:
*"For every natural number $n$, twice the sum $0 + 1 + \cdots + n$ equals $n(n + 1)$."*
-/
theorem challenge3_gauss_sum (n : ℕ) : 2 * sumUpTo n = n * (n + 1) := by
  sorry

/-- **Challenge 4 (Advanced — 2D Cauchy-Schwarz via Draft, Sketch, Prove):**
Informal statement:
*"For all real numbers $a_1, a_2, b_1, b_2$, we have
$(a_1 b_1 + a_2 b_2)^2 \le (a_1^2 + a_2^2)(b_1^2 + b_2^2)$."*

Hint: Use Lagrange's identity
$(a_1^2 + a_2^2)(b_1^2 + b_2^2) - (a_1 b_1 + a_2 b_2)^2 = (a_1 b_2 - a_2 b_1)^2$.
-/
theorem challenge4_cauchy_schwarz_2d (a1 a2 b1 b2 : ℝ) :
    (a1 * b1 + a2 * b2) ^ 2 ≤ (a1 ^ 2 + a2 ^ 2) * (b1 ^ 2 + b2 ^ 2) := by
  sorry

end LeanWorkshop.Part4
