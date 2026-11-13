/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Use
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Prime.Basic

/-!
# Part 4.1: Statement Translation (Autoformalization)

Autoformalization translates informal mathematics (LaTeX or natural language) into formal Lean 4
definitions, theorem statements, and proofs—verified by Lean's trusted kernel.

The **hardest and most error-prone step** is not writing tactics; it is making sure the formal
statement accurately captures the *intended* mathematical meaning.

---

## 1. Semantic Trap 1: Truncated Subtraction on `ℕ`

In Lean, subtraction on `ℕ` is **truncated at zero**: `2 - 5 = 0`.
Therefore, a naive translation of:
> *"For natural numbers $a, b, c$, if $a - b = c$ then $a = b + c$."*
is **FALSE**! Counterexample: `a = 2, b = 5, c = 0` gives `2 - 5 = 0` (`rfl`), yet `2 ≠ 5 + 0`.

To formalize the true mathematical claim, either:
1. Add the missing domain guard `(h_le : b ≤ a)`, or
2. State it over `ℤ` or `ℝ`, where subtraction is true inverse addition.
-/

namespace LeanWorkshop.Part4

/-- Counterexample showing naive `ℕ` subtraction violates `a - b = c → a = b + c`. -/
example : ¬ (∀ a b c : ℕ, a - b = c → a = b + c) := by
  intro h
  have hfalse : (2 : ℕ) = 5 + 0 := h 2 5 0 rfl
  omega

/-- Corrected `ℕ` statement with explicit guard `h_le : b ≤ a`. -/
theorem nat_sub_eq_imp_eq_add {a b c : ℕ} (h_le : b ≤ a) (h : a - b = c) : a = b + c := by
  omega

/-- Over `ℤ`, subtraction is not truncated, so no order guard is needed. -/
theorem int_sub_eq_imp_eq_add {a b c : ℤ} (h : a - b = c) : a = b + c := by
  linarith

/-!
---

## 2. Semantic Trap 2: Integer Division Truncation

Similarly, `a / b` on `ℕ` and `ℤ` truncates toward zero: `(5 : ℕ) / 2 = 2`.
- Over `ℕ`, `a / 2 + a / 2 = a` is **false** for odd `a` (`5 / 2 + 5 / 2 = 4 ≠ 5`).
- Adding `(h_even : 2 ∣ a)` makes the `ℕ` statement true; casting `(a : ℝ)` makes real division
  exact for all `a`.
-/

/-- Real division with explicit coercion `(a : ℝ)` avoids integer truncation. -/
theorem nat_cast_half_add_half (a : ℕ) : (a : ℝ) / 2 + (a : ℝ) / 2 = (a : ℝ) := by
  ring

/-- Over `ℕ`, halving only reconstructs `a` when `2 ∣ a`. -/
theorem nat_half_add_half_of_even {a : ℕ} (h_even : 2 ∣ a) : a / 2 + a / 2 = a := by
  omega

/-!
---

## 3. Semantic Trap 3: Coercions (`↑`) & Implicit Domain Hypotheses

Informal prose frequently leaves domain assumptions implicit:
- *"Let $p$ be prime"* → `(hp : Nat.Prime p)`
- *"For any positive real $x$"* → `(hx : 0 < x)`
- *"Let $n \ge 1$ be an integer"* → `(n : ℤ) (hn : 1 ≤ n)`

When mixing `ℕ`, `ℤ`, and `ℝ` in one formula, Lean inserts coercions (`↑n`, printed in the
Infoview). Lemmas like `Nat.cast_le` (`(m : ℝ) ≤ (n : ℝ) ↔ m ≤ n`) bridge between `ℕ` inequalities
and `ℝ` inequalities.
-/

/-- Converting a natural number inequality `m ≤ n` into a real inequality `(m : ℝ) ≤ (n : ℝ)`. -/
theorem nat_le_to_real {m n : ℕ} (h : m ≤ n) : (m : ℝ) ≤ (n : ℝ) :=
  Nat.cast_le.mpr h

/-- Example making primality explicit: every prime is at least `2`. -/
theorem two_le_of_prime {p : ℕ} (hp : Nat.Prime p) : 2 ≤ p :=
  hp.two_le

/-!
---

## 4. Exercises

Each formal statement below has already been rescued from semantic traps. Complete the proofs!
(Reference solutions are in
`LeanWorkshop/Solutions/Part4_Autoformalization/S1_StatementTranslation.lean`.)
-/

/-- **Exercise 1:** Informally: *"If $b \le a$ in $\mathbb{N}$, then $(a - b) + b = a$."* -/
theorem ex1_nat_sub_cancel {a b : ℕ} (h : b ≤ a) : a - b + b = a := by
  sorry

/-- **Exercise 2:** Informally: *"The midpoint $(x+y)/2$ lies between $x$ and $y$ in $\mathbb{R}$."*
-/
theorem ex2_real_average {x y : ℝ} (h : x ≤ y) :
    x ≤ (x + y) / 2 ∧ (x + y) / 2 ≤ y := by
  sorry

/-- **Exercise 3:** Informally: *"The square of an odd integer $n = 2k + 1$ is odd."* -/
theorem ex3_odd_square {n : ℤ} (k : ℤ) (hn : n = 2 * k + 1) :
    ∃ m : ℤ, n ^ 2 = 2 * m + 1 := by
  sorry

/-- **Exercise 4:** Informally: *"If $m \le n$ in $\mathbb{N}$, then $m + 1 \le n + 1$ in
$\mathbb{R}$."* -/
theorem ex4_coercion_mono {m n : ℕ} (h : m ≤ n) : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
  sorry

end LeanWorkshop.Part4
