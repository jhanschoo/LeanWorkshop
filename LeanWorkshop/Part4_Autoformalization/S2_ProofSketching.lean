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

/-!
# Part 4.2: Proof Sketching (Draft, Sketch, Prove)

When formalizing non-trivial proofs—either manually or with an LLM—do **not** try to generate
the entire tactic script in one shot. Use the **Draft, Sketch, Prove (DSP)** workflow:

1. **Draft:** Write a clear, step-by-step informal mathematical argument.
2. **Sketch:** Translate each intermediate claim into a `have h_step : ... := by sorry` block,
   and check that the *final conclusion compiles* from those `have` steps alone!
3. **Prove:** Fill in each `sorry` subgoal independently (using `ring`, `linarith`, `positivity`,
   `omega`, or targeted searches).

Because Lean typechecks each `have` independently, a failed subgoal never breaks the overall
structure of your proof!

---

## 1. Walkthrough 1: AM-GM on Two Real Numbers

**Informal Draft:**
> To prove $2ab \le a^2 + b^2$, note that $(a - b)^2 \ge 0$ because any real square is
> nonnegative. Expanding gives $(a - b)^2 = a^2 - 2ab + b^2 \ge 0$, so $2ab \le a^2 + b^2$.

**Step 2 (Sketch — notice the outer proof already compiles with `linarith`!):**
-/

namespace LeanWorkshop.Part4

/-- Verified proof sketch: only the inner `have` steps carry `sorry`. -/
theorem two_mul_le_sq_add_sq_sketch (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h_sq : 0 ≤ (a - b) ^ 2 := by sorry
  have h_expand : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by sorry
  linarith

/-- Step 3 (Prove): discharge each `sorry` independently. -/
theorem two_mul_le_sq_add_sq (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h_sq : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  have h_expand : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by ring
  linarith

/-!
---

## 2. Walkthrough 2: Isolating Algebra from Positivity via `have` and `calc`

Separating algebraic identities (`ring`) from sign reasoning (`positivity` / `linarith`) keeps
each subgoal within the decidable fragment of a single Mathlib tactic:
-/

/-- Completing the square: `x ^ 2 + 4 * x + 7 ≥ 3` for all `x : ℝ`. -/
theorem quad_lower_bound (x : ℝ) : 3 ≤ x ^ 2 + 4 * x + 7 := by
  have h_complete : x ^ 2 + 4 * x + 7 = (x + 2) ^ 2 + 3 := by
    ring
  have h_sq : 0 ≤ (x + 2) ^ 2 := by
    positivity
  linarith

/-!
---

## 3. Exercises

In each exercise below, the outer proof skeleton is already verified! Replace each inner `sorry`
inside the `have` blocks with a short tactic or proof term.
(Reference solutions are in
`LeanWorkshop/Solutions/Part4_Autoformalization/S2_ProofSketching.lean`.)
-/

/-- **Exercise 1:** Symmetric 3-variable inequality via sum of squares. -/
theorem ex1_sum_of_squares_bound (a b c : ℝ) :
    a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have h1 : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by
    sorry
  have h2 :
      (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 =
        2 * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)) := by
    sorry
  linarith

/-- **Exercise 2:** Interval bound via separate `x` and `y` bounds. -/
theorem ex2_abs_bound_sketch {x y : ℝ} (hx : -2 ≤ x ∧ x ≤ 2) (hy : -3 ≤ y ∧ y ≤ 3) :
    2 * x - y ≤ 7 := by
  have hx_upper : 2 * x ≤ 4 := by
    sorry
  have hy_lower : -3 ≤ y := by
    sorry
  linarith

/-- **Exercise 3:** Cubic polynomial nonnegativity on `[1, ∞)` by factoring. -/
theorem ex3_cubic_factor_sketch {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ x ^ 3 - x ^ 2 - x + 1 := by
  have h_factor : x ^ 3 - x ^ 2 - x + 1 = (x - 1) ^ 2 * (x + 1) := by
    sorry
  have h_sq : 0 ≤ (x - 1) ^ 2 := by
    sorry
  have h_pos : 0 ≤ x + 1 := by
    sorry
  rw [h_factor]
  exact mul_nonneg h_sq h_pos

end LeanWorkshop.Part4
