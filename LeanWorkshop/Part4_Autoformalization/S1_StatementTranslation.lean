/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Use
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Part 4.1: Statement Translation (Autoformalization)

Autoformalization translates informal mathematics (LaTeX or natural language) into formal Lean 4
definitions, theorem statements, and proofs—verified by Lean's trusted kernel.

An **error-prone step** is in making sure the formal
statement accurately captures the *intended* mathematical meaning. Subtle semantic differences
between informal conventions and Mathlib definitions occur across every area of mathematics.
We exhibit some **examples** below.

---

## Example 1: Truncated Subtraction on `ℕ`

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

## Example 2: Integer Division Truncation

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

## Example 3: Coercions (`↑`) & Implicit Domain Hypotheses

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

## Example 4: Definition Alignment Beyond Arithmetic (`Monotone` vs. `StrictMono`)

Semantic drift also comes from choosing a Mathlib definition that is weaker (or stronger) than the
informal term. In informal analysis, *"increasing"* often means $x < y \implies f(x) < f(y)$
(which implies injectivity), whereas Mathlib's `Monotone` only requires $x \le y \implies f(x) \le
f(y)$ and holds for constant functions! Whenever you mean strictly increasing, use `StrictMono`.
-/

/-- Constant functions satisfy `Monotone`, so `Monotone` does not imply injectivity. -/
example : ¬ (∀ f : ℝ → ℝ, Monotone f → Function.Injective f) := by
  intro h
  have h_inj : Function.Injective (fun _ : ℝ ↦ (0 : ℝ)) := h _ monotone_const
  have h_eq : (0 : ℝ) = 1 := h_inj rfl
  norm_num at h_eq

/-- Under `StrictMono`, functions are injective (`hf.injective`). -/
theorem strictMono_injective {f : ℝ → ℝ} (hf : StrictMono f) : Function.Injective f :=
  hf.injective

/-!
---

## 5. Discovering and Auditing Semantic Misalignments in Mathlib

Two of the misalignments above come
from **totalization** and **boundary conventions**. Because every function in Lean must be total,
operations that are informally partial (undefined on certain inputs) are extended in Mathlib with a
convenient default ("junk") value outside their natural domain:
- `a / 0 = 0` on `ℕ`, `ℤ`, `ℚ`, `ℝ`
- `a - b = 0` on `ℕ` when `a ≤ b`
- `Real.sqrt x = 0` for `x < 0`
- `deriv f x = 0` when `f` is not differentiable at `x`
- `sSup s` / `sInf s` return a default value when `s : Set ℝ` is empty or unbounded

To check whether an unfamiliar Mathlib definition might be misaligned with your informal intent:

1. **Jump to the definition & read "Implementation notes" (`F12` / hover / `#print`):**
   Press `F12` on any symbol in VS Code to open its Mathlib file. Module headers and docstrings
   usually spell out edge-case conventions and why a totalization choice was made.
2. **Inspect the hypotheses of surrounding API lemmas (`#check`):**
   Look at the theorems proved right next to the definition. Extra hypotheses—such as `b ≤ a` in
   `Nat.sub_add_cancel`, `y ≠ 0` in `div_mul_cancel₀`, `0 ≤ x` in `Real.sq_sqrt`, or
   `DifferentiableAt ℝ f x` in derivative rules—reveal the exact domain where the usual
   mathematical behavior holds.
3. **Probe degenerate and out-of-domain inputs (`#eval`, `norm_num`, `simp`):**
   Evaluate or simplify the expression on `0`, `1`, negative numbers, `∅`, or discontinuous
   functions to see directly what the definition returns outside the intended domain.
4. **Try to refute your statement on boundary cases before proving it:**
   Before investing effort in a proof of `∀ x, P x`, check if `x = 0`, `x < 0`, or `s = ∅` gives a
   quick counterexample (`¬ ∀ x, P x`). You can also use property-based testing (`plausible`) or
   ask an LLM to look for degenerate counterexamples.
5. **Prove a sanity-check corollary (guard against vacuity):**
   Even if a statement compiles and is provable, missing or contradictory hypotheses can make it
   vacuously true. Specialize your theorem to a concrete non-trivial case to confirm it actually
   says something meaningful.
-/

-- Because `(x : ℝ) / 0 = 0` by totalization, `x / y * y = x` fails at `y = 0`:
example : ¬ (∀ x y : ℝ, x / y * y = x) := by
  intro h
  have h1 : (1 : ℝ) / 0 * 0 = 1 := h 1 0
  linarith

-- Inspecting Mathlib's cancellation lemma reveals the required domain guard `y ≠ 0`:
#check div_mul_cancel₀

/-!
---

## 6. Exercises: Auditing & Repairing Statement Translations

Practice refuting naive translations, inspecting Mathlib domain guards (`#check`), and running
sanity instantiations. (Reference solutions are in
`LeanWorkshop/Solutions/Part4_Autoformalization/S1_StatementTranslation.lean`.)
-/

/-- **Exercise 1a (Refute):** Naive `ℕ` translation of *"$(a - b) + b = a$ for all naturals"*
is false! Exhibit a counterexample. -/
theorem ex1a_refute_naive_sub : ¬ (∀ a b : ℕ, a - b + b = a) := by
  sorry

/-- **Exercise 1b (Repair):** With the domain guard `b ≤ a`, prove the repaired identity. -/
theorem ex1b_nat_sub_cancel {a b : ℕ} (h : b ≤ a) : a - b + b = a := by
  sorry

/-- **Exercise 2a (Refute):** Naive `ℝ` translation of *"$x / y = z \implies x = z \cdot y$"* is
false because `(x : ℝ) / 0 = 0`! Exhibit a counterexample. -/
theorem ex2a_refute_naive_div : ¬ (∀ x y z : ℝ, x / y = z → x = z * y) := by
  sorry

/-- **Exercise 2b (Discover guard & prove):** Repair Exercise 2a with `y ≠ 0` and prove it
(hint: check `#check div_mul_cancel₀`). -/
theorem ex2b_div_eq_mul {x y z : ℝ} (hy : y ≠ 0) (h : x / y = z) : x = z * y := by
  sorry

/-- **Exercise 2c (Sanity instantiation):** Instantiate `ex2b_div_eq_mul` on `x = 6, y = 3, z = 2`
to confirm the hypotheses are non-vacuous. -/
theorem ex2c_div_sanity : (6 : ℝ) = 2 * 3 := by
  sorry

/-- **Exercise 3 (Definition alignment):** Using `StrictMono`, prove that `f x = f y → x = y`.
Notice this would be false if `StrictMono` were mistakenly translated as `Monotone`! -/
theorem ex3_strictMono_eq_imp_eq {f : ℝ → ℝ} (hf : StrictMono f) {x y : ℝ}
    (h : f x = f y) : x = y := by
  sorry

end LeanWorkshop.Part4
