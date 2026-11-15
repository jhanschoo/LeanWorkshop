/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Order.Monotone.Basic
import Mathlib.Basic.Real.Basic

/-!
# Part 4.3: Steering AI Agents & Guarding Against Modern Failure Modes

Modern AI agents run **with the Lean compiler in the loop** (`lake env lean`, LSP diagnostics,
and MCP search tools). Shallow syntactic bugs—hallucinated lemma names, legacy Lean 3 syntax, or
flipped `rw` directions—are normally fixed by the agent in seconds before you ever inspect a file.

The real failure modes today are **semantic and architectural**: code that compiles cleanly with
exit code `0`, yet silently proves the wrong theorem, isolates itself from Mathlib, loops on a
false subgoal, or leaves behind brittle spaghetti scripts.

---

## 1. Failure Mode 1: Specification Gaming & Silent Statement Drift

When told *"make the file compile with zero `sorry`s,"* an agent may subtly alter a `def` or
`theorem` signature—weakening the conclusion, adding contradictory hypotheses so the theorem holds
vacuously, or slipping in `axiom` / `sorryAx`.

**How to guard against it:**
1. **Lock target signatures:** Check `git diff` to ensure `def` and `theorem` headers did not
   drift while proofs were being repaired.
2. **Audit axioms (`#print axioms`):** Verify that only standard axioms (`propext`,
   `Classical.choice`, `Quot.sound`) appear—never `sorryAx` or custom `axiom`s.
3. **Write a concrete instantiation test:** Apply the proved theorem to specific numbers; any
   contradictory hypothesis immediately causes the test to fail.
-/

namespace LeanWorkshop.Part4

/-- Realistic vacuity trap: an agent drops the `x + 1 ≤ y` guard when translating
"if `x + 1 ≤ y` then `f x + 1 ≤ f y`". Setting `x = 0, y = 0` yields `f 0 + 1 ≤ f 0`,
so `linarith` "proves" `f 0 = f 1` vacuously with zero compiler warnings! -/
theorem step_bound_vacuous (f : ℝ → ℝ) (h : ∀ x y : ℝ, f x + 1 ≤ f y) : f 0 = f 1 := by
  linarith [h 0 0]

/-- Non-vacuous target theorem: `2 * x ≤ x ^ 2` whenever `2 ≤ x`. -/
theorem two_mul_le_sq {x : ℝ} (hx : 2 ≤ x) : 2 * x ≤ x ^ 2 := by
  have h : 0 ≤ x * (x - 2) := mul_nonneg (by linarith) (by linarith)
  linarith

-- Audit 1: confirm no `sorryAx` or hidden custom axioms were introduced:
#print axioms two_mul_le_sq

-- Audit 2: instantiate the theorem on a concrete input (`x = 3`) to rule out vacuity:
example : (2 : ℝ) * 3 ≤ 3 ^ 2 :=
  two_mul_le_sq (by norm_num)

/-!
---

## 2. Failure Mode 2: Creating "API Islands" Instead of Using Mathlib

Agents frequently reinvent definitions from scratch—for example, writing
`def MyMonotone (f : ℝ → ℝ) : Prop := ∀ x y, x ≤ y → f x ≤ f y` instead of using Mathlib's
`Monotone`. Although the file compiles, every downstream proof becomes an isolated "API island"
cut off from Mathlib's `Monotone.add`, `Monotone.comp`, and `@[simp]` / `@[fun_prop]` lemmas.

- **Fix:** Search Mathlib first (`Loogle`, `LeanSearch`, `LeanExplore`, or local grep) before
  defining standard concepts, and bridge any necessary domain wrappers via `@[simp]` lemmas.
-/

/-- Using Mathlib's `Monotone` gives composition and addition in one line. -/
example {f g : ℝ → ℝ} (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun x ↦ f (g x) + g x) :=
  (hf.comp hg).add hg

/-!
---

## 3. Failure Mode 3: Tactic Loops on False Intermediate Subgoals

An agent will often outline a plausible-sounding `have` claim that is actually **false**—for
example, asserting `x ≤ x ^ 2` for an arbitrary `x : ℝ`—and then burn dozens of turns trying
`linarith`, `nlinarith`, and `grind` on an unprovable subgoal.

- **Fix:** When an intermediate `have` resists automation, immediately test it on `0`, `1 / 2`, or
  negative inputs (`¬ ∀ x, ...`) and revise the subgoal statement instead of forcing tactics.
-/

-- Refuting the false intermediate subgoal `∀ x : ℝ, x ≤ x ^ 2` at `x = 1 / 2`:
example : ¬ (∀ x : ℝ, x ≤ x ^ 2) := by
  intro h
  have h_half : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ 2 := h (1 / 2)
  norm_num at h_half

/-- Revising the subgoal to completing the square (`0 ≤ (x - 1 / 2) ^ 2`) solves the bound. -/
theorem poly_pos_quarter (x : ℝ) : 3 / 4 ≤ x ^ 2 - x + 1 := by
  have h_sq : 0 ≤ (x - 1 / 2) ^ 2 := sq_nonneg (x - 1 / 2)
  linarith

/-!
---

## 4. Failure Mode 4: Brittle "Spaghetti Proofs" vs. Modular Structure

Even when a theorem statement is right, agents can emit sprawling tactic blocks full of
manual `have` chains, non-terminal `simp` calls, and raw `rw` chains that break on Mathlib bumps.

- **Fix:**
  - Extract reusable facts into standalone `lemma`s inside a `namespace`/`section` (as in 4.2).
  - Replace non-terminal `simp` with `simp only [...]` (via `simp?`).
  - Prefer `calc`, `gcongr`, `fun_prop`, `grind`, and `positivity` over fragile manual rewrites.
-/

/-- Verbose, brittle proof emitted by an unguided agent: manual factoring and `rw` chains. -/
theorem quad_mono_spaghetti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    2 * a ^ 2 + a ≤ 2 * b ^ 2 + b := by
  have hb : 0 ≤ b := le_trans ha hab
  have h_sub : 0 ≤ b - a := sub_nonneg.mpr hab
  have h_sum : 0 ≤ b + a := add_nonneg hb ha
  have h_mul : 0 ≤ (b - a) * (b + a) := mul_nonneg h_sub h_sum
  have h_sq : a ^ 2 ≤ b ^ 2 := by
    have h_diff : b ^ 2 - a ^ 2 = (b - a) * (b + a) := by ring
    linarith
  have h_two : 2 * a ^ 2 ≤ 2 * b ^ 2 := by
    rw [← sub_nonneg]
    have h_fac : 2 * b ^ 2 - 2 * a ^ 2 = 2 * (b ^ 2 - a ^ 2) := by ring
    rw [h_fac]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr h_sq)
  exact add_le_add h_two hab

/-- Modular refactored proof: `gcongr` handles powers and linear combinations cleanly. -/
theorem quad_mono_clean {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    2 * a ^ 2 + a ≤ 2 * b ^ 2 + b := by
  gcongr

/-!
---

## 5. Exercises

(Reference solutions are in `LeanWorkshop/Solutions/Part4_Autoformalization/S3_ErrorRecovery.lean`.)
-/

/-- **Exercise 1 (False Subgoal Recovery):** An agent tried to prove `-1 / 4 ≤ x ^ 2 + x` by
writing `have h_bad : 0 ≤ x ^ 2 + x := by sorry` (which is false at `x = -1 / 2`!).
Replace `sorry` with a valid completing-the-square proof. -/
theorem ex1_fix_false_subgoal (x : ℝ) : -1 / 4 ≤ x ^ 2 + x := by
  -- Broken subgoal: `have h_bad : 0 ≤ x ^ 2 + x := by ...` (false at `x = -1 / 2`!)
  sorry

/-- **Exercise 2 (Avoid an API Island):** Prove monotonicity of `fun x ↦ f (g x) + f x` directly
using Mathlib's `Monotone.comp` and `Monotone.add` without unfolding `Monotone`. -/
theorem ex2_use_mathlib_monotone {f g : ℝ → ℝ} (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun x ↦ f (g x) + f x) := by
  sorry

/-- **Exercise 3a (Refute Vacuous Hypothesis):** Show that no function `f : ℝ → ℝ` satisfies the
unguarded hypothesis from `step_bound_vacuous`. -/
theorem ex3a_vacuous_hyp_impossible : ¬ (∃ f : ℝ → ℝ, ∀ x y : ℝ, f x + 1 ≤ f y) := by
  sorry

/-- **Exercise 3b (Repair Statement):** Restore the `x + 1 ≤ y` guard and prove `f 0 + 2 ≤ f 2`.
-/
theorem ex3b_step_bound_fixed (f : ℝ → ℝ) (h : ∀ x y : ℝ, x + 1 ≤ y → f x + 1 ≤ f y) :
    f 0 + 2 ≤ f 2 := by
  sorry

/-- **Exercise 3c (Sanity Instantiation):** Instantiate `ex3b_step_bound_fixed` on `id` to
verify the repaired hypothesis is satisfiable. -/
theorem ex3c_step_bound_sanity : (0 : ℝ) + 2 ≤ 2 := by
  sorry

end LeanWorkshop.Part4
