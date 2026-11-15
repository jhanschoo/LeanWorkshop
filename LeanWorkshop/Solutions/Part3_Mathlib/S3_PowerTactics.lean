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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Algebra.Ring.Real
import Aesop
import Mathlib.Basic.Real.Basic

/-!
# Solutions — Part 3.3: Tactics in Mathlib

Complete, `sorry`-free reference solutions for
`LeanWorkshop.Part3_Mathlib.S3_PowerTactics`.
-/

namespace LeanWorkshop.Solutions.Part3

/-- **Exercise 1:** Expand `(x + y) ^ 3` over `ℝ` with `ring`. -/
theorem ex1_ring_identity (x y : ℝ) :
    (x + y) ^ 3 = x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3 := by
  ring

/-- **Exercise 2:** Solve linear system with `linarith`. -/
theorem ex2_linarith_bound {x y : ℝ} (h1 : 2 * x + y ≤ 10) (h2 : x - y ≤ 2) : x ≤ 4 := by
  linarith

/-- **Exercise 3:** Prove nonnegativity with `positivity`. -/
theorem ex3_positivity_bound (x y : ℝ) : 0 ≤ x ^ 2 + y ^ 2 + 1 := by
  positivity

/-- **Exercise 4:** Prove inequality via `gcongr`. -/
theorem ex4_gcongr_ineq {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) : a * c + 5 ≤ b * c + 5 := by
  gcongr

/-- **Exercise 5:** Prove the contrapositive using `contrapose!`. -/
theorem ex5_contrapose {n : ℤ} (h : 3 * n + 1 ≤ 10 → n ≤ 2) (hn : 2 < n) : 10 < 3 * n + 1 := by
  contrapose! hn
  exact h hn

/-- **Exercise 6:** Solve modular arithmetic on `ℕ` using `omega` (or `lia`). -/
theorem ex6_omega_parity {n : ℕ} (h : n % 2 = 1) : (n + 3) % 2 = 0 := by
  omega

/-- **Exercise 7:** Prove continuity of a polynomial function on `ℝ` using `fun_prop`. -/
theorem ex7_fun_prop_continuous : Continuous (fun x : ℝ ↦ (x - 1) ^ 2 + 5 * x) := by
  fun_prop

/-- **Exercise 8:** Combine congruence closure and algebraic hypotheses using `grind`. -/
theorem ex8_grind_congr (f : ℝ → ℝ) (x y : ℝ) (hxy : x + y = 4) (hf : f 16 = 0) :
    f ((x + y) ^ 2) = 0 := by
  grind

end LeanWorkshop.Solutions.Part3
