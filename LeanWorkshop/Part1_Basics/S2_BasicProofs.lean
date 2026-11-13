/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Use
import Mathlib.Data.Nat.Basic

/-!
# Part 1.2: Basic Mathematical Proofs

In this module we tour the fundamental proof techniques in Lean 4:
1. Term-mode vs. tactic-mode (`by`) proofs
2. Core structural tactics (`rfl`, `intro`, `exact`, `apply`)
3. Rewriting, forward steps, and chains (`rw`, `have`, `calc`)
4. Logical connectives and quantifiers (`∧`, `∨`, `↔`, `¬`, `∃`)
5. Case analysis and mathematical induction (`cases`, `induction`)
-/

namespace LeanWorkshop.Part1

/-!
---

## 1. Term-Mode vs. Tactic-Mode (`by`) Proofs

Because proofs are terms in Lean, you can write proofs either:
- **In Term Mode:** writing the proof expression directly (concise for one-liners).
- **In Tactic Mode (`by`):** giving step-by-step instructions that transform the goal in the
  Infoview.
-/

-- Term-mode proof of symmetry of equality (if `h : a = b` is an equation, `h.symm : b = a` is
-- that equation flipped):
theorem eq_symm_term (a b : ℕ) (h : a = b) : b = a :=
  h.symm

-- Equivalent tactic-mode proof:
theorem eq_symm_tactic (a b : ℕ) (h : a = b) : b = a := by
  exact h.symm

/-!
---

## 2. Core Structural Tactics (`rfl`, `intro`, `exact`, `apply`)

- **`rfl`** (reflexivity): proves `a = a` up to definitional unfolding (`2 + 2 = 4`, `n + 0 = n`).
- **`intro`**: introduces universally quantified variables (`∀ x`) or implication assumptions
  (`P → Q`) into the local context above `⊢`.
- **`exact t`**: closes the goal immediately when the term `t` has the exact type of the goal.
- **`apply h`**: backward reasoning! If `h : P → Q` and your goal is `⊢ Q`, `apply h` reduces the
  goal to proving the premise `⊢ P`.
-/

example : ∀ a b : ℕ, a = b → a + 0 = b := by
  intro a b h
  -- Context now has `a b : ℕ` and `h : a = b`; goal is `⊢ a + 0 = b`.
  -- Since `a + 0` is definitionally `a`, `exact h` works directly!
  exact h

-- Backward reasoning with `apply`:
example (P Q R : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by
  apply hqr
  -- Goal is now `⊢ Q`
  apply hpq
  -- Goal is now `⊢ P`
  exact hp

/-!
---

## 3. Rewriting, Forward Reasoning, and Calculational Proofs (`rw`, `have`, `calc`)

- **`rw [h]`**: replaces the left-hand side of `h : A = B` (or `A ↔ B`) with its right-hand side in
  the goal, then automatically attempts `rfl`.
- **`rw [← h]`** (typed `\l`): rewrites from right to left (`B` becomes `A`).
- **`rw [h] at hyp`**: rewrites inside a local hypothesis `hyp` instead of the goal.
- **`have h_new : T := by ...`**: forward reasoning—states and proves an intermediate claim `h_new`
  and adds it to the local context.
- **`calc`**: structures a multi-step chain of equalities or inequalities just like a chalkboard
  calculation.
-/

-- Using `rw` and `rw [← ...]`:
example (a b c : ℕ) (h1 : a = b + 1) (h2 : c = b + 1) : a = c := by
  rw [h1]
  rw [← h2]

-- Using `nth_rw` when `rw [h]` would rewrite *all* occurrences of `x` (yielding `f y + y = 10`,
-- which no longer matches `hf`):
example (f : ℕ → ℕ) (x y : ℕ) (h : x = y) (hf : f x + y = 10) : f x + x = 10 := by
  nth_rw 2 [h]
  exact hf

-- Forward reasoning with `have`:
example (P Q R : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by
  have hq : Q := hpq hp
  have hr : R := hqr hq
  exact hr

-- A step-by-step algebraic proof using `calc`
-- (`calc` works with any (pre-)order relation, not just `=`):
theorem add_sq_expand (a b : ℕ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  calc
    (a + b) * (a + b)
      = (a + b) * a + (a + b) * b := by rw [Nat.mul_add]
    _ = a * a + b * a + (a * b + b * b) := by rw [Nat.add_mul, Nat.add_mul]
    _ = a * a + a * b + (a * b + b * b) := by rw [Nat.mul_comm b a]
    _ = a * a + (a * b + (a * b + b * b)) := by rw [Nat.add_assoc]
    _ = a * a + (a * b + a * b + b * b) := by rw [← Nat.add_assoc (a * b)]
    _ = a * a + (2 * (a * b) + b * b) := by rw [← Nat.two_mul]
    _ = a * a + 2 * (a * b) + b * b := by rw [← Nat.add_assoc]

/-!
---

## 4. Logical Connectives and Quantifiers

| Connective | To **Prove** Goal `⊢ ...`         | To **Use** Hypothesis `h : ...`        |
| :--------- | :-------------------------------- | :------------------------------------- |
| `P → Q`, `∀` | `intro h` / `intro x`           | `apply h` or `have := h x`             |
| `P ∧ Q`    | `constructor` or `exact ⟨hp, hq⟩` | `rcases h with ⟨hp, hq⟩` or `h.1`/`h.2`|
| `P ∨ Q`    | `left` or `right`                 | `rcases h with hp \| hq`               |
| `P ↔ Q`    | `constructor` (`→` and `←`)       | `rw [h]` or `h.mp` / `h.mpr`           |
| `¬ P`      | `intro hp` (goal becomes `False`) | `exact h hp` or `apply h`              |
| `∃ x, P x` | `use witness` or `exact ⟨w, hw⟩`  | `rcases h with ⟨x, hx⟩`                |
-/

-- Conjunction (`∧`) and Disjunction (`∨`):
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  rcases h with hp | hq
  · right
    exact hp
  · left
    exact hq

-- Equivalence (`↔`) and Negation (`¬`):
example (P Q : Prop) (h : P → Q) (hnq : ¬ Q) : ¬ P := by
  intro hp
  have hq : Q := h hp
  exact hnq hq

-- Existential quantifier (`∃`):
example (n : ℕ) (h : ∃ k : ℕ, n = 2 * k) : ∃ m : ℕ, n + 2 = 2 * m := by
  rcases h with ⟨k, hk⟩
  use k + 1
  rw [hk, Nat.mul_add, Nat.mul_one]

/-!
---

## 5. Case Analysis and Mathematical Induction (`cases`, `induction`)

When working with inductive types like `Bool`, `List α`, or `ℕ`:
- **`cases x`** splits into a subgoal for each constructor of `x` without an inductive hypothesis.
- **`induction n with | zero => ... | succ n ih => ...`** performs mathematical induction on `n`.
-/

-- Case analysis on a Boolean:
example (b : Bool) : b || !b = true := by
  cases b
  · rfl
  · rfl

/-- Proving `0 + n = n` from scratch by induction on `n`. -/
theorem zero_add_by_induction (n : ℕ) : 0 + n = n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [Nat.add_succ, ih]

/-!
---

## 6. Exercises

Replace each `sorry` below with a working proof.
(Reference solutions are in `LeanWorkshop/Solutions/Part1_Basics/S2_BasicProofs.lean`.)
-/

/-- **Exercise 1:** Prove `R` from `hp : P`, `hpq : P ∧ Q → R`, and `hq : Q`.
Hint: Use `apply hpq` and `constructor`. -/
theorem ex1_and_imp (P Q R : Prop) (hp : P) (hq : Q) (hpq : P ∧ Q → R) : R := by
  sorry

/-- **Exercise 2:** Prove that `∧` distributes over `∨` from the left.
Hint: Start with `constructor`, then use `rcases` to destruct conjunctions `⟨..., ...⟩` and
disjunctions `... | ...`. -/
theorem ex2_and_or_distrib (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry

/-- **Exercise 3:** Prove that `14` is even by providing an explicit witness `k` with `use`. -/
theorem ex3_fourteen_even : ∃ k : ℕ, 14 = 2 * k := by
  sorry

/-- Recursive doubling function on `ℕ` for Exercise 4. -/
def double : ℕ → ℕ
  | 0 => 0
  | n + 1 => double n + 2

/-- **Exercise 4:** Prove by induction on `n` that `double n = n + n`.
Hint: In the `succ n ih` step, unfold `double (n + 1)` with `rw [double, ih]` and use
`Nat.add_right_comm` / `Nat.add_assoc`. -/
theorem ex4_double_eq_add_self (n : ℕ) : double n = n + n := by
  sorry

end LeanWorkshop.Part1
