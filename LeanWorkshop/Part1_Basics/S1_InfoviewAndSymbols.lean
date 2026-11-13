/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Basic.Real.Basic

/-!
# Part 1.1: The Infoview and Symbol Input

Welcome to **LeanWorkshop**! Lean 4 is both a functional programming language and an interactive
theorem prover. As you move your cursor through a `.lean` file in VS Code, the **Lean Infoview**
panel updates in real time to show:
- Output of interactive queries (`#check`, `#eval`, `#print`)
- Current proof state (local hypotheses above `⊢` and goals to prove below `⊢`)
- Compiler diagnostics, warnings, and linter messages

> **Tip:** To open the Infoview in VS Code, click the `∀` icon in the top-right editor title bar
> or press `Ctrl+Shift+Enter` (`Cmd+Shift+Enter` on macOS).

---

## 1. Interacting with the Infoview (`#check`, `#eval`, `#print`)

Place your cursor on each line below and observe the **Messages** section of the Infoview.
-/

namespace LeanWorkshop.Part1

-- `#check` reports the type of any expression or declaration without evaluating it:
#check 42
#check (42 : ℤ)
#check (-3 : ℝ)
#check "Hello, Lean 4!"
#check true && false

-- `#check` also works on types and functions:
#check ℕ
#check ℝ
#check Nat.add
#check Nat.add_comm

-- `#eval` executes a computational expression and prints the resulting value:
#eval 2 + 3 * 4
#eval 2 ^ 10
#eval Nat.gcd 48 180
#eval (1 / 3 + 1 / 6 : ℚ)
#eval List.map (fun n ↦ n * n) [1, 2, 3, 4, 5]

/-
Note: `#eval` requires a computable representation. Because real numbers `ℝ` are constructed as
equivalence classes of Cauchy sequences, operations on `ℝ` are marked `noncomputable` and cannot
be run with `#eval` (use `ℚ` for exact rational arithmetic evaluation).
-/

-- `#print` reveals the internal definition of an inductive type, function, or theorem:
#print Bool
#print And
#print Or
#print Nat.add_comm

/-!
---

## 2. Unicode Symbol Input Cheat Sheet

Lean uses standard mathematical Unicode symbols. In VS Code, type a backslash `\` followed by the
shortcut name, then press `Space`, `Tab`, or `Enter` (or simply continue typing).

> **Tip:** Hovering your mouse over any symbol in a `.lean` file displays a tooltip showing the
> exact `\` keystroke sequences used to type it!
>
> **Tip:** To view the full list of all symbol shortcuts in VS Code, open the Command Palette
> (`Ctrl+Shift+P` / `Cmd+Shift+P`) and run **`Lean 4: Docs: Show Unicode Input Abbreviations`**,
> or use **`Lean 4: Input: Find Unicode Symbol...`** to search by name.

| Symbol | Meaning                        | Backslash Shortcut(s)          |
| :----: | :----------------------------- | :----------------------------- |
|  `ℕ`   | Natural numbers (`0, 1, 2, …`) | `\N` or `\nat`                 |
|  `ℤ`   | Integers                       | `\Z` or `\int`                 |
|  `ℚ`   | Rational numbers               | `\Q` or `\rat`                 |
|  `ℝ`   | Real numbers                   | `\R` or `\real`                |
|  `→`   | Function / Implication arrow   | `\to` or `\r` or `\imp`        |
|  `↦`   | Function maps-to (`fun x ↦ …`) | `\mapsto`                      |
|  `←`   | Left arrow (reverse rewrite)   | `\l` or `\gets`                |
|  `∀`   | Universal quantifier (for all) | `\forall` or `\all`            |
|  `∃`   | Existential quantifier         | `\exists` or `\ex`             |
|  `∧`   | Logical AND                    | `\and` or `\wedge`             |
|  `∨`   | Logical OR                     | `\or` or `\vee`                |
|  `¬`   | Logical NOT                    | `\not` or `\neg`               |
|  `↔`   | If and only if (iff)           | `\iff` or `\lr`                |
|  `≤`   | Less than or equal             | `\le` or `\leq`                |
|  `≥`   | Greater than or equal          | `\ge` or `\geq`                |
|  `≠`   | Not equal                      | `\ne` or `\neq`                |
| `⟨ ⟩`  | Anonymous constructor brackets | `\langle` and `\rangle` (or `\<`, `\>`) |
|  `·`   | Subgoal focus bullet           | `\cdot` or `\.`                |
| `α β`  | Greek letters                  | `\alpha` (`\a`), `\beta` (`\b`)|
| `₁ ₂`  | Subscripts                     | `\_1`, `\_2`                   |
-/

-- Hover over the symbols in these expressions to inspect their types and input shortcuts:
#check ∀ n : ℕ, 0 ≤ n
#check ∃ k : ℕ, k + k = 10
#check fun x : ℤ ↦ x ^ 2 + 1
#check ∀ P Q : Prop, P ∧ Q → Q ∨ P

/-!
---

## 3. Anatomy of a Statement and Proof / Definition

Almost every declaration in Lean follows the same four-part template:

```text
keyword  name  (inputs_and_assumptions) : target_type_or_claim :=
  body_or_proof
```

1. **Keyword (`def`, `theorem`, `lemma`, `example`):** All four keywords share this structure.
   `def` defines a value or function; `theorem` and `lemma` state a named mathematical claim;
   `example` states an anonymous claim (omitting `name`).
2. **Inputs `( ... )`:** Variables (such as `(n : ℕ)`) and assumptions (such as `(h : x = y)`)
   available inside the statement and proof. You may also encounter inputs written in curly braces
   `{ ... }`, square brackets `[ ... ]`, or to the right of `:` using `∀` or `→` (such as
   `: ∀ n : ℕ, ...`). Take note of how things differ between specifying to the left or right
   of the colon, but you can ignore the other differences for now.
3. **Target `: ...`:** After the colon `:`, either the output type of a definition or the
   mathematical statement to be proved.
4. **Body `:= ...`:** After `:=`, either a formula/expression (for a `def`) or `by` followed by
   proof steps (tactics).
-/

-- A function definition (`def`): takes `n : ℕ`, returns a `: ℕ`, defined by the formula `2 * n`:
/-- Doubles a natural number `n`. -/
def doubleNat (n : ℕ) : ℕ :=
  2 * n

-- A named theorem (`theorem` / `lemma`): takes `n : ℕ`, claims `: n + 0 = n`, proved via `by rfl`:
/-- Adding zero on the right of `n` yields `n`. -/
theorem add_zero_nat (n : ℕ) : n + 0 = n := by
  rfl

-- An anonymous claim (`example`): omits the name, takes `x y : ℕ` and assumption `h : x = y`:
example (x y : ℕ) (h : x = y) : y = x := by
  rw [h]

-- Inputs in curly braces `{ ... }` (implicit inputs inferred by Lean):
example {x y : ℕ} (h : x = y) : y = x := by
  rw [h]

-- Inputs with square brackets `[ ... ]` (equipping a type `G` with a structure like `Group`):
example {G : Type*} [Group G] (a : G) : a * 1 = a := by
  exact mul_one a

-- Inputs written to the right of `:` using `∀` ("for all") and `→` ("implies"):
example : ∀ x y : ℕ, x = y → y = x := by
  intro x y h
  rw [h]

/-!
---

## 4. Reading the Infoview Tactic State

When proving a statement inside a `by` block, the Infoview displays the **Tactic State**:
- Everything **above** the turnstile `⊢` is your local context (variables and assumptions).
- Everything **below** (or to the right of) `⊢` is the current goal you must prove.

Step your cursor line-by-line through the two examples below to watch the goal state change.
-/

example (x y : ℕ) (h : x = y) : x + 1 = y + 1 := by
  -- Cursor here: context has `x y : ℕ` and `h : x = y`; goal is `⊢ x + 1 = y + 1`.
  rw [h]
  -- `rw [h]` replaces `x` with `y` and automatically closes the reflexive goal `y + 1 = y + 1`.

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  -- Cursor here: goal is `⊢ P ∧ Q`.
  constructor
  -- Now there are TWO subgoals: `⊢ P` and `⊢ Q`.
  -- We focus on each subgoal using the middle dot `·` (typed `\cdot` or `\.`):
  · exact hp
  · exact hq

/-!
---

## 5. Exercises

Replace each `sorry` below with a working definition or proof. Watch the Infoview as you work!
(Reference solutions are in `LeanWorkshop/Solutions/Part1_Basics/S1_InfoviewAndSymbols.lean`.)
-/

/-- **Exercise 1:** Define a function that maps a natural number `n` to `n * n + 1`.
Hint: Emulate `#check fun x : ℤ ↦ x ^ 2 + 1` from earlier in the file (using `n * n + 1` as the
body). -/
def ex1_squarePlusOne (n : ℕ) : ℕ :=
  sorry

/-- **Exercise 2:** Prove that for every natural number `n`, `n + 0 = n`.
Hint: Use `intro n` followed by `rfl`. -/
theorem ex2_add_zero : ∀ n : ℕ, n + 0 = n := by
  sorry

/-- **Exercise 3:** Swap the components of a conjunction `P ∧ Q`.
Hint: Use `constructor` and focus each branch with `·`, using `h.1` and `h.2`. -/
theorem ex3_swap_and (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  sorry

/-- **Exercise 4:** Chain two equality rewrites `h1 : a = b` and `h2 : b = c` to prove
`a + 2 = c + 2`. -/
theorem ex4_rewrite_chain (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a + 2 = c + 2 := by
  sorry

end LeanWorkshop.Part1
