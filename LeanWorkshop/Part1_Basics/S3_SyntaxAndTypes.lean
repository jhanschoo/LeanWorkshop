/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Group.Defs

/-!
# Part 1.3: Basic Mathematical Syntax and Types

Lean's foundation is **dependent type theory** (specifically, the Calculus of Inductive
Constructions). Every expression in Lean has a unique type, and types themselves are first-class
citizens.

---

## 1. Basic Mathematical Types and the Universe Hierarchy

In Lean, values, sets of values, and logical statements all live in a unified type system:
- `42 : ℕ` (a term of type `ℕ`)
- `ℕ : Type` (`ℕ` itself has type `Type`, which is shorthand for `Type 0`)
- `Type : Type 1`, `Type 1 : Type 2`, … (a hierarchy of universes preventing Russell's paradox)
- `Prop`: the universe of logical propositions (`2 + 2 = 4 : Prop`, `Prop : Type`)
-/

namespace LeanWorkshop.Part1

#check (5 : ℕ)
#check (-5 : ℤ)
#check (3 / 4 : ℚ)
#check (3.5 : ℝ)
#check (2 + 2 = 4 : Prop)
#check ℕ
#check Prop
#check Type

/-!
### Arithmetic Pitfall: Natural Number Truncation (`ℕ` vs. `ℤ` and `ℚ`)

In Lean and Mathlib, binary operations like `-` and `/` are total functions on their type.
On `ℕ`:
- Subtraction truncates at `0`: `a - b = 0` whenever `a ≤ b`.
- Division is integer division (floor): `7 / 2 = 3`.
-/

#eval (3 - 5 : ℕ) -- 0 (truncated subtraction on ℕ!)
#eval (3 - 5 : ℤ) -- -2 (true integer subtraction on ℤ)
#eval (7 / 2 : ℕ) -- 3 (integer division on ℕ!)
#eval (7 / 2 : ℚ) -- 7/2 (exact rational division on ℚ)
#eval (1 / 0 : ℕ) -- 0 (division by zero returns 0 by convention!)
#eval (1 / 0 : ℚ) -- 0 (same convention on ℤ, ℚ, and ℝ)

/-!
> **Note on "division" by zero:** Because `/` is a total function (it does not take a `b ≠ 0`
> proof argument), Lean and Mathlib adopt the convention `a / 0 = 0` on `ℕ`, `ℤ`, `ℚ`, and `ℝ`.
> This "junk value" convention keeps algebraic notation clean, while theorems about division
> (such as `a / b * b = a`) still require an explicit `b ≠ 0` hypothesis so nothing false can be
> proved.
-/

/-!
### Propositions as Types (Curry–Howard Correspondence)

In Lean:
- A proposition `P : Prop` is a **type**.
- A proof `h : P` is a **term** of type `P`.
- An implication `P → Q` is a **function type** taking a proof of `P` and returning a proof of `Q`.
-/

/-!
---

## 2. Defining Functions and Constants (`def`, `abbrev`, `fun x ↦ ...`)

Use `def` to define named constants and functions. Notice that Lean functions are **curried** by
default: a two-argument function `f : ℤ → ℤ → ℤ` can be partially applied to one argument!
-/

/-- Doubles a natural number and adds three. -/
def doubleAddThree (n : ℕ) : ℕ :=
  2 * n + 3

/-- Equivalent anonymous lambda syntax using `fun n ↦ ...` (typed `\mapsto`). -/
def doubleAddThree' : ℕ → ℕ :=
  fun n ↦ 2 * n + 3

#eval doubleAddThree 10
#eval doubleAddThree' 10

/-- Computes a weighted sum `2 * x + y`. -/
def weightedSum (x y : ℤ) : ℤ :=
  2 * x + y

#check weightedSum      -- ℤ → ℤ → ℤ
#check weightedSum 10   -- ℤ → ℤ (partially applied function!)
#eval weightedSum 10 5  -- 25

/-- Recursive definition by pattern matching on `ℕ`: sum of `0 + 1 + ⋯ + n`. -/
def sumUpTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumUpTo n + (n + 1)

#eval sumUpTo 10 -- 55

/-!
> **Note:** Pattern matching in Lean has important nuances (such as exhaustiveness checks,
> structural recursion / termination, `n + 1` as shorthand for `Nat.succ n`, and how overlapping
> patterns are ordered). Feel free to ask an LLM or consult the Lean 4 reference manual for
> details when writing more complex pattern matches.
-/

/-!
---

## 3. Stating Theorems (`def` vs. `theorem` vs. `example`)

- **`def`**: Used for **data** and **functions** (`ℕ`, `ℤ → ℤ`, `Type`). Lean remembers the
  computational body of a `def` so it can unfold and `#eval` it.
- **`theorem`** (or **`lemma`**): Used for **proofs of propositions** (`Prop`). By *proof
  irrelevance*, any two proofs of the same proposition `P : Prop` are definitionally equal.
- **`example`**: An unnamed `theorem` or `def` used for demonstrations and scratch work without
  adding a permanent name to the environment.
-/

/-- A named theorem about `doubleAddThree`. -/
theorem doubleAddThree_zero : doubleAddThree 0 = 3 := by
  rfl

-- An unnamed example verifying a specific evaluation:
example : sumUpTo 4 = 10 := by
  rfl

/-!
---

## 4. Binder Types: Explicit `()`, Implicit `{}`, and Typeclass `[]`

Lean supports three main kinds of parameter brackets:

1. **Explicit `(x : α)`**: The caller must pass `x` explicitly.
2. **Implicit `{α : Type*}`**: Lean infers the argument automatically from context.
3. **Typeclass `[Monoid M]`**: Lean synthesizes the algebraic structure automatically from its
   typeclass table.
-/

/-- Identity function with an implicit type parameter `{α : Type*}` and explicit input `(x : α)`. -/
def myId {α : Type*} (x : α) : α :=
  x

-- Lean infers `α = ℕ` or `α = String` automatically:
#eval myId 42
#eval myId "implicit!"

-- Prefix a declaration with `@` to supply implicit arguments explicitly:
#eval @myId ℕ 42

/-- Squares any element in a monoid `M` using its multiplication `*`. -/
def monoidSquare {M : Type*} [Monoid M] (x : M) : M :=
  x * x

-- From `(7 : ℤ)`, Lean infers `M = ℤ` and then automatically runs *typeclass synthesis* to find
-- the `Monoid ℤ` instance in Mathlib, which supplies the `*` operation for `x * x`:
#eval monoidSquare (7 : ℤ)

/-- In any monoid `M`, multiplying `x` by `1` on the right yields `x`. -/
theorem monoidSquare_of_eq_one {M : Type*} [Monoid M] (x : M) (hx : x = 1) :
    monoidSquare x = 1 := by
  unfold monoidSquare
  rw [hx, mul_one]

/-!
---

## 5. Applying Theorems in Proofs: Partial Application, `_`, and Inline `by`

Because theorems in Lean are typed just like curried functions (taking parameters and proofs of
hypotheses to a proof of the conclusion), all of Lean's function-application features work inside
proofs as well.

### 5.1 Partial Application of Theorems

Passing only the first few arguments to a theorem specializes those parameters and returns a
proof of the remaining implication or `∀` statement:
-/

-- `Nat.add_comm` takes two explicit `ℕ` arguments:
#check Nat.add_comm       -- ∀ (n m : ℕ), n + m = m + n
#check Nat.add_comm 3     -- ∀ (m : ℕ), 3 + m = m + 3
#check Nat.add_comm 3 5   -- 3 + 5 = 5 + 3

example (h : ∀ a b : ℕ, a = b → a + 1 = b + 1) (x y : ℕ) (hxy : x = y) :
    x + 1 = y + 1 := by
  -- Partially applying `h` to `x` and `y` yields a specialized implication:
  have h_spec : x = y → x + 1 = y + 1 := h x y
  -- Applying `h_spec` to `hxy` produces the final proof of `x + 1 = y + 1`:
  exact h_spec hxy

/-!
### 5.2 Placeholder `_` Usage

When a theorem has explicit `( ... )` parameters that can be determined from later arguments or
from the goal, you can write `_` to ask Lean to infer them automatically:
-/

example (h : ∀ a b : ℕ, a = b → a + 1 = b + 1) (x y : ℕ) (hxy : x = y) :
    x + 1 = y + 1 := by
  -- Lean infers both `_`s (`a = x` and `b = y`) from the type of `hxy : x = y`:
  exact h _ _ hxy

example (a b c : ℕ) : a + (b + c) = a + (c + b) := by
  -- Pin down the second argument `c` of `Nat.add_comm` while letting Lean infer the first (`_`):
  rw [Nat.add_comm _ c]

/-!
### 5.3 Omitting Specialization in Tactics That Support It (`rw`, `apply`)

Many tactics unify a theorem against the current goal automatically, allowing you to omit explicit
arguments or hypotheses altogether:
- **`rw [thm]`** searches the goal for the first subterm matching the left-hand side of `thm` and
  fills in its parameters automatically.
- **`apply thm`** matches the *conclusion* of `thm` against the goal, infers the leading parameters,
  and turns any remaining hypotheses into new subgoals.
-/

example (a b : ℕ) : a + b = b + a := by
  -- No need to write `rw [Nat.add_comm a b]`; `rw` specializes `a` and `b` from the goal:
  rw [Nat.add_comm]

example (h : ∀ a b : ℕ, a = b → a + 1 = b + 1) (x y : ℕ) (hxy : x = y) :
    x + 1 = y + 1 := by
  -- `apply h` unifies `a = x` and `b = y` from the goal and leaves only `⊢ x = y`:
  apply h
  exact hxy

/-!
### 5.4 Inline Tactic Blocks `(by ...)`

Since `by ...` constructs a proof term, you can embed `(by ...)` inline wherever an expression or
hypothesis proof is expected—such as inside `exact`, `have`, `rw`, or a tuple `⟨..., ...⟩`:
-/

example (h : ∀ a b : ℕ, a + b = b + a → a + b + 1 = b + a + 1) (x y : ℕ) :
    x + y + 1 = y + x + 1 := by
  -- Supply the proof of `x + y = y + x` on the fly using an inline `(by ...)` block:
  exact h _ _ (by rw [Nat.add_comm])

example (a b : ℕ) (h : a = b) : a = b ∧ b + 0 = a :=
  -- Combine a direct proof term `h` with an inline tactic block inside `⟨..., ...⟩`:
  ⟨h, by rw [Nat.add_zero, h]⟩

/-!
---

## 6. Exercises

Replace each `sorry` below with a valid implementation or proof.
(Reference solutions are in `LeanWorkshop/Solutions/Part1_Basics/S3_SyntaxAndTypes.lean`.)
-/

/-- **Exercise 1:** Define the quadratic expression `a * x ^ 2 + b * x + c` over the integers `ℤ`.
-/
def ex1_quad (a b c x : ℤ) : ℤ :=
  sorry

/-- **Exercise 2:** Define polymorphic function composition `(g ∘ f) x = g (f x)`.
Notice that `α`, `β`, and `γ` are implicit `{...}`. -/
def ex2_myComp {α β γ : Type*} (g : β → γ) (f : α → β) (x : α) : γ :=
  sorry

/-- **Exercise 3:** Prove that `monoidSquare (1 : M) = 1` in any `Monoid M`.
Hint: `unfold monoidSquare` and then `rw [mul_one]`. -/
theorem ex3_monoidSquare_one {M : Type*} [Monoid M] : monoidSquare (1 : M) = 1 := by
  sorry

/-- **Exercise 4:** Give a direct term-mode proof (using `fun hpq hqr hp ↦ ...`, no `by`) of the
transitivity of implication. -/
theorem ex4_imp_trans {P Q R : Prop} : (P → Q) → (Q → R) → P → R :=
  sorry

/-- **Exercise 5:** Use `exact h _ _` together with an inline `(by ...)` block to prove
`f (x + 0) = f x` from `h : ∀ a b : ℕ, a = b → f a = f b`. -/
theorem ex5_inline_by (f : ℕ → ℕ) (h : ∀ a b : ℕ, a = b → f a = f b) (x : ℕ) :
    f (x + 0) = f x := by
  sorry

end LeanWorkshop.Part1
