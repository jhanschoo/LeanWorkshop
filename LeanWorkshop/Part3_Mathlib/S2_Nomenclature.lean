/-
Copyright (c) 2026 Johannes Choo <jhanschoo@gmail.com>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Choo <jhanschoo@gmail.com>
-/
import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Order.Basic
import Mathlib.GroupTheory.Coset.Card

/-!
# Part 3.2: Mathlib Nomenclature and Dot Notation

Even without running `exact?`, you can predict the exact name of most Mathlib lemmas by reading
the statement **from the outside in** (conclusion first for implications; outermost operator first
for nested expressions such as `mul_add` for `a * (b + c)`) and left-to-right in written infix
order.

For the full official guidelines, see:
- **Mathlib Naming Conventions:** `https://leanprover-community.github.io/contribute/naming.html`
- **Mathlib Style Guide:** `https://leanprover-community.github.io/contribute/style.html`

---

## 1. Capitalization Conventions

| Kind | Style | Example |
| :--- | :--- | :--- |
| Terms of `Prop` (theorems, lemmas, proof variables) | `snake_case` | `add_comm`, `le_of_lt` |
| Types, structures, classes, inductive types | `UpperCamelCase` | `Point2D`, `RingHom` |
| Predicates (`... → Prop`) | `UpperCamelCase` (often `Is...`) | `List.IsPrefix` |
| Data definitions, functions, fields, constructors | `lowerCamelCase` | `doubleList`, `normSq` |

Rule of thumb: **capitalize Types (`Type*`), `lowerCamelCase` data/functions, `snake_case`
proofs!** When a `camelCase` identifier (or an `UpperCamelCase` type converted to `lowerCamelCase`)
appears inside a `snake_case` theorem name, it keeps its internal `lowerCamelCase` (as in
`doubleBound_even_mod` below).
-/

namespace LeanWorkshop.Part3

/-- An `UpperCamelCase` structure wrapping a natural number bound. -/
structure UpperBound where
  /-- The stored upper bound value. -/
  val : ℕ

/-- A `lowerCamelCase` function returning a value. -/
def doubleBound (b : UpperBound) : ℕ :=
  2 * b.val

/-- A `snake_case` theorem stating a `Prop`. -/
theorem doubleBound_even_mod (b : UpperBound) : doubleBound b % 2 = 0 := by
  dsimp [doubleBound]
  omega

/-!
---

## 2. The Grammar of Mathlib Lemma Names

1. **Implications read conclusion-first (`conclusion_of_hyp1_of_hyp2`):**
   - `lt_of_le_of_lt`: from `a ≤ b` and `b < c`, conclude `a < c`.
   - `le_of_lt`: from `a < b`, conclude `a ≤ b`.
   - `ne_of_lt`: from `a < b`, conclude `a ≠ b`.
2. **Equivalences use `_iff_` (or describe the simplified form directly):**
   - `add_le_add_iff_right`: `(a + c ≤ b + c) ↔ (a ≤ b)`.
   - `sub_eq_zero`: `(a - b = 0) ↔ (a = b)`.
   - `not_le`: `(¬ a ≤ b) ↔ (b < a)`.
-/

#check lt_of_le_of_lt
#check le_of_lt
#check ne_of_lt
#check add_le_add_iff_right
#check sub_eq_zero

/-!
---

## 3. The Symbol Dictionary

Mathlib translates mathematical symbols into consistent `snake_case` tokens:

| Symbol | Token | Symbol | Token |
| :--- | :--- | :--- | :--- |
| `+` | `add` | `=` | `eq` |
| `-` (binary / unary) | `sub` / `neg` | `≠` | `ne` |
| `*` | `mul` | `<` | `lt` |
| `/` | `div` | `≤` | `le` |
| `^` | `pow` (`sq` for `^ 2`) | `>` / `≥` | `gt` / `ge` (prefer `lt`/`le`) |
| `0` / `1` | `zero` / `one` | `∧` / `∨` | `and` / `or` |
| `¬` | `not` | `↔` | `iff` |
| `∪` / `∩` | `union` / `inter` | `∈` / `⊆` / `∅` | `mem` / `subset` / `empty` |

Reading `a + b = b + a` as tokens gives `add_comm`; reading `a * (b + c) = a * b + a * c` gives
`mul_add`; reading `(a + b) * c = a * c + b * c` gives `add_mul`.

---

## 4. Structural Laws and Positional Suffixes

- **Algebraic properties:** `comm`, `assoc`, `left_comm`, `right_comm`
- **Identity & inverse laws:** `zero_add`, `add_zero`, `one_mul`, `mul_one`, `sub_self`, `neg_neg`
- **Cancellation:** `add_left_cancel`, `add_right_cancel`
- **Left vs right sides:**
  - `mul_add` distributes `*` from the **left** (`a * (b + c)`); `add_mul` from the **right**
    (`(a + b) * c`).
  - `le_max_left` says `a ≤ max a b`; `le_max_right` says `b ≤ max a b`.
  - `add_le_add_left` adds a constant on the **left** (`c + a ≤ c + b`); `add_le_add_right` on
    the **right** (`a + c ≤ b + c`).
-/

#check mul_add
#check add_mul
#check add_right_cancel
#check le_max_right

/-!
---

## 5. Standard Predicates (`pos`, `nonneg`, `neg`, `mono`, `inj`)

Instead of writing `0 < _`, `0 ≤ _`, or `_ < 0`, Mathlib names inequalities against zero using
predicates:
- `pos`: `0 < x` (e.g., `add_pos`, `mul_pos`)
- `nonneg`: `0 ≤ x` (e.g., `add_nonneg`, `mul_nonneg`, `sq_nonneg`)
- `neg`: `x < 0`
- `mono` / `strictMono`: monotonicity (`Monotone f` / `StrictMono f`)
- `inj`: injectivity (`Function.Injective f`)
-/

#check add_pos
#check mul_pos
#check mul_nonneg
#check sq_nonneg

/-!
---

## 6. Famous Theorems vs. Their Structural Names in Mathlib

Mathlib strongly prefers **structural names** over **eponyms** (historical names vary across
languages and cultures, and figures like Euler, Cauchy, or Lagrange have dozens of theorems). A
structural name lets you read the conclusion and hypotheses straight from the identifier, while
the eponym is kept in the docstring so semantic search tools (such as LeanSearch and LeanExplore)
still find it:

| Famous Name | Mathlib Structural Name | Statement Idea |
| :--- | :--- | :--- |
| **Lagrange's Theorem** | `Subgroup.card_subgroup_dvd_card` | `Nat.card H ∣ Nat.card G` |
| **Fermat's Little Theorem** | `ZMod.pow_card_sub_one_eq_one` | `a ≠ 0 → a ^ (p - 1) = 1` |
| **Pigeonhole Principle** | `Fintype.exists_ne_map_eq_of_card_lt` | `∃ x y, x ≠ y ∧ f x = f y` |
| **Cauchy–Schwarz** | `norm_inner_le_norm` | `‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖` |
| **Squeeze Theorem** | `tendsto_of_tendsto_of_tendsto_of_le_of_le` | `f ≤ g ≤ h` implies `g → a` |
| **Intermediate Value** | `intermediate_value_Icc` | `Icc (f a) (f b) ⊆ f '' Icc a b` |
| **FTC (Part 2)** | `intervalIntegral.integral_eq_sub_of_hasDerivAt` | `∫ a..b, f' = f b - f a` |
| **Cantor's Theorem** | `Function.cantor_surjective` | `¬ Surjective (f : α → Set α)` |

Notice that `Function.cantor_surjective` is a rare exception where the eponym appears in the name
itself (alongside variants like `inner_mul_inner_self_le` for squared Cauchy–Schwarz).
-/

#check Subgroup.card_subgroup_dvd_card
#check Function.cantor_surjective

/-!
---

## 7. Dot Notation on Proof Terms

Because `Eq`, `LE.le`, `LT.lt`, and `Iff` are types/predicates in namespaces, Lean lets you call
projection lemmas directly on proof terms `h`:
- `h.symm`: turns `h : a = b` into `b = a`.
- `h1.trans h2`: combines `h1 : a = b` and `h2 : b = c` (or `≤`) into `a = c` (or `a ≤ c`).
- `h.le` / `h.ne`: turns `h : a < b` into `a ≤ b` or `a ≠ b`.
- `h.mp` / `h.mpr`: extracts the forward (`P → Q`) or backward (`Q → P`) direction of `h : P ↔ Q`.
-/

example {a b c : ℕ} (h1 : a = b) (h2 : b = c) : c = a :=
  (h1.trans h2).symm

example {a b : ℕ} (h : a < b) : a ≤ b :=
  h.le

example {P Q : Prop} (h : P ↔ Q) (hq : Q) : P :=
  h.mpr hq

/-!
---

## 8. Exercises

Solve these **without** `exact?` or automation tactics—predict the Mathlib lemma name or use dot
notation directly!
(Reference solutions are in `LeanWorkshop/Solutions/Part3_Mathlib/S2_Nomenclature.lean`.)
-/

/-- **Exercise 1:** Combine `h1 : a ≤ b` and `h2 : b < c` to prove `a < c`. -/
theorem ex1_predict_name {a b c : ℤ} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  sorry

/-- **Exercise 2:** Prove right-distributivity `(a + b) * c = a * c + b * c` on `ℤ`. -/
theorem ex2_predict_distrib (a b c : ℤ) : (a + b) * c = a * c + b * c := by
  sorry

/-- **Exercise 3:** Prove positivity of a sum of positive integers `0 < a + b`. -/
theorem ex3_predict_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by
  sorry

/-- **Exercise 4:** Chain equalities with dot notation (`h.trans`, `h.symm`) to prove `a = c`. -/
theorem ex4_dot_chain {a b c : ℕ} (h1 : a = b) (h2 : c = b) : a = c := by
  sorry

/-- **Exercise 5:** Derive `a ≤ b ∧ a ≠ b` from `h : a < b` using dot notation. -/
theorem ex5_lt_imp_le_and_ne {a b : ℕ} (h : a < b) : a ≤ b ∧ a ≠ b := by
  sorry

end LeanWorkshop.Part3
