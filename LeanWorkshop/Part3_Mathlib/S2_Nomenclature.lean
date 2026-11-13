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

/-!
# Part 3.2: Mathlib Nomenclature and Dot Notation

Even without running `exact?`, you can predict the exact name of most Mathlib lemmas just by
reading the statement from the inside out.

---

## 1. The Grammar of Mathlib Lemma Names

1. **Implications read conclusion-first (`conclusion_of_hyp1_of_hyp2`):**
   - `lt_of_le_of_lt`: from `a ≤ b` and `b < c`, conclude `a < c`.
   - `le_of_lt`: from `a < b`, conclude `a ≤ b`.
   - `ne_of_lt`: from `a < b`, conclude `a ≠ b`.
2. **Equivalences use `_iff_` (or describe the simplified form directly):**
   - `add_le_add_iff_right`: `(a + c ≤ b + c) ↔ (a ≤ b)`.
   - `sub_eq_zero`: `(a - b = 0) ↔ (a = b)`.
   - `not_le`: `(¬ a ≤ b) ↔ (b < a)`.
-/

namespace LeanWorkshop.Part3

#check lt_of_le_of_lt
#check le_of_lt
#check ne_of_lt
#check add_le_add_iff_right
#check sub_eq_zero

/-!
---

## 2. The Symbol Dictionary

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

## 3. Structural Laws and Positional Suffixes

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

## 4. Standard Predicates (`pos`, `nonneg`, `neg`, `mono`, `inj`)

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

## 5. Dot Notation on Proof Terms

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

## 6. Exercises

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
