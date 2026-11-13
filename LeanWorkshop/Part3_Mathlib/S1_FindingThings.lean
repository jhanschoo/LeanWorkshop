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
# Part 3.1: Finding Things in Mathlib and Community Resources

Mathlib contains well over a hundred thousand theorems. Nobody memorizes them all; instead, Lean
users combine **in-editor search tactics**, **type/name inspection**, and **external search
engines** to locate lemmas in seconds.

---

## 1. Interactive Search Tactics (`exact?`, `apply?`, `rw?`, `simp?`)

When you know a fact should already exist in the local context or Mathlib, ask Lean directly:

- `exact?` searches the local context and imported Mathlib lemmas to close the goal in one step,
  printing a clickable `Try this: exact ...` suggestion in the Infoview.
- `apply?` finds lemmas whose conclusion matches the current goal and leaves any remaining
  hypotheses as subgoals.
- `rw?` suggests equality or `iff` lemmas that rewrite part of the goal.
- `simp?` runs `simp` and prints the minimal `simp only [...]` call it used.

**Best practice:** Always replace `exact?`, `apply?`, `rw?`, and `simp?` with their suggested
output once found! Leaving search tactics in finished proofs slows down compilation and makes
builds sensitive to future library changes.
-/

namespace LeanWorkshop.Part3

/-- Example: discovering `Nat.add_comm` via `exact?`. -/
example (a b : ℕ) : a + b = b + a := by
  -- Try uncommenting `exact?` and clicking the Infoview suggestion:
  -- exact?
  exact Nat.add_comm a b

/-- Example: discovering `add_neg_cancel` via `exact?` or `simp?`. -/
example (x : ℤ) : x + -x = 0 := by
  -- simp?
  -- exact?
  exact add_neg_cancel x

/-- Example: discovering `le_trans` via `apply?`. -/
example {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  -- apply?
  exact le_trans hab hbc

/-!
---

## 2. Inspecting Declarations (`#check`, `#print`, and Go-to-Definition)

Once you know or guess a lemma name, inspect its exact signature and implementation:
- `#check` shows the type signature (implicit vs explicit arguments, typeclasses).
- `#check @lemma` prints all implicit arguments `{...}` and typeclass instances `[...]` explicitly.
- `#print` prints the full definition or proof term.
- In VS Code, hover over any identifier to read its docstring, or press `F12` (Ctrl/Cmd+Click) to
  jump straight to its source file in Mathlib.
-/

#check Nat.add_comm
#check @add_comm
#check le_trans
#check Int.sub_add_cancel

/-!
---

## 3. External Search Engines and Documentation

When the lemma you need is not yet imported in your file—or you only know its mathematical idea—use
these community search tools:

| Tool | Best For | Example Query / URL |
| :--- | :--- | :--- |
| **Loogle** | Type / pattern search | `https://loogle.lean-lang.org` — `?a + ?b = ?b + ?a` |
| **LeanSearch** | Natural language queries | `https://leansearch.net` — "sum of first n naturals" |
| **Moogle** | Semantic Mathlib search | `https://www.moogle.ai` — "triangle inequality" |
| **Mathlib4 Docs** | API & module browsing | `https://leanprover-community.github.io/mathlib4_docs/` |
| **Reservoir** | Lean 4 package index | `https://reservoir.lean-lang.org` |
| **Lean Zulip** | Live Q&A (`#new members`) | `https://leanprover.zulipchat.com` |

---

## 4. Community Tutorials and Learning Resources

To continue learning after this workshop, these free community resources are the gold standard:

1. **The Natural Number Game (NNG4)** — Gamified introduction to Lean 4 tactics (`rw`, `induction`,
   `apply`, `exact`, `simp`). Great right after Part 1.
2. **Mathematics in Lean (MIL)** — Hands-on interactive repository covering algebra, analysis,
   topology, and Mathlib idioms (`leanprover-community/mathematics_in_lean`).
3. **Theorem Proving in Lean 4 (TPIL4)** — Thorough reference on dependent type theory, terms,
   tactics, typeclasses, and induction.
4. **The Mechanics of Proof** (Heather Macbeth) — Undergraduate-friendly textbook emphasizing clean
   structured proofs in Lean 4.
5. **Formalising Mathematics** (Kevin Buzzard) — Worked problem sheets across groups, rings,
   filters, and topology.
6. **Functional Programming in Lean** — Essential if you plan to write Lean programs or custom
   tactics.
7. **Lean Blueprints** (`leanblueprint`) — Connects LaTeX dependency graphs with formalized Lean
   theorems for collaborative projects.

---

## 5. Exercises

Use `exact?`, `apply?`, `rw?`, `#check`, or Loogle to find the right Mathlib lemma for each
exercise, then replace `sorry` with the clean one-line lemma call.
(Reference solutions are in `LeanWorkshop/Solutions/Part3_Mathlib/S1_FindingThings.lean`.)
-/

/-- **Exercise 1:** Find the associativity lemma to re-associate `a + (a + b)`. -/
theorem ex1_absorb (a b : ℕ) : a + (a + b) = a + a + b := by
  sorry

/-- **Exercise 2:** Find the lemma converting `a < b + 1` to `a ≤ b` on `ℕ`. -/
theorem ex2_le_of_lt_add_one {a b : ℕ} (h : a < b + 1) : a ≤ b := by
  sorry

/-- **Exercise 3:** Find the integer cancellation lemma for `a - b + b = a`. -/
theorem ex3_sub_add_cancel (a b : ℤ) : a - b + b = a := by
  sorry

/-- **Exercise 4:** Find the lemma stating `a ≤ max a b` on `ℕ`. -/
theorem ex4_le_max_left (a b : ℕ) : a ≤ max a b := by
  sorry

end LeanWorkshop.Part3
