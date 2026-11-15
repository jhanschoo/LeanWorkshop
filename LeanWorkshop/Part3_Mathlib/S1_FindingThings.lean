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

## 3. Searching Mathlib and External Libraries

When the lemma you need is not yet imported in your file—or you only know its mathematical idea—use
these search tools:

| Tool | Best For | Usage & Example |
| :--- | :--- | :--- |
| **Loogle** | Type / pattern search | `#loogle` / `loogle.lean-lang.org` (`?a + ?b = ?b + ?a`) |
| **LeanSearch** | Natural language | `#leansearch "..."` / `leansearch.net` |
| **LeanExplore** | Hybrid + ecosystem search | `leanexplore.com` (web, Python API, MCP) |
| **Mathlib4 Docs** | API & module browsing | `leanprover-community.github.io/mathlib4_docs` |

- **Loogle** (`https://loogle.lean-lang.org`) supports rich pattern queries such as
  `List ?a → List (List ?a)`.
- **LeanSearch** (`https://leansearch.net`) answers natural-language prompts like
  `"sum of first n naturals"`.
- **LeanExplore** (`https://www.leanexplore.com`) searches across `Mathlib`, `Batteries`, `Std`,
  `PhysLean`, and related packages.

### Practical Search Workflow Today

In practice, experienced Lean users combine external search with local exploration:
1. **Start with Loogle or LeanSearch / LeanExplore:** Use **Loogle** when you know the rough type
   shape or constants involved, and **LeanSearch** or **LeanExplore** when you only have a
   natural-language description (or want to search across downstream libraries beyond Mathlib).
   You can also invoke `#loogle` and `#leansearch "..."` directly in-editor when `LeanSearchClient`
   is available.
2. **Grep your local `.lake/packages/mathlib` checkout** (or use VS Code workspace symbol search
   `Ctrl+T` / `Cmd+T`): reading neighboring lemmas in the same Mathlib file often reveals naming
   conventions and helper theorems faster than any web engine.
3. **Pair LLMs / coding agents with Lean's kernel:** Ask an LLM (or an agent connected via MCP to
   LeanExplore / local grep) to suggest candidate Mathlib names, then verify and adapt them inside
   Lean with `#check`, `exact?`, `apply?`, and `rw?`.

---

## 4. Learning Resources, Community, and Ecosystem

### Interactive Tutorials (Where to Start)

- **Glimpse of Lean** (`https://github.com/PatrickMassot/GlimpseOfLean`) — **Recommended!**
  A concise, hands-on tutorial ("for the impatient") that lets you experience proving
  theorems across logic, analysis, and algebra in just a few hours.
- **The Natural Number Game (NNG4)** (`https://adam.math.hhu.de/#/g/leanprover-community/nng4`) and
  **The Mechanics of Proof** (Heather Macbeth) — Both are popular tutorials, targeted at people
  still somewhat fresh to logic and mathematics.

### Topic Reference Books (Consult by Topic, Not Cover-to-Cover)

It is **not necessarily productive to read these books cover to cover**; instead, consult the
chapters relevant to the topic or technique you are currently using:

- **Mathematics in Lean (MIL)** (`leanprover-community/mathematics_in_lean`) — Hands-on idioms for
  working with Mathlib's algebraic hierarchy, topology, filters, calculus, and measure theory.
- **Theorem Proving in Lean 4 (TPIL4)** — Thorough reference on dependent type theory foundations,
  inductive types, typeclasses, and tactic basics.
- **Functional Programming in Lean (FPIL)** — Reference when writing computable Lean 4 programs,
  monadic code, or custom tactics and metaprograms.

### Community, Package Index, and Prominent Projects

- **Lean Zulip (`https://leanprover.zulipchat.com`)** — The **most central community resource** for
  Lean 4. Live Q&A (`#new members`, `#mathlib4`), library design discussions, and formalization
  project coordination all happen here.
- **Reservoir (`https://reservoir.lean-lang.org`)** — The official package index and registry for
  the Lean 4 ecosystem, cataloging libraries, tools, and formalizations beyond Mathlib.
- **Prominent Lean 4 Formalization Projects & Blueprints:** Large collaborative efforts coordinate
  on Zulip and commonly use **Lean Blueprints** (`leanblueprint`) to connect human-readable LaTeX
  proofs and dependency graphs directly to verified Lean declarations. Notable examples include:
  - **Polynomial Freiman–Ruzsa (`teorth/pfr`)** — Terence Tao and collaborators' rapid collaborative
    formalization in additive combinatorics.
  - **Fermat's Last Theorem (`ImperialCollegeLondon/FLT`)** — Ongoing multi-year project led by
    Kevin Buzzard to formalize the modern proof of FLT.
  - **Carleson (`leanprover-community/carleson`)** — Collaborative formalization of Carleson's
    theorem in harmonic analysis.
  - **PrimeNumberTheoremAnd (`AlexKontorovich/PrimeNumberTheoremAnd`)** — Formalization of the
    Prime Number Theorem with classical error terms and analytic number theory.
  - **Domain Libraries (e.g., `PhysLean`, `SciLean`, `Cslib`)** — Ecosystem packages for physics,
    scientific computing, and computer science discoverable on Reservoir.

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
