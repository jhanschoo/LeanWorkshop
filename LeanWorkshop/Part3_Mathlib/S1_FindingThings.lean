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
builds sensitive to future library changes. Also put your goal and hypotheses in `simp` normal
form and `clear` extraneous hypotheses before running `exact?`, `apply?`, or `rw?` so library
search matches Mathlib's canonical lemmas instead of stalling on clutter.
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
| **LeanSearch** | Natural language (v2 Reasoning) | `#leansearch "..."` / `leansearch.net` |
| **LeanExplore** | Hybrid + ecosystem search | `leanexplore.com` (web, Python API, MCP) |
| **Lean Finder** | Proof-state & repo search | `leanfinder.org` / `@leanfinder` on Zulip |
| **Mathlib4 Docs** | API & module browsing | `leanprover-community.github.io/mathlib4_docs` |

- **Loogle** (`https://loogle.lean-lang.org`) supports rich pattern queries such as
  `List ?a → List (List ?a)`.
- **LeanSearch** (`https://leansearch.net`) offers semantic search and a v2 Reasoning mode for
  natural-language prompts like `"sum of first n naturals"`.
- **LeanExplore** (`https://www.leanexplore.com`) searches across `Mathlib`, `Batteries`, `Std`,
  `PhysLean`, and related packages.
- **Lean Finder** (`https://leanfinder.org`) indexes Mathlib4 and GitHub research repos by
  proof state or statement, and runs as `@leanfinder` on Zulip. *(Legacy **Moogle** is no
  longer maintained; prefer the modern search tools above.)*

### Practical Search Workflow Today

In practice, experienced Lean users combine external search with local exploration:
1. **Start with Loogle, LeanSearch, LeanExplore, or Lean Finder:** Use **Loogle** for exact
   type shapes, **LeanSearch** (with v2 Reasoning mode) or **LeanExplore** for natural language
   and downstream packages, and **Lean Finder** for proof-state queries across Mathlib4 and
   GitHub research repos (or `#loogle` / `#leansearch` in-editor via `LeanSearchClient`).
2. **Grep or run `lean_local_search` locally:** Search your `.lake/packages/mathlib` checkout
   (or VS Code `Ctrl+T` / `Cmd+T`). Note that `lean_local_search` (in `lean-lsp-mcp`) resolves
   `@[to_additive]`-generated declarations that raw text grep misses, while reading nearby
   Mathlib lemmas reveals naming conventions and helpers faster than any web engine.
3. **Pair coding agents with Lean's kernel:** Connect an agent via `lean-lsp-mcp` (and
   LeanExplore) to propose candidates, then verify and adapt them inside Lean with `#check`,
   `exact?`, `apply?`, and `rw?`.

---

## 4. Learning Resources, Community, and Ecosystem

### Interactive Tutorials, Playgrounds, and Case Studies

- **Lean Live Playground** (`https://live.lean-lang.org`) — Zero-install browser editor with
  Mathlib preloaded for trying proofs or sharing minimal reproducible examples.
- **Glimpse of Lean** (`https://github.com/PatrickMassot/GlimpseOfLean`) — **Recommended!**
  A concise, hands-on tutorial ("for the impatient") that lets you experience proving
  theorems across logic, analysis, and algebra in just a few hours.
- **The Natural Number Game (NNG4)** (`https://adam.math.hhu.de/#/g/leanprover-community/nng4`) and
  **The Mechanics of Proof** (`https://hrmacbeth.github.io/math2001/`) — Popular introductory
  tutorials for readers still building fluency with formal logic and mathematics.
- **Mathlib Tutorials (`leanprover-community/tutorials`)** — Classic exercise-based repository for
  practicing Mathlib idioms in analysis, topology, and algebra.
- **Case Studies & Statement Design Guides:**
  - **Terence Tao's Lean 4 Proof Tours** — Detailed walkthroughs documenting real-world
    formalization choices, refactoring, and proof engineering in research mathematics.
  - **zkSecurity FRI Post-Mortem** — Concrete lessons from formalizing cryptographic protocols in
    Lean 4, highlighting statement fidelity and engineering trade-offs.
  - **Getting the Statement Right** (`https://robertj1.com`) — A practical six-check guide to
    catching subtle definition mismatches, edge cases, and vacuity bugs in Lean statements.

### Topic Reference Books (Consult by Topic, Not Cover-to-Cover)

It is **not necessarily productive to read these books cover to cover**; instead, consult the
chapters relevant to the topic or technique you are currently using:

- **Mathematics in Lean (MIL)** (`https://leanprover-community.github.io/mathematics_in_lean/`) —
  Idioms for Mathlib's algebraic hierarchy, topology, filters, calculus, and measure theory.
- **Theorem Proving in Lean 4 (TPIL4)** (`https://lean-lang.org/theorem_proving_in_lean4/`) —
  Thorough reference on dependent type theory, inductive types, typeclasses, and tactic basics.
- **Functional Programming in Lean (FPIL)**
  (`https://lean-lang.org/functional_programming_in_lean/`) — Reference when writing computable
  Lean 4 programs, monadic code, or custom tactics and metaprograms.

### Community, Package Index, Tooling, and Projects

- **Lean Zulip (`https://leanprover.zulipchat.com`)** — The **most central community resource** for
  Lean 4. Live Q&A (`#new members`, `#mathlib4`), the `@leanfinder` search bot, library design
  discussions, and formalization coordination all happen here.
- **Reservoir (`https://reservoir.lean-lang.org`)** — The official package index and registry for
  the Lean 4 ecosystem, cataloging libraries, tools, and formalizations beyond Mathlib.
- **Palomar (`https://palomar-registry.org`)** — Public registry ("preprint server") for
  machine-checked Lean 4 formalizations (Lean FRO & ICARM), indexing immutable repository
  snapshots verified via `lake comparator` (`Challenge.lean` vs. `Solution.lean`), independent
  kernel replay, and `formalization.yaml` provenance disclosures.
- **Agentic & Verification Tooling:**
  - **`lean-lsp-mcp`** (`https://github.com/oOo0oOo/lean-lsp-mcp`) — MCP server exposing Lean
    Infoview diagnostics, goal states, and `lean_local_search` (`@[to_additive]` support) to agents.
  - **`lean4-skills`** (`https://github.com/cameronfreer/lean4-skills`) — Reusable Lean 4 and
    Mathlib workflow skills, prompts, and verification checklists for coding agents.
  - **`lake comparator`** (`https://github.com/leanprover/comparator`) — Sandboxed verifier for
    checking theorem-statement and axiom equivalence when auditing formalizations.
  - **Paperproof** — VS Code extension and interactive proof visualizer showing backwards and
    forwards tactic proof structure.
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
  - **Formal Conjectures (`google-deepmind/formal-conjectures`)** — Open-source repository of
    formalized open conjectures in Lean 4, useful for benchmarking and statement style.
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
