# Autoformalization Workflow Guide

This guide accompanies [`S1_StatementTranslation.lean`](S1_StatementTranslation.lean), [`S2_ProofSketching.lean`](S2_ProofSketching.lean), and [`S3_ErrorRecovery.lean`](S3_ErrorRecovery.lean) for multi-stage, non-one-shot AI/agent autoformalization.

---

## 1. The Multi-Stage Autoformalization Workflow

Real formalizations are rarely solved in one shot. Break the work into four compiler-verified stages, revising earlier choices whenever downstream proofs reveal friction:

```text
Informal Problem & Proof (LaTeX / English)
   │
   ▼  [1. Agent-Driven Literature/Library Survey, Architectural Planning & Semantic Audit]
Direct an agent to search `.lake/packages/mathlib`, external Lean 4 repos (Reservoir/Blueprints), & prior ITPs
   │  └─ Have it audit version skew, typeclass compatibility, & style; reuse or translate to Mathlib types.
Core `structure`/`def` (`Def_work` & `Def_paper`) + `namespace` + `section`/`variable` + Main Statement
   │  └─ Run `#check`/boundary checks; flag hard-to-formalize steps & pin `Design Note`s for adapted `Def_work`.
   ▼  [2. Top-Down Theory Outline (`sorry`-Stubbed Lemma Graph & Equivalence Bridges)]
Intermediate `lemma`s on `Def_work` + Bridge (`Def_work ↔ Def_paper`) + Target `theorem` on `Def_paper`
   │  └─ Compiler checks dependency flow, binders, and signatures before helper proofs are written.
   ▼  [3. Incremental Fleshing Out & Statement Revision]
Prove helper lemmas bottom-up; revise signatures when needed (clear denominators, fix binders, `@[simp]`)
   │  └─ Within each lemma, use local `have` blocks and `calc` only where needed to bridge tactics.
   ▼  [4. Post-Proof Semantic Audit, Refactoring & Verification]
Audit final `def`/`theorem` signatures against the informal math, run `#print axioms` & non-vacuity checks.
   │  └─ Refactor long/brittle proofs into helper `lemma`s, replace `exact?`/`simp?`, and verify `lake build`.
```

### Agent-Driven Survey & Using Formalized Libraries Outside Mathlib

Before letting an agent draft definitions in Stage 1, prepare the workspace (`lake exe cache get && lake build` so `.olean` caches exist—with ≥ 16 GB RAM recommended—so LSP/MCP tools like `lean-lsp-mcp` and `lean4-skills` do not stall) and run a **tool-grounded survey** using search/research agents rather than relying on model memory. Agents can grep local sources, browse repositories, and translate cross-language mathematical blueprints in minutes—if you constrain how they read and adapt what they find.

1. **How to direct AI agents to conduct the survey (never rely on model memory alone):**
   - **Local `.lake/packages/mathlib` & LSP index first:** Instruct the agent to follow the practical retrieval hierarchy:
     1. `lean_local_search` (in `lean-lsp-mcp`, resolving `@[to_additive]` names absent from raw `.lean` text) + `rg` over `.lake/packages/mathlib/Mathlib`, `Archive/`, and `Counterexamples/`.
     2. `Loogle` (`--loogle-local` for offline type-pattern / AST queries without rate limits).
     3. Semantic and Zulip/GitHub-trained retrievers (`LeanSearch-v2`, `LeanExplore`, `Lean Finder`—which also indexes external research repos; avoid legacy `Moogle`, which is no longer maintained).
     4. Goal-state premise search (`exact?`, `apply?`, `rw?`, `lean_hammer_premise`) on `simp`-normalized goals after `clear`ing extraneous hypotheses, verified via `#check`/`#synth` against your pinned Mathlib commit (see [`S1_FindingThings.lean`](../Part3_Mathlib/S1_FindingThings.lean)).
   - **External Lean 4 ecosystem (Reservoir, Palomar, GitHub, Blueprints):** Dispatch a web-enabled or research subagent to search **Reservoir** (Lean's package index), **Palomar** (`palomar-registry.org`, the public registry of audited Lean 4 formalizations), GitHub (`language:Lean`), `Lean Finder`, and Blueprint-driven research repos (e.g., *PFR*, *Carleson*, *PrimeNumberTheoremAnd*, *PhysLean*/*HepLean*, *SciLean*). **Practical tip:** Have the agent clone promising external repos into a scratch or `/tmp` folder outside your Lake project so it can grep and read `.lean` files without altering `lakefile.toml`.
   - **Cross-ITP & paper reconnaissance (Lean 3, Isabelle/AFP, Coq/Rocq):** Ask a research subagent to search Isabelle's Archive of Formal Proofs (AFP), Coq/Rocq (`mathcomp`), HOL Light, or unported Lean 3 repos. Coding agents are strong at reading `.thy` or `.v` files and distilling the *mathematical decomposition, inductive invariants, and boundary hypotheses* into a Lean 4 blueprint, even when the original proofs sit in another proof assistant.

2. **Why agents must not blindly import or copy external libraries (Common hazards):**
   - **Toolchain & Mathlib version skew (Outdated):** Left unconstrained, an agent may edit `lakefile.toml` or `lean-toolchain` to add an unmaintained `[[require]]` dependency—breaking the build or pinning your project to an old Mathlib release—or copy stale external files built against deprecated APIs.
   - **Incompatible representations ("API Islands"):** Research repos often define bespoke structures (`MyGraph`, custom metric/matrix records) instead of Mathlib typeclasses (`SimpleGraph`, `PseudoMetricSpace`, `Module`). If an agent copies those definitions verbatim, it strands downstream proofs on an API island ([`S3_ErrorRecovery.lean`](S3_ErrorRecovery.lean)) cut off from Mathlib's `@[simp]` lemmas, `gcongr`, and `fun_prop`.
   - **Bad style, monolithic proofs, and transitive `sorry`s:** Unreviewed paper artifacts frequently contain 200-line brittle tactic scripts, unconstrained `simp` calls, non-standard naming, disabled linters, or hidden `sorry`s. Feeding legacy tactic spaghetti into an agent's context induces it to burn turns patching broken `rw` chains instead of writing clean modular proofs.

3. **How to steer agents when leveraging external libraries:**
   - **Treat external repos as read-only donor blueprints (forbid `lakefile.toml` / `lean-toolchain` edits):** Unless an external package is actively maintained in lockstep with Mathlib, instruct the agent to inspect it in a scratch directory or via web fetch strictly as a **design reference**—never as a new Lake dependency.
   - **Port the statement graph, not the tactic scripts:** Direct the agent to: (a) translate external carrier types and predicates into canonical Mathlib types/typeclasses, (b) extract only the intermediate `lemma` **signatures** as `:= by sorry` stubs to seed Stage 2's outline, and (c) discard legacy tactic scripts and re-prove each lemma from scratch in Stage 3 using modern Mathlib tactics (`grind`, `lia`, `fun_prop`, `positivity`, `gcongr`, `ring`, `linarith`) and naming conventions.
   - **Mandate automated semantic and axiom audits on adapted code:** Require the agent to run small boundary `example` checks ([`S1_StatementTranslation.lean`](S1_StatementTranslation.lean)) and `#print axioms` ([`S3_ErrorRecovery.lean`](S3_ErrorRecovery.lean)) on every adapted definition or theorem so semantic mismatches and hidden `sorry`s fail fast.

### Managing Divergences Between Informal Proofs and Formal Developments

Formalizing a theorem rarely means translating an informal paper step-for-step. Intermediate definitions and lemmas that look routine to experts often need deliberate adaptation—both to become formalizable within scope and to expose edge cases the prose quietly glossed over.

1. **Why formal developments require subtly different definitions and intermediate lemmas:**
   - **Expert-friendly vs. formalization-friendly arguments:** Informal proofs freely use maneuvers that are intuitive to domain experts but disproportionately expensive or out-of-scope to formalize literally—*"without loss of generality, sort and re-index the sum"*, *"perturb slightly into general position"*, *"pass to a limit / apply a density argument"*, or quotient/isomorphism identifications.
   - **Elided tedium and unconscious gaps:** Experts routinely write *"the boundary case is similar"* or *"clearly extends to $k = 0$"* without realizing that rigor demands a strengthened inductive invariant, an explicit slack or guard parameter, or a modified carrier type—or that an intermediate claim in the paper is subtly false at a boundary.

2. **Steering AI agents to the adapted definition/interpretation (preventing "textbook reversion"):**
   - **Beware "canonical reversion":** Because LLMs have strong priors toward textbook definitions and standard proof paths, an unsteered agent will repeatedly "correct" an adapted working definition back into the naive textbook statement, or burn context attempting a 1,500-line literal WLOG/perturbation detour instead of a clean algebraic surrogate.
   - **Ask agents to propose formalization-friendly surrogates in Stages 1–2:** Instruct the agent to flag high-friction informal idioms (WLOG re-indexing, limiting detours, quotient coercions, division guards) and suggest algebraic, inductive, or order-theoretic reformulations that align cleanly with existing Mathlib APIs.
   - **Pin explicit "Intentional Deviation Notes" above adapted declarations:** Whenever your formalization replaces a textbook notion (`Def_paper`) with an adapted working version (`Def_work`) or strengthened invariant, place a prominent comment right above it—e.g.:
     ```lean
     /-! ### Design Note (Intentional Deviation from Informal Proof)
     The paper states this step using division (`|x - x*| ≤ |x - T x| / (1 - c)`), whereas this
     working lemma keeps the cleared-denominator form `(1 - c) * |x - x*| ≤ |x - T x|`.
     Do NOT rewrite this back to the textbook divided form; internal API lemmas rely on this form. -/
     ```
   - **Lock the target header, let the in-Lean lemma DAG evolve, and enforce stuck detection:** Freeze the paper-facing target `theorem` header, stub `Def_work` and intermediate `lemma`s directly inside Lean (rather than locking every intermediate step to a static LaTeX blueprint that bottlenecks fast provers), and apply stuck-detection rules: if a subgoal blocks twice, switch from tactic search to lemma splitting or counterexample refutation.

3. **Communicating differences with the mathematician / domain researcher:**
   - **Translate formal friction into mathematical design questions (not Lean tactic jargon):** Researchers seldom know which informal steps are costly in Mathlib and may not consciously realize an adaptation is needed. Instead of reporting coercion or rewrite failures, ask crisp mathematical questions:
     - *"Assuming $a_1 \le \dots \le a_n$ via WLOG sorting forces permutation bijections through every sum; can we phrase Lemma 3 as a symmetric invariant over unordered pairs instead?"*
     - *"Step 2 divides by $1 - c$ (or $x$); can we carry the cleared-denominator inequality $(1 - c) A \le B$ as our primary inductive invariant?"*
     - *"The proof invokes [Heavy Theorem X] solely to obtain [Property Y]; can we isolate [Property Y] as the intermediate lemma and prove it directly?"*
   - **Surface concrete boundary counterexamples early:** When a naive intermediate lemma fails on a degenerate input ($x = 0$, empty set, non-strict bound), show the researcher the concrete Lean counterexample (`example : ¬ ...`) right away so you can decide together whether to strengthen hypotheses or refine the working definition.

4. **Closing the loop — Proving Equivalence ("The Working-to-Paper Bridge Pattern"):**
   Never leave a formalization proving only an unfamiliar internal reformulation (`Def_work`) when the researcher expects the theorem they recognize (`Def_paper`)—and beware the **`BEq` (`Theorem_work ↔ Theorem_paper`) fallacy**, where any two provable theorems imply each other vacuously regardless of mathematical meaning:
   1. **State both:** Keep `Def_work` (tailored for internal proofs and Mathlib automation) alongside `Def_paper` (matching the informal statement or canonical Mathlib definition as transparently as possible).
   2. **Bridge at the predicate/definition level (`∀ x, Def_work x ↔ Def_paper x`):** Prove equivalence between the definitions or predicates themselves (not between closed, independently proved theorems).
   3. **Prove internally with `Def_work`, deduce `Theorem_paper` directly:** Build the Stage 2–3 lemma graph on `Def_work`, then deduce the exported target `theorem` in terms of `Def_paper` cleanly in a few lines by applying `Theorem_work` and the bridge lemma.

---

## 2. Copy-Paste Prompt Templates

### Template 1: Agent Literature/Library Survey, Architectural Planning & Statement Formalization

> **Prompt:**
> Before writing proofs, conduct a tool-grounded survey and plan the Lean 4 (Mathlib) architecture for the mathematical setup below (do **not** rely on memory for lemma names or edit `lakefile.toml`/`lean-toolchain`):
> - **Mathlib search:** Search `.lake/packages/mathlib` (including `Archive/` and `Counterexamples/`) and verify candidate declarations in Lean with `#check`/`#synth`.
> - **External & cross-ITP survey:** Search external Lean 4 packages (Reservoir, Blueprint repos) and prior formalizations (Lean 3, Isabelle/AFP, Coq/Rocq), inspecting any external repo in a scratch directory without adding Lake dependencies.
> - **Reuse & Adaptation Assessment:** Report what exists in Mathlib, what external work you found, whether external code suffers from version skew, "API island" custom types, or brittle/poor proof style, and how you will reuse or translate definitions and lemma signatures into canonical Mathlib types (discarding legacy tactic scripts).
> - **Informal-to-formal divergence audit:** Flag informal idioms that are hard to formalize literally, out of scope, or subtly underspecified at boundaries (WLOG re-indexing, limiting detours, partial ops, elided invariants). Where helpful, propose a formalization-friendly **working definition/invariant (`Def_work`)** alongside the paper statement (`Def_paper`), and add an in-file `Design Note` explaining why `Def_work` intentionally deviates from the paper so downstream agents do not revert it.
> - **Architecture & Main statement:** Design the core `structure`/`def` anchored to Mathlib types, an accompanying `namespace` for dot notation, a `section` with shared `variable`s, and the target `theorem` ending in `:= by sorry`.
> - **Semantic audit:** Test boundary conventions (`ℕ` subtraction/division, `/ 0`, `Real.sqrt` on negatives, implicit domain hypotheses) with `#check` and sanity `example`s, listing any explicit guards added.

### Template 2: Top-Down Theory Outline (`sorry`-Stubbed Lemma Graph)

> **Prompt:**
> Given the definitions and target `theorem` below, produce a **top-down Lean 4 outline** (without proving the helper lemmas yet):
> - Preserve any `Design Note`-annotated working definitions or invariants (`Def_work`); do **not** revert them to textbook definitions unless explicitly asked.
> - Factor the informal argument into reusable intermediate `lemma`s over `Def_work` inside the module's `namespace` and `section`, each ending in `:= by sorry`, and include an explicit **equivalence / bridge lemma (`Def_work ↔ Def_paper`)** if the internal formulation differs from the exported paper statement.
> - Write a complete proof of the main `theorem` (in terms of `Def_paper` / canonical Mathlib types) using only those stubbed lemmas (plus basic tactics), and verify that the main theorem compiles cleanly with zero errors.
> - Flag any awkward hypotheses (e.g. denominators that can be cleared multiplicatively, missing `@[simp]` lemmas, or explicit vs. implicit binder adjustments).
> - Use Lean 4 syntax only (never Lean 3 `begin ... end` or `λ`).

### Template 3: Incremental Lemma Proof & Statement Revision

> **Prompt:**
> Prove the next unproved `lemma` in the outline below:
> - Prefer short, modular proofs using standard Mathlib tactics (`ring`, `linarith`, `omega`, `lia`, `positivity`, `gcongr`, `fun_prop`, `grind`, `simp`).
> - If proving a helper reveals a clunky signature or unnecessary hypothesis, **propose a statement revision** (e.g., clearing a denominator, strengthening/weakening a hypothesis, or flipping explicit/implicit binders) and update any downstream call sites accordingly.
> - Only use inline `have` blocks inside a lemma when bridging between distinct tactic fragments (e.g. separating an algebraic identity from an inequality step).

### Template 4: Post-Proof Semantic Audit, Refactoring & Verification

> **Prompt:**
> Perform a post-proof audit and cleanup of the Lean 4 development below (ideally in a fresh review pass):
> - **Specification fidelity, elaboration & back-translation check:** Inspect `#check @theorem_name` with `set_option autoImplicit false`, run a blinded `Lean → NL` back-translation of each target `def`/`theorem` to confirm no hypotheses were strengthened or scope narrowed, and verify any `Def_work` carries a `Design Note` plus a predicate-level bridge (`∀ x, Def_work x ↔ Def_paper x`) to `Def_paper`.
> - **Axiom, source-pattern & hypothesis audit:** Run `#print axioms` / `lean_verify` to confirm only `[propext, Classical.choice, Quot.sound]` appear (no `sorryAx`, `unsafe`, `opaque`, `@[implemented_by]`, or `set_option debug.*`), add a non-trivial concrete instantiation `example` for each main theorem, and check the unused-variable linter (`lean_minimal_hypotheses`) so every hypothesis is load-bearing.
> - **Structural refactoring:** Extract sprawling proof blocks into reusable helper `lemma`s inside the module's `namespace`/`section`, replace non-terminal `simp` with `simp only [...]`, and remove search tactics (`exact?`, `apply?`, `simp?`).
> - **Build & style verification:** Run `lake build` to confirm exit code `0`, zero unexpected warnings, and lines ≤ 100 chars (`·` bullets, `fun x ↦ ...`).

---

## 3. Running the Walkthrough

- **Multi-stage walkthrough (`S2_ProofSketching.lean`):**
  - Inspect [`S2_ProofSketching.lean`](S2_ProofSketching.lean) to see how `ContractionMap` progresses from **Stage 1** (`structure ContractionMap`, `namespace ContractionMap`, `IsFixedPt`, `slack`) through **Stages 2–3** (`section BasicAPI`, intermediate lemmas `slack_pos`, `dist_fixed_step`, `slack_mul_dist_le_residual`, and `fixedPt_unique`), including why clearing denominators and making `x` explicit improved the outline.
  - Complete **Exercises 1–3** inside `section BasicAPI` and compare against [`LeanWorkshop/Solutions/Part4_Autoformalization/S2_ProofSketching.lean`](../Solutions/Part4_Autoformalization/S2_ProofSketching.lean).

---

## 4. Six-Step Statement & Proof Validation Checklist

1. **Freeze headers & pin versions:** Lock target `def`/`theorem` headers (verify via `git diff` or the Palomar-style `Challenge.lean` / `Solution.lean` split checked with `lake comparator` and `formalization.yaml` provenance metadata) and pin Lean + Mathlib commits before proving.
2. **Record informal-to-formal deviations & back-translate:** Document adapted `Def_work` choices with `Design Note`s and verify fidelity with blinded `Lean → NL` directional back-translation.
3. **Reuse Mathlib & bridge custom `Def_work` definitions:** Prefer Mathlib's bundled/unbundled APIs; pair any custom `Def_work` with worked examples and a predicate-level equivalence bridge (`∀ x, Def_work x ↔ Def_paper x`, never a closed-theorem `BEq` check), modularized into helper lemmas in a `namespace`/`section`.
4. **Inspect full elaborated type:** Run `#check @theorem_name` with `set_option autoImplicit false` to audit every implicit binder, coercion (`↑`), universe level, and synthesized typeclass instance.
5. **Falsify & rule out triviality/vacuity:** Construct a concrete simultaneous witness for all preconditions, verify existentials (`∃ x, ...`) cannot hold trivially (`0`, `∅`), and add non-trivial sanity/completeness checks.
6. **Audit axioms, banned patterns, hypotheses & style:** Confirm `#print axioms` / `lean_verify` shows only standard axioms (no `sorryAx`, `unsafe`, `opaque`, `@[implemented_by]`, or `set_option debug.*`), verify every hypothesis is used (`lean_minimal_hypotheses`), ensure `lake build` exits `0` with targeted imports (e.g., `Mathlib.Basic.Real.Basic` / `Mathlib.Data.Real.Basic`), lines ≤ 100 chars, `·` bullets, and `fun x ↦ ...`.
