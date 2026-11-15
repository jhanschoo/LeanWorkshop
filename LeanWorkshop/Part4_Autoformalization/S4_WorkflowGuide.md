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
Core `structure`/`def` + `namespace` + `section`/`variable` + Main Statement
   │  └─ Run `#check`/boundary checks on Mathlib & adapted definitions (`F12`, totalization/junk values).
   ▼  [2. Top-Down Theory Outline (`sorry`-Stubbed Lemma Graph)]
Intermediate `lemma`s (`:= by sorry`) + Target `theorem` proved from those lemmas
   │  └─ Compiler checks dependency flow, binders, and signatures before helper proofs are written.
   ▼  [3. Incremental Fleshing Out & Statement Revision]
Prove helper lemmas bottom-up; revise signatures when needed (clear denominators, fix binders, `@[simp]`)
   │  └─ Within each lemma, use local `have` blocks and `calc` only where needed to bridge tactics.
   ▼  [4. Post-Proof Semantic Audit, Refactoring & Verification]
Audit final `def`/`theorem` signatures against the informal math, run `#print axioms` & non-vacuity checks.
   │  └─ Refactor long/brittle proofs into helper `lemma`s, replace `exact?`/`simp?`, and verify `lake build`.
```

### Agent-Driven Survey & Using Formalized Libraries Outside Mathlib

Before letting an agent draft definitions in Stage 1, run a **tool-grounded survey** using search/research agents rather than relying on the model's parametric memory. Agents can grep local sources, browse repositories, and translate cross-language mathematical blueprints in minutes—if you constrain how they read and adapt what they find.

1. **How to direct AI agents to conduct the survey (never rely on model memory alone):**
   - **Local `.lake/packages/mathlib` & Lean environment first:** Instruct the agent to search `.lake/packages/mathlib/Mathlib` directly (e.g. with `rg`), inspect `Archive/` and `Counterexamples/`, and verify candidate declarations via `#check`/`#synth` (or Loogle MCP tools) against your project's *pinned* Mathlib commit rather than guessing names from training data (see [`S1_FindingThings.lean`](../Part3_Mathlib/S1_FindingThings.lean)).
   - **External Lean 4 ecosystem (Reservoir, GitHub, Blueprints):** Dispatch a web-enabled or research subagent to search **Reservoir** (Lean's package index), GitHub (`language:Lean`), and Blueprint-driven research repos (e.g., *PFR*, *Carleson*, *PrimeNumberTheoremAnd*, *PhysLean*/*HepLean*, *SciLean*). **Practical tip:** Have the agent clone promising external repos into a scratch or `/tmp` folder outside your Lake project so it can grep and read `.lean` files without altering `lakefile.toml`.
   - **Cross-ITP & paper reconnaissance (Lean 3, Isabelle/AFP, Coq/Rocq):** Ask a research subagent to search Isabelle's Archive of Formal Proofs (AFP), Coq/Rocq (`mathcomp`), HOL Light, or unported Lean 3 repos. Coding agents are strong at reading `.thy` or `.v` files and distilling the *mathematical decomposition, inductive invariants, and boundary hypotheses* into a Lean 4 blueprint, even when the original proofs sit in another proof assistant.

2. **Why agents must not blindly import or copy external libraries (Common hazards):**
   - **Toolchain & Mathlib version skew (Outdated):** Left unconstrained, an agent may edit `lakefile.toml` or `lean-toolchain` to add an unmaintained `[[require]]` dependency—breaking the build or pinning your project to an old Mathlib release—or copy stale external files built against deprecated APIs.
   - **Incompatible representations ("API Islands"):** Research repos often define bespoke structures (`MyGraph`, custom metric/matrix records) instead of Mathlib typeclasses (`SimpleGraph`, `PseudoMetricSpace`, `Module`). If an agent copies those definitions verbatim, it strands downstream proofs on an API island ([`S3_ErrorRecovery.lean`](S3_ErrorRecovery.lean)) cut off from Mathlib's `@[simp]` lemmas, `gcongr`, and `fun_prop`.
   - **Bad style, monolithic proofs, and transitive `sorry`s:** Unreviewed paper artifacts frequently contain 200-line brittle tactic scripts, unconstrained `simp` calls, non-standard naming, disabled linters, or hidden `sorry`s. Feeding legacy tactic spaghetti into an agent's context induces it to burn turns patching broken `rw` chains instead of writing clean modular proofs.

3. **How to steer agents when leveraging external libraries:**
   - **Treat external repos as read-only donor blueprints (forbid `lakefile.toml` / `lean-toolchain` edits):** Unless an external package is actively maintained in lockstep with Mathlib, instruct the agent to inspect it in a scratch directory or via web fetch strictly as a **design reference**—never as a new Lake dependency.
   - **Port the statement graph, not the tactic scripts:** Direct the agent to: (a) translate external carrier types and predicates into canonical Mathlib types/typeclasses, (b) extract only the intermediate `lemma` **signatures** as `:= by sorry` stubs to seed Stage 2's outline, and (c) discard legacy tactic scripts and re-prove each lemma from scratch in Stage 3 using modern Mathlib tactics (`grind`, `lia`, `fun_prop`, `positivity`, `gcongr`, `ring`, `linarith`) and naming conventions.
   - **Mandate automated semantic and axiom audits on adapted code:** Require the agent to run small boundary `example` checks ([`S1_StatementTranslation.lean`](S1_StatementTranslation.lean)) and `#print axioms` ([`S3_ErrorRecovery.lean`](S3_ErrorRecovery.lean)) on every adapted definition or theorem so semantic mismatches and hidden `sorry`s fail fast.

---

## 2. Copy-Paste Prompt Templates

### Template 1: Agent Literature/Library Survey, Architectural Planning & Statement Formalization

> **Prompt:**
> Before writing proofs, conduct a tool-grounded survey and plan the Lean 4 (Mathlib) architecture for the mathematical setup below (do **not** rely on memory for lemma names or edit `lakefile.toml`/`lean-toolchain`):
> - **Mathlib search:** Search `.lake/packages/mathlib` (including `Archive/` and `Counterexamples/`) and verify candidate declarations in Lean with `#check`/`#synth`.
> - **External & cross-ITP survey:** Search external Lean 4 packages (Reservoir, Blueprint repos) and prior formalizations (Lean 3, Isabelle/AFP, Coq/Rocq), inspecting any external repo in a scratch directory without adding Lake dependencies.
> - **Reuse & Adaptation Assessment:** Report what exists in Mathlib, what external work you found, whether external code suffers from version skew, "API island" custom types, or brittle/poor proof style, and how you will reuse or translate definitions and lemma signatures into canonical Mathlib types (discarding legacy tactic scripts).
> - **Architecture & Main statement:** Design the core `structure`/`def` anchored to Mathlib types, an accompanying `namespace` for dot notation, a `section` with shared `variable`s, and the target `theorem` ending in `:= by sorry`.
> - **Semantic audit:** Test boundary conventions (`ℕ` subtraction/division, `/ 0`, `Real.sqrt` on negatives, implicit domain hypotheses) with `#check` and sanity `example`s, listing any explicit guards added.

### Template 2: Top-Down Theory Outline (`sorry`-Stubbed Lemma Graph)

> **Prompt:**
> Given the definitions and target `theorem` below, produce a **top-down Lean 4 outline** (without proving the helper lemmas yet):
> - Factor the informal argument into reusable intermediate `lemma`s inside the module's `namespace` and `section`, each ending in `:= by sorry`.
> - Write a complete proof of the main `theorem` using only those stubbed lemmas (plus basic tactics), and verify that the main theorem compiles cleanly with zero errors.
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
> - **Specification fidelity check:** Diff final `def` and `theorem` signatures against the informal problem statement to verify no hypotheses were strengthened or conclusions weakened during proving.
> - **Axiom & non-vacuity audit:** Run `#print axioms` on target theorems to confirm only standard axioms (`propext`, `Classical.choice`, `Quot.sound`) appear, and add a concrete instantiation `example` for each main theorem.
> - **Structural refactoring:** Extract sprawling proof blocks into reusable helper `lemma`s inside the module's `namespace`/`section`, replace non-terminal `simp` with `simp only [...]`, and remove search tactics (`exact?`, `apply?`, `simp?`).
> - **Build & style verification:** Run `lake build` to confirm exit code `0`, zero unexpected warnings, and lines ≤ 100 chars (`·` bullets, `fun x ↦ ...`).

---

## 3. Running the Walkthrough

- **Multi-stage walkthrough (`S2_ProofSketching.lean`):**
  - Inspect [`S2_ProofSketching.lean`](S2_ProofSketching.lean) to see how `ContractionMap` progresses from **Stage 1** (`structure ContractionMap`, `namespace ContractionMap`, `IsFixedPt`, `slack`) through **Stages 2–3** (`section BasicAPI`, intermediate lemmas `slack_pos`, `dist_fixed_step`, `slack_mul_dist_le_residual`, and `fixedPt_unique`), including why clearing denominators and making `x` explicit improved the outline.
  - Complete **Exercises 1–3** inside `section BasicAPI` and compare against [`LeanWorkshop/Solutions/Part4_Autoformalization/S2_ProofSketching.lean`](../Solutions/Part4_Autoformalization/S2_ProofSketching.lean).

---

## 4. Checklist Before Committing Formalized Code

- [ ] `lake build` exits with code `0` and no unexpected warnings.
- [ ] Every target theorem and helper lemma is free of `sorry` (`admit` / `exact?` / `simp?` replaced with concrete terms).
- [ ] Any definitions or lemmas adapted from external libraries are translated to canonical Mathlib types/naming conventions, refactored into short modular proofs, and verified with `#print axioms`.
- [ ] Helper lemmas live in an appropriate `namespace` / `section` with clean binders and `@[simp]` tags where useful (rather than sprawling single-theorem scripts).
- [ ] Imports are targeted (no barrel `import Mathlib.Tactic`; use `Mathlib.Data.Real.Basic` for `ℝ`).
- [ ] Lines are ≤ 100 characters, bullets use `·`, lambdas use `fun x ↦ ...`, and no unused hypotheses remain.
