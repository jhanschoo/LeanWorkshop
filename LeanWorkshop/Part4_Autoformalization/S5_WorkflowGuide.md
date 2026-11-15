# Autoformalization Workflow Guide (Live Demo Recipes)

This guide accompanies [`S2_ProofSketching.lean`](S2_ProofSketching.lean) and [`S4_LiveSandbox.lean`](S4_LiveSandbox.lean) for multi-stage, non-one-shot AI/agent autoformalization.

---

## 1. The Multi-Stage Autoformalization Workflow

Real formalizations are rarely solved in one shot. Break the work into four compiler-verified stages, revising earlier choices whenever downstream proofs reveal friction:

```text
Informal Problem & Proof (LaTeX / English)
   │
   ▼  [1. Architectural Planning & Semantic Audit]
Core `structure`/`def` + `namespace` + `section`/`variable` + Main Statement
   │  └─ Audit Mathlib definitions for totalization/junk values (`F12`, `#check`, boundary checks).
   ▼  [2. Top-Down Theory Outline (`sorry`-Stubbed Lemma Graph)]
Intermediate `lemma`s (`:= by sorry`) + Target `theorem` proved from those lemmas
   │  └─ Compiler checks dependency flow, binders, and signatures before helper proofs are written.
   ▼  [3. Incremental Fleshing Out & Statement Revision]
Prove helper lemmas bottom-up; revise signatures when needed (clear denominators, fix binders, `@[simp]`)
   │  └─ Within each lemma, use local `have` blocks and `calc` only where needed to bridge tactics.
   ▼  [4. Compiler-in-the-Loop Repair & Linter Polish]
Diagnose errors from Infoview states, replace search tactics (`exact?`/`simp?`), verify `lake build`
```

---

## 2. Copy-Paste Prompt Templates

### Template 1: Architectural Planning & Statement Formalization

> **Prompt:**
> Plan the Lean 4 (Mathlib) formalization architecture for the mathematical setup below before writing proofs:
> - Design the core `structure` or `def` definitions, an accompanying `namespace` for dot notation, and a `section` with shared `variable`s.
> - Formalize the target `theorem` signature ending in `:= by sorry`.
> - Audit every Mathlib operation used for totalization or boundary conventions (`ℕ` subtraction/division, `/ 0`, `Real.sqrt` on negatives, implicit domain hypotheses) and list any explicit guards added.
> - Use Lean 4 syntax only (never Lean 3 `begin ... end` or `λ`).

### Template 2: Top-Down Theory Outline (`sorry`-Stubbed Lemma Graph)

> **Prompt:**
> Given the definitions and target `theorem` below, produce a **top-down Lean 4 outline** (without proving the helper lemmas yet):
> - Factor the informal argument into reusable intermediate `lemma`s inside the module's `namespace` and `section`, each ending in `:= by sorry`.
> - Write a complete proof of the main `theorem` using only those stubbed lemmas (plus basic tactics), and verify that the main theorem compiles cleanly with zero errors.
> - Flag any awkward hypotheses (e.g. denominators that can be cleared multiplicatively, missing `@[simp]` lemmas, or explicit vs. implicit binder adjustments).

### Template 3: Incremental Lemma Proof & Statement Revision

> **Prompt:**
> Prove the next unproved `lemma` in the outline below:
> - Prefer short, modular proofs using standard Mathlib tactics (`ring`, `linarith`, `omega`, `lia`, `positivity`, `gcongr`, `fun_prop`, `grind`, `simp`).
> - If proving a helper reveals a clunky signature or unnecessary hypothesis, **propose a statement revision** (e.g., clearing a denominator, strengthening/weakening a hypothesis, or flipping explicit/implicit binders) and update any downstream call sites accordingly.
> - Only use inline `have` blocks inside a lemma when bridging between distinct tactic fragments (e.g. separating an algebraic identity from an inequality step).

### Template 4: Compiler-in-the-Loop Error Recovery

> **Prompt:**
> The Lean 4 proof below failed with the following compiler diagnostics and Infoview goal state.
> - Repair the proof **without weakening the `theorem` statement** (only revise helper lemma signatures if clearly beneficial and consistent with the mathematical goal).
> - Prefer standard Mathlib tactics or search tactics (`exact?`, `apply?`, `rw?`, `simp?`) over guessing unverified lemma names.
> - Follow Mathlib formatting (`·` bullets, `fun x ↦ ...`, line length ≤ 100 chars).

---

## 3. Running the Walkthrough & Live Sandbox

1. **Multi-stage walkthrough (`S2_ProofSketching.lean`):**
   - Inspect [`S2_ProofSketching.lean`](S2_ProofSketching.lean) to see how `ContractionMap` progresses from **Stage 1** (`structure ContractionMap`, `namespace ContractionMap`, `IsFixedPt`, `slack`) through **Stages 2–3** (`section BasicAPI`, intermediate lemmas `slack_pos`, `dist_fixed_step`, `slack_mul_dist_le_residual`, and `fixedPt_unique`), including why clearing denominators and making `x` explicit improved the outline.
   - Complete **Exercises 1–3** inside `section BasicAPI` and compare against [`LeanWorkshop/Solutions/Part4_Autoformalization/S2_ProofSketching.lean`](../Solutions/Part4_Autoformalization/S2_ProofSketching.lean).
2. **Live Sandbox (`S4_LiveSandbox.lean`):**
   - Open [`S4_LiveSandbox.lean`](S4_LiveSandbox.lean) alongside the Lean 4 Infoview (`Ctrl+Shift+Enter` / `Cmd+Shift+Enter` in VS Code) and walk through **Challenges 1–4**:
     - **Challenge 1 (`challenge1_consecutive_squares`):** `ring` after verifying the statement uses `ℤ` (avoiding `ℕ` subtraction truncation).
     - **Challenge 2 (`challenge2_weighted_average`):** Splitting nonlinear steps (`w * (b - a) ≥ 0` via `mul_nonneg`) from linear combination (`linarith`).
     - **Challenge 3 (`challenge3_gauss_sum`):** `induction n with | zero => ... | succ k ih => ...` combined with `rw [sumUpTo]` and `ring`.
     - **Challenge 4 (`challenge4_cauchy_schwarz_2d`):** Factoring Lagrange's identity as a helper step before concluding with `sq_nonneg` and `linarith`.
   - Compare live proofs against [`LeanWorkshop/Solutions/Part4_Autoformalization/S4_LiveSandbox.lean`](../Solutions/Part4_Autoformalization/S4_LiveSandbox.lean).

---

## 4. Checklist Before Committing Formalized Code

- [ ] `lake build` exits with code `0` and no unexpected warnings.
- [ ] Every target theorem and helper lemma is free of `sorry` (`admit` / `exact?` / `simp?` replaced with concrete terms).
- [ ] Helper lemmas live in an appropriate `namespace` / `section` with clean binders and `@[simp]` tags where useful (rather than sprawling single-theorem scripts).
- [ ] Imports are targeted (no barrel `import Mathlib.Tactic`; use `Mathlib.Basic.Real.Basic` for `ℝ`).
- [ ] Lines are ≤ 100 characters, bullets use `·`, lambdas use `fun x ↦ ...`, and no unused hypotheses remain.
