# Autoformalization Workflow Guide (Live Demo Recipes)

This guide accompanies [`S4_LiveSandbox.lean`](S4_LiveSandbox.lean) for live AI/agent autoformalization demos.

---

## 1. The Compiler-in-the-Loop Autoformalization Workflow

```text
Informal Problem (LaTeX / English)
   │
   ▼  [1. Statement Translation]
Lean 4 Signature (`theorem ... := by sorry`)
   │  └─ Sanity check: Are `ℕ` subtraction/division or missing hypotheses avoided?
   ▼  [2. Draft, Sketch, Prove]
Proof Skeleton (`have h₁ : ... := by sorry`, outer proof closes goal)
   │  └─ Compiler confirms the high-level logic is sound before details are proved.
   ▼  [3. Subgoal Automation & Error Recovery]
Automated Tactics (`ring`, `linarith`, `omega`, `positivity`, `gcongr`, `aesop`)
   │  └─ Feed exact compiler errors + Infoview goal states back into the repair loop.
   ▼  [4. Linter & Build Check]
Clean Module (`lake build` passes, zero `sorry`s, ≤ 100 chars/line)
```

---

## 2. Copy-Paste Prompt Templates

### Template 1: Statement Formalization & Semantic Sanity Check

> **Prompt:**
> Translate the following informal mathematical statement into Lean 4 (compatible with Mathlib).
> - Make all domain assumptions explicit (`ℝ` vs `ℤ` vs `ℕ`, positivity, non-zero denominators, primality).
> - Avoid unintended `ℕ` truncated subtraction (`a - b`) or integer division (`a / b`) unless the problem genuinely concerns natural numbers.
> - Use Lean 4 syntax only (never Lean 3 `begin ... end` or `λ`).
> - Output a single `theorem` signature ending in `:= by sorry` and list any implicit assumptions you made explicit.

### Template 2: Draft-Sketch-Prove (DSP) Skeleton

> **Prompt:**
> Given the informal proof and Lean 4 `theorem` signature below, write a structured Lean 4 proof sketch:
> - Break the informal argument into sequential `have` steps (`have h1 : ... := by sorry`).
> - Wire the `have` hypotheses together so the outer theorem compiles with zero errors (leaving `sorry` only inside the `have` subgoals).
> - Do not guess or invent Mathlib lemma names you have not verified.

### Template 3: Compiler-in-the-Loop Error Recovery

> **Prompt:**
> The Lean 4 proof below failed with the following compiler diagnostics and Infoview goal state.
> - Repair the proof **without changing the `theorem` statement**.
> - Prefer standard Mathlib tactics (`ring`, `linarith`, `omega`, `positivity`, `norm_num`, `gcongr`, `simp`, `aesop`) or search tactics (`exact?`, `apply?`, `rw?`, `simp?`) over guessing obscure lemma names.
> - Follow Mathlib formatting (`·` bullets, `fun x ↦ ...`, line length ≤ 100 chars).

---

## 3. Running the Live Demo in `S4_LiveSandbox.lean`

1. Open [`S4_LiveSandbox.lean`](S4_LiveSandbox.lean) alongside the Lean 4 Infoview (`Ctrl+Shift+Enter` / `Cmd+Shift+Enter` in VS Code).
2. Walk through **Challenges 1–4** in order:
   - **Challenge 1 (`challenge1_consecutive_squares`):** Show how `ring` immediately closes algebraic polynomial identities after verifying the statement uses `ℤ` (avoiding `ℕ` subtraction truncation).
   - **Challenge 2 (`challenge2_weighted_average`):** Demonstrate splitting nonlinear steps (`w * (b - a) ≥ 0` via `mul_nonneg`) from linear combination (`linarith`).
   - **Challenge 3 (`challenge3_gauss_sum`):** Show `induction n with | zero => ... | succ k ih => ...` combined with `rw [sumUpTo]` and `ring`.
   - **Challenge 4 (`challenge4_cauchy_schwarz_2d`):** Demonstrate the full **Draft, Sketch, Prove** loop—first write `have h_id : ... := by sorry` and `have h_sq : ... := by sorry`, verify `linarith` closes the main goal, and then fill in `ring` and `sq_nonneg`.
3. Compare your live proofs against [`LeanWorkshop/Solutions/Part4_Autoformalization/S4_LiveSandbox.lean`](../Solutions/Part4_Autoformalization/S4_LiveSandbox.lean).

---

## 4. Checklist Before Committing Formalized Code

- [ ] `lake build` exits with code `0` and no unexpected warnings.
- [ ] Every target theorem is free of `sorry` (`admit` / `exact?` / `simp?` replaced with concrete terms).
- [ ] Imports are targeted (no barrel `import Mathlib.Tactic`; use `Mathlib.Basic.Real.Basic` for `ℝ`).
- [ ] Lines are ≤ 100 characters, bullets use `·`, lambdas use `fun x ↦ ...`, and no unused hypotheses remain.
