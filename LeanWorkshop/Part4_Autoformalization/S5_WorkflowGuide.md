# Autoformalization Workflow Guide (Live Demo Recipes)

This guide accompanies [`S4_LiveSandbox.lean`](S4_LiveSandbox.lean) for live AI/agent autoformalization demos.

## Overview: Compiler-in-the-Loop Autoformalization

1. **Formalize the statement first** and sanity-check that it captures the true mathematical meaning (avoiding vacuous hypotheses or `ℕ` truncation/division pitfalls).
2. **Draft a structured proof sketch** using `have ... := by sorry` steps so the Lean compiler checks that the high-level argument closes the goal.
3. **Discharge and repair subgoals iteratively** using Lean compiler diagnostics, Infoview goal states, and search tactics (`exact?`, `apply?`, `rw?`, `simp?`).

---

## Stage 1 Prompt Template: Statement Formalization & Semantic Sanity Check

> **Prompt:**
> Translate the following informal mathematical statement into Lean 4 (compatible with Mathlib).
> - Make all domain assumptions explicit (e.g., `ℝ` vs `ℕ`, positivity, non-zero denominators, finite sets).
> - Avoid unintended `ℕ` truncated subtraction (`a - b`) or integer division (`a / b`) unless the problem is genuinely over `ℕ`.
> - Output only a `theorem` signature ending in `:= by sorry` and briefly explain any implicit assumptions you made explicit.

---

## Stage 2 Prompt Template: Structured Proof Sketch (`have ... := by sorry`)

> **Prompt:**
> Given the informal proof and Lean 4 `theorem` signature below, write a structured Lean 4 proof skeleton:
> - Break the informal argument into sequential `have` steps (`have h₁ : ... := by sorry`).
> - Close the main goal using the `have` hypotheses so that the outer proof structure compiles (with `sorry` only inside the `have` subgoals).
> - Do not invent Mathlib lemma names you are unsure about.

---

## Stage 3 Prompt Template: Subgoal Repair via Lean Diagnostics

> **Prompt:**
> The following Lean 4 proof failed with the compiler diagnostics and Infoview goal state below.
> - Fix the error without altering the theorem statement.
> - Prefer standard Mathlib tactics (`ring`, `linarith`, `nlinarith`, `omega`, `positivity`, `norm_num`, `simp`, `aesop`, `gcongr`) or search placeholders (`exact?`, `apply?`) over guessing obscure lemma names.
