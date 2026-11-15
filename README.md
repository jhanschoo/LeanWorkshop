# LeanWorkshop

An interactive Lean 4 + Mathlib learning repository covering core Lean fundamentals, project organization, Mathlib workflows, and an autoformalization demo.

---

## Prerequisites & Quickstart

1. **Install Lean 4 via `elan`:** Follow the [Lean installation guide](https://lean-lang.org/install/). This repository pins its toolchain in [`lean-toolchain`](lean-toolchain) (`leanprover/lean4:v4.36.0-rc2`).
2. **Install the VS Code extension:** Install **lean4** (`leanprover.lean4`) in VS Code so the Infoview panel and Unicode symbol input (`\` shortcuts) work automatically.
3. **Fetch prebuilt Mathlib oleans & build:**
   ```bash
   lake exe cache get
   lake build
   ```

---

## Workshop Syllabus & Repository Map

### Part 1: Basics (`LeanWorkshop/Part1_Basics/`)
- [`S1_InfoviewAndSymbols.lean`](LeanWorkshop/Part1_Basics/S1_InfoviewAndSymbols.lean) — Using `#check`, `#eval`, `#print`, reading the Infoview, and entering Unicode math symbols.
- [`S2_BasicProofs.lean`](LeanWorkshop/Part1_Basics/S2_BasicProofs.lean) — Term vs. tactic mode, `rfl`, `intro`, `exact`, `apply`, `rw`, `have`, `calc`, logical connectives, `cases`, and `induction`.
- [`S3_SyntaxAndTypes.lean`](LeanWorkshop/Part1_Basics/S3_SyntaxAndTypes.lean) — `Prop` vs. `Type`, `def`/`theorem`/`lemma`/`example`, and explicit `()` / implicit `{}` / typeclass `[]` binders.

### Part 2: Namespaces and Project Organization (`LeanWorkshop/Part2_Organization/`)
- [`S1_NamespacesAndSections.lean`](LeanWorkshop/Part2_Organization/S1_NamespacesAndSections.lean) — `namespace`, `section`, `variable` scoping, `open` variants, and `private`/`protected`.
- `S2_MiniProject/`:
  - [`S1_Defs.lean`](LeanWorkshop/Part2_Organization/S2_MiniProject/S1_Defs.lean) — Core definitions inside a dedicated namespace.
  - [`S2_Lemmas.lean`](LeanWorkshop/Part2_Organization/S2_MiniProject/S2_Lemmas.lean) — API lemmas and `@[simp]` rules importing `S1_Defs`.
- [`S3_ProjectStructure.lean`](LeanWorkshop/Part2_Organization/S3_ProjectStructure.lean) — Module-to-path mapping, `lakefile.toml`, `lean-toolchain`, and `lake-manifest.json`.

### Part 3: Working with Mathlib (`LeanWorkshop/Part3_Mathlib/`)
- [`S1_FindingThings.lean`](LeanWorkshop/Part3_Mathlib/S1_FindingThings.lean) — `exact?`, `apply?`, `rw?`, `simp?`, Loogle, LeanSearch, LeanExplore, and community resources.
- [`S2_Nomenclature.lean`](LeanWorkshop/Part3_Mathlib/S2_Nomenclature.lean) — Capitalization conventions, decoding Mathlib lemma names, structural names vs. eponyms, symbol dictionaries, suffixes, and dot notation.
- [`S3_PowerTactics.lean`](LeanWorkshop/Part3_Mathlib/S3_PowerTactics.lean) — `simp`, `ring`, `abel`, `group`, `linarith`, `omega`, `lia`, `norm_num`, `positivity`, `ext`, `gcongr`, `fun_prop`, `push_neg`, `aesop`, and `grind`.

### Part 4: Autoformalization Demo (`LeanWorkshop/Part4_Autoformalization/`)
- [`S1_StatementTranslation.lean`](LeanWorkshop/Part4_Autoformalization/S1_StatementTranslation.lean) — Natural language / LaTeX to Lean 4 signatures and semantic traps (`ℕ` subtraction/division, coercions).
- [`S2_ProofSketching.lean`](LeanWorkshop/Part4_Autoformalization/S2_ProofSketching.lean) — Outlining and incremental formalization (`structure`, `namespace`, `section`, `sorry`-stubbed helper lemmas, and statement revision) via `ContractionMap`.
- [`S3_ErrorRecovery.lean`](LeanWorkshop/Part4_Autoformalization/S3_ErrorRecovery.lean) — Compiler-in-the-loop repair of common LLM hallucinations and type mismatches.
- [`S4_LiveSandbox.lean`](LeanWorkshop/Part4_Autoformalization/S4_LiveSandbox.lean) — Curated problems ready for live AI/agent autoformalization.
- [`S5_WorkflowGuide.md`](LeanWorkshop/Part4_Autoformalization/S5_WorkflowGuide.md) — Prompt templates and workflow recipes for live demos.

### Solutions (`LeanWorkshop/Solutions/`)
Every exercise file in Parts 1–4 has a corresponding `sorry`-free solution module under [`LeanWorkshop/Solutions/`](LeanWorkshop/Solutions/):
- Part 1: [`S1_InfoviewAndSymbols.lean`](LeanWorkshop/Solutions/Part1_Basics/S1_InfoviewAndSymbols.lean), [`S2_BasicProofs.lean`](LeanWorkshop/Solutions/Part1_Basics/S2_BasicProofs.lean), [`S3_SyntaxAndTypes.lean`](LeanWorkshop/Solutions/Part1_Basics/S3_SyntaxAndTypes.lean)
- Part 2: [`S1_NamespacesAndSections.lean`](LeanWorkshop/Solutions/Part2_Organization/S1_NamespacesAndSections.lean), [`S3_ProjectStructure.lean`](LeanWorkshop/Solutions/Part2_Organization/S3_ProjectStructure.lean)
- Part 3: [`S1_FindingThings.lean`](LeanWorkshop/Solutions/Part3_Mathlib/S1_FindingThings.lean), [`S2_Nomenclature.lean`](LeanWorkshop/Solutions/Part3_Mathlib/S2_Nomenclature.lean), [`S3_PowerTactics.lean`](LeanWorkshop/Solutions/Part3_Mathlib/S3_PowerTactics.lean)
- Part 4: [`S1_StatementTranslation.lean`](LeanWorkshop/Solutions/Part4_Autoformalization/S1_StatementTranslation.lean), [`S2_ProofSketching.lean`](LeanWorkshop/Solutions/Part4_Autoformalization/S2_ProofSketching.lean), [`S3_ErrorRecovery.lean`](LeanWorkshop/Solutions/Part4_Autoformalization/S3_ErrorRecovery.lean), [`S4_LiveSandbox.lean`](LeanWorkshop/Solutions/Part4_Autoformalization/S4_LiveSandbox.lean)

All modules are imported from the root barrel file [`LeanWorkshop.lean`](LeanWorkshop.lean).

---

## Community Resources & Tutorials

- **Books & Interactive Tutorials**
  - [*Mathematics in Lean*](https://leanprover-community.github.io/mathematics_in_lean/) — Hands-on introduction to proving mathematics with Mathlib.
  - [*Theorem Proving in Lean 4*](https://lean-lang.org/theorem_proving_in_lean4/) — Official guide to Lean 4's type theory and tactic language.
  - [*The Natural Number Game*](https://adam.math.hhu.de/#/g/leanprover-community/nng4) — Browser-based interactive introduction to Lean tactics.
- **Search & Documentation**
  - [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/) — Browsable API docs for all of Mathlib.
  - [Loogle](https://loogle.lean-lang.org/) — Type- and pattern-based search across Lean & Mathlib.
  - [Moogle](https://www.moogle.ai/) & [LeanSearch](https://leansearch.net/) — Natural-language semantic search for Mathlib theorems.
  - [Lean Reservoir](https://reservoir.lean-lang.org/) — Index of Lean 4 packages and projects.
- **Community**
  - [Lean Zulip Chat](https://leanprover.zulipchat.com/) — Main community forum (especially `#new members` and `#mathlib4`).
