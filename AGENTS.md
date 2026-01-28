# AGENTS_proof.md

You are a code agent working within the local Lean4 + mathlib project `formal_lean_datasets/`.
Your core task in the **proof pipeline** is: given Lean declaration skeletons that already exist (with `sorry` placeholders), **fill in the proofs** so that the target file passes Lean compilation.

All general conventions (file layout, mathlib reuse, etc.) mirror the statement pipeline, with the following emphasis for proofs.

## 1. File and Namespace Layout

- Dataset name and problem id corresponds to the file:
  - `FormalLeanDatasets/<dataset_name>/<problem_id>.lean`
  - Example: Problem 19 of FATEH dataset is at `FormalLeanDatasets/FATEH/Problem019.lean`

## 2. Your Job for a formal statement

- Locate the existing declaration(s) in the corresponding file.
- **Replace `sorry` with Lean proofs**, pushing as far as possible.
  - If you are conceptually blocked and request re-planning, you may leave small, well-scoped `sorry`, but the file must still compile (no Lean errors other than explicit `sorry`).
  - If you hand off to the fixer, remove all `sorry`; only minor compile errors (typos/imports) may remain.
- Only modify the proof corresponding to the provided `content`; leave other proofs/declarations untouched.
- **Do not modify any given statement** (the declaration header/signature of an existing `theorem`/`lemma`/`def`/`instance`/`class`): no changing binders, types, or goals. If the statement appears malformed or inconsistent, do not “fix” it; instead keep the file compilable (using scoped `sorry` only when requesting re-plan) and report the issue clearly in the agent feedback/logs.
- The orchestrator checks with:

```bash
lake env lean FormalLeanDatasets/<dataset_name>/<problem_id>.lean
```

## 3. Mathlib and Naming

- Prefer using existing mathlib lemmas/definitions; do not reintroduce concepts already in mathlib.
- If the informal's notion matches mathlib’s, lean on the mathlib definition and prove equivalence/instances as needed.
- Use mathematically meaningful names; avoid problem-specific or ad-hoc names unless already present in the skeleton.

## 4. Proof Style and Constraints

- Aim for complete proofs; if blocked, leave structured, minimal `sorry` and keep the file compiling.
- Keep edits minimal: do not delete comments or change labels.
- Do not add unrelated declarations. Do not adjust statements.
- Prefer decomposing long proofs into multiple helper lemmas so each declaration stays reasonably short. Make helper lemmas as general and reusable as possible, and add concise, informative comments above them to make later reuse easy.
- Avoid heavy commands (`lake build`); compilation checks are performed by the orchestrator with `lake env lean <file>`.

## 5. Tooling Strategy

- Rely on Lean LSP (via `lean-lsp-mcp`) for diagnostics, goals, and completions. If Lean LSP tool is timed out or unresponsive, fall back to `lake env lean <file>` immediately for compilation checks.
- Use `lake env lean <file>` sparingly as a final check; do **not** call `lake build`.

## Performance and Execution Strategy (Lean Server Lifecycle)

In this project, you must rely heavily on the **long-lived Lean LSP server** (via `lean-lsp-mcp`) rather than frequently restarting Lean via the command line.

Specific Requirements:

1.  **Keep Lean Server Resident**
    *   Let the Lean LSP server started by `lean-lsp-mcp` run as persistently as possible.
    *   Your interactions with Lean (checking goals, types, errors, completions, etc.) should be prioritized through LSP + MCP tools, not by repeatedly restarting Lean via external commands.

2.  **Diagnostics First: Debug with MCP Tools**
    *   After inserting/modifying a Lean declaration in a file, you should prioritize:
        *   Using tools like `diagnostics`, `local_search`, or `completions` provided by `lean-lsp-mcp` to check for errors and type information.
        *   Fixing errors within the same Lean session until the LSP diagnostics report no errors.
    *   This step is the "inner loop" and should be performed repeatedly **without exiting the Lean server**.

3.  **Usage of LeanSearch**
    *   LeanSearch is a semantic search engine for mathlib. It means that you need to use natural language queries to find relevant theorems, definitions, and lemmas in mathlib that can help you construct proofs.
    *   Example queries:
        *   "continuous functions on compact sets is uniformly continuous"
        *   "definition of a metric space"
        *   "definition of Dihedral group"
        *   "multiplication is commutative in a group"

3.  **`lake env lean` as an "Occasional Final Confirmation"**
    *   **Prohibited:** Do not call `lake env lean <file>` after every single declaration or minor edit.
        *   Doing so causes frequent cold starts of Lean and repeated loading of mathlib, drastically slowing down speed.
    *   **Correct Strategy:**
        *   After generating statements for a section (or a batch of entries) and fixing them via MCP diagnostics;
        *   **Occasionally**, at the outer layer of the orchestrator, call:
            ```bash
            lake env lean FormalBook/Chapters/ChapXX/sectionYY.lean
            ```
        *   Treat this as a "final sanity check," not a step-by-step operation.

4.  **No `lake build` or Heavy Commands**
    *   Reiteration: You are not allowed to use `lake build` or any command that recompiles the entire project.
    *   Your goal is:
        *   Resolve most errors at the LSP diagnostic level.
        *   Use `lake env lean <file>` only at key checkpoints to confirm the single file passes in the full environment.

**In Summary:**

> **Daily Loop:** **Resident Lean LSP server + `lean-lsp-mcp` diagnostics for fixing errors.**  
> Only use `lake env lean <file>` occasionally for final confirmation after a block of work is deemed complete.  
> **Never** frequently restart Lean via external commands, and **never** use `lake build`.

## 6. Agent Proof Pipeline Summary


Replace the sorry placeholders in the given Lean file with complete proofs, ensuring the file compiles without errors. Do not modify any statements. Feel free to decompose long proofs into helper lemmas for clarity and reusability. Use mathlib theorems or lemmas when possible. Rely on Lean LSP for diagnostics and use `lake env lean <file>` sparingly for final checks.
