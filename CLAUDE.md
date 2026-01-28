# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Lean 4 formalization project for **pointless algebraic geometry** - developing scheme theory using locales (pointless topology) instead of point-set topology. The formalization follows a LaTeX blueprint in `blueprint/src/chapters/`.

## Build Commands

```bash
# Build the project
lake build

# Build with cache (downloads mathlib cache first)
lake exe cache get && lake build

# Check a single file
lake env lean PointlessScheme/FileName.lean

# Build and check for errors
lake build 2>&1 | head -50
```

## Project Structure

- `PointlessScheme/` - Main Lean source files (one per blueprint chapter)
- `PointlessScheme.lean` - Root import file (must import all submodules)
- `blueprint/src/chapters/` - LaTeX blueprint with mathematical specifications
- `blueprint/lean_decls` - List of Lean declaration names referenced in blueprint
- `lakefile.toml` - Lake build configuration (depends on mathlib, checkdecls, doc-gen4)

## Blueprint-Driven Development

The formalization follows chapters in order:
1. `foundational-locale-theory.tex` - Frames, locales, frame presentations
2. `zariski-locale.tex` - Zariski locale via radical ideals
3. `functoriality.tex` - Functorial properties of Spec
4. `structure-sheaf.tex` - Structure sheaf construction
5. `locally-ringed-locale.tex` - Locally ringed locales
6. `basic-properties.tex` - Basic scheme properties

Each chapter requires:
1. Formalize all definitions/statements (proofs can be `sorry`)
2. Ensure file compiles with no errors
3. Mark `\lean{FullDeclarationName}` and `\leanok` tags in blueprint
4. Complete all proofs (no `sorry`, no axioms)

## Key Mathlib Dependencies

- `Mathlib.Order.Frame` - Frame and locale theory
- `Mathlib.RingTheory.Ideal.Basic` - Ideal theory
- `Mathlib.RingTheory.Ideal.Operations` - Radical ideals
- `Mathlib.Algebra.Ring.Localization` - Localizations
- `Mathlib.Topology.Category.Locale` - Category of locales

## Blueprint Tag Convention

In `.tex` files:
- `\lean{Namespace.declName}` - Links to Lean declaration
- `\leanok` - Marks statement as formalized
- `\uses{label1, label2}` - Declares dependencies on other results
