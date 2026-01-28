# Claude Guide for Mathematical Formalization

You are Claude, an AI assistant helping with mathematical formalization in Lean 4. This guide covers three main workflows:
1. **Understanding and summarizing mathematical knowledge** from blueprints
2. **Building and maintaining blueprints** for formalization projects
3. **Formalizing definitions, statements, and proofs** in Lean 4

---

## Part 1: Understanding Mathematical Knowledge from Blueprints

### 1.1 Blueprint Structure and Reading Order

The blueprint is organized in LaTeX files under `blueprint/src/chapters/`. Read chapters in dependency order:

1. `foundational-locale-theory.tex` - Basic definitions (frames, locales)
2. `zariski-locale.tex` - Zariski topology on locales
3. `functoriality.tex` - Functorial properties
4. `structure-sheaf.tex` - Structure sheaves
5. `locally-ringed-locale.tex` - Locally ringed locales
6. `basic-properties.tex` - Additional properties

**Reading Strategy:**
- Start from fundamental definitions and build up
- Track dependencies using `\uses{}` tags
- Identify key theorems and their proof sketches
- Note mathematical patterns and standard constructions

### 1.2 Blueprint Tags and Conventions

**Important LaTeX Tags:**

- `\label{def:name}` - Unique identifier for definitions
- `\label{lemma:name}` - Unique identifier for lemmas
- `\label{theorem:name}` - Unique identifier for theorems
- `\uses{label1, label2}` - Dependency declarations
- `\lean{FullName}` - Reference to Lean declaration (e.g., `\lean{Frame.inf_sSup_eq}`)
- `\leanok` - Marks completed formalization (statement or proof)

**Example:**
```latex
\begin{definition}[Frame]
  \label{def:frame}
  \lean{Frame}
  \leanok
  A frame is a complete lattice satisfying...
\end{definition}
```

### 1.3 Extracting Mathematical Content

When reading a blueprint chapter:

**For Definitions:**
- Identify the mathematical structure being defined
- Note all axioms/properties required
- Check if mathlib already has this (search first!)
- List dependencies (what must be defined first)

**For Theorems/Lemmas:**
- Extract the precise statement
- Identify hypotheses and conclusion
- Note proof strategy (constructive vs. classical)
- List required lemmas from dependencies

**For Proofs:**
- Outline the proof structure (direct, by induction, by contradiction, etc.)
- Identify key steps and subgoals
- Note which existing mathlib lemmas might apply
- Mark potential difficulties

### 1.4 Dependency Graph Analysis

Build a mental (or explicit) dependency graph:

```
def:frame → def:frame-homomorphism → lemma:locale-morphism-composition
           ↘ def:locale              ↗
```

**Workflow:**
1. List all definitions in order of dependency
2. Group lemmas by which definitions they use
3. Identify "theorem clusters" (groups of related results)
4. Prioritize formalization by dependency order

### 1.5 Mathematical Knowledge Summary Template

For each chapter, create a summary:

```markdown
## Chapter: [Name]

### Core Concepts
- **Frame**: Complete lattice with infinite distributivity
- **Locale**: Dual of frame (contravariant category)

### Key Definitions
1. Frame (def:frame) - needs: CompleteLattice
2. FrameHom (def:frame-homomorphism) - needs: Frame
3. Locale (def:locale) - needs: Frame, FrameHom

### Important Theorems
1. Locale morphism composition (lemma:locale-morphism-composition)
   - Uses: def:locale, def:frame-homomorphism
   - Strategy: Straightforward composition proof

### Formalization Notes
- Check if Frame is in mathlib (likely yes!)
- Frame distributivity might need custom instance
- Locale as OppositeCategory might work
```

---

## Part 2: Building and Maintaining Blueprints

### 2.1 Blueprint Writing Guidelines

**Structure Requirements:**

1. **Each mathematical object needs:**
   - Unique `\label{}`
   - Clear mathematical definition
   - Dependency tags (`\uses{}`)

2. **Each theorem/lemma needs:**
   - Statement with hypotheses and conclusion
   - Proof sketch (even informal)
   - Dependencies explicitly listed

3. **LaTeX Organization:**
   ```latex
   \chapter{Title}
   \section{Main Topic}

   \begin{definition}[Name]
     \label{def:shortname}
     \uses{def:prereq1, def:prereq2}
     \lean{Lean.Declaration.Name}
     \leanok
     Mathematical content...
   \end{definition}
   ```

### 2.2 Blueprint Maintenance Workflow

**Before Formalization:**
1. Fix all broken `\label{}` references
2. Ensure all `\uses{}` tags point to valid labels
3. Remove empty or placeholder `\lean{}` tags
4. Verify mathematical correctness

**During Formalization:**
1. Add `\lean{FullLeanName}` when declaration is created
2. Add `\leanok` when statement compiles correctly
3. Add second `\leanok` when proof is complete
4. Update dependencies if formalization reveals issues

**Tag Status System:**
```latex
% Not started:
\begin{definition}[Name]
  \label{def:name}
  ...
\end{definition}

% Statement formalized:
\begin{definition}[Name]
  \label{def:name}
  \lean{MyProject.Name}
  \leanok
  ...
\end{definition}

% Proof complete:
\begin{theorem}[Name]
  \label{thm:name}
  \lean{MyProject.theorem_name}
  \leanok
  ...
\end{theorem}
\begin{proof}
  \leanok
  ...
\end{proof}
```

### 2.3 Common Blueprint Patterns

**Pattern 1: Algebraic Structure**
```latex
\begin{definition}[Structure Name]
  \label{def:structure}
  \uses{def:underlying-type}
  A [structure] consists of:
  \begin{enumerate}
    \item A type $X$
    \item Operations: $\cdot : X \to X \to X$
    \item Axioms: (list all)
  \end{enumerate}
\end{definition}
```

**Pattern 2: Category-Theoretic Construction**
```latex
\begin{definition}[Category]
  \label{def:category}
  Objects: [describe]
  Morphisms: [describe]
  Composition: [describe]
  Identity: [describe]
\end{definition}
```

**Pattern 3: Universal Property**
```latex
\begin{lemma}[Universal Property]
  \label{lemma:universal}
  \uses{def:object}
  For any object $X$ and morphisms satisfying [conditions],
  there exists a unique morphism $f: A \to X$ such that...
\end{lemma}
```

---

## Part 3: Formalization in Lean 4

### 3.1 Project Structure

**File Organization:**
```
PointlessScheme/
├── FoundationalLocaleTheory.lean   (from foundational-locale-theory.tex)
├── ZariskiLocale.lean              (from zariski-locale.tex)
├── Functoriality.lean              (from functoriality.tex)
├── StructureSheaf.lean             (from structure-sheaf.tex)
├── LocallyRingedLocale.lean        (from locally-ringed-locale.tex)
└── BasicProperties.lean            (from basic-properties.tex)
```

**Naming Conventions:**
- File names: PascalCase matching chapter names
- Namespaces: Match file structure (`PointlessScheme.FoundationalLocaleTheory`)
- Definitions: PascalCase (`Frame`, `FrameHom`)
- Theorems: snake_case (`frame_distributivity`, `locale_comp_assoc`)

### 3.2 Formalization Workflow (Three-Pass System)

#### **Pass 1: Definitions and Statements**

**Goal:** Get all definitions and theorem statements to compile (proofs can be `sorry`)

**Process:**
1. Start from first chapter (lowest in dependency graph)
2. For each definition in blueprint:
   - Search mathlib first: Use `/search-mathlib` or `lean_leansearch`
   - If exists in mathlib: use it directly, define equivalence/instances as needed
   - If not in mathlib: formalize from scratch
   - Fill in definitions completely (no `sorry` in defs!)
3. For each theorem/lemma:
   - Formalize the statement carefully
   - Use `sorry` for proof
   - Ensure statement type-checks

**Example:**
```lean
-- Definition: must be complete
def Frame : Type u :=
  CompleteLattice α ×' (∀ a : α, ∀ s : Set α, a ⊓ sSup s = sSup ((a ⊓ ·) '' s))

-- Statement: proof can be sorry
theorem locale_comp_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (h ≫ g) ≫ f = h ≫ (g ≫ f) := by
  sorry
```

**Critical Rules for Pass 1:**
- **Never use axioms** (no `axiom`, no `Classical.choice` unless unavoidable)
- Definitions must be filled (instances too!)
- Statements must compile without errors
- Update blueprint with `\lean{}` and first `\leanok` tag

#### **Pass 2: Compilation and Semantic Verification**

**Goal:** Ensure file compiles and statements match blueprint semantics

**Process:**
1. Use LSP diagnostics: `lean_diagnostic_messages`
2. Fix type errors, import errors, name conflicts
3. Check semantic alignment:
   - Does Lean statement capture blueprint intent?
   - Are quantifiers in right order?
   - Are implicit arguments correct?
4. Add necessary instances and coercions
5. Verify with: `lake env lean PointlessScheme/ChapterName.lean`

**Common Issues:**
- Missing imports: Use `lean_local_search` to find where things are defined
- Instance synthesis failures: Add explicit `haveI` or `letI`
- Universe issues: Check universe polymorphism carefully
- Type class diamonds: Resolve with `convert` or explicit instances

**Do NOT:**
- Call `lake build` (too slow!)
- Modify statements without checking blueprint alignment
- Change variable names arbitrarily (keep mathematical meaning)

#### **Pass 3: Proof Filling**

**Goal:** Replace all `sorry` with complete proofs

**Process:**

1. **Proof Strategy:**
   - Start with simplest lemmas (no dependencies)
   - Use helper lemmas liberally
   - Keep each proof focused and short

2. **Using Lean LSP Tools:**
   ```
   - lean_goal: Check goal state at cursor
   - lean_term_goal: Check expected type
   - lean_completions: Get suggestions
   - lean_hover_info: Check lemma types
   ```

3. **Searching for Lemmas:**
   ```
   - lean_local_search: Search project definitions
   - lean_leansearch: Natural language search mathlib
     Example: "addition is commutative on natural numbers"
   - lean_loogle: Type-based search
     Example: "Nat.add", "(?a → ?b) → List ?a → List ?b"
   - lean_leanfinder: Semantic search
     Example: "continuous function on compact set"
   - lean_state_search: Find lemmas to close current goal
   - lean_hammer_premise: Get premises for simp/aesop
   ```

4. **Proof Tactics Workflow:**
   ```lean
   theorem my_theorem (h : P) : Q := by
     -- 1. Check goal: what do we need to prove?
     -- 2. Introduce variables and hypotheses
     intro x
     -- 3. Use lean_state_search to find relevant lemmas
     -- 4. Apply lemmas or use tactics
     apply some_lemma
     · -- Subgoal 1
       simp [other_lemma]
     · -- Subgoal 2
       exact h
   ```

5. **Breaking Down Complex Proofs:**
   ```lean
   -- Helper lemma (keep it general!)
   /-- Helper: characterizes when property P holds -/
   lemma helper_property (x : X) (h : Condition x) : Property x := by
     sorry

   -- Main theorem uses helper
   theorem main_result : Statement := by
     apply helper_property
     sorry
   ```

6. **After Each Proof:**
   - Check diagnostics: `lean_diagnostic_messages`
   - Verify no new errors introduced
   - Update blueprint with second `\leanok` in proof environment
   - Commit progress frequently

### 3.3 Lean LSP Tooling Strategy

**Inner Loop (Constant Use):**
- Use MCP tools via `lean-lsp-mcp` for all diagnostics
- Check goals with `lean_goal` after each tactic
- Search with `lean_leansearch`, `lean_loogle`, `lean_leanfinder`
- Fix errors using LSP feedback
- **Never restart Lean unnecessarily**

**Outer Loop (Occasional Checkpoints):**
- After completing a section of definitions
- After proving a cluster of related theorems
- Use: `lake env lean PointlessScheme/File.lean`
- This is a "final sanity check", not per-edit verification

**Forbidden:**
- Don't use `lake build` (recompiles entire project - too slow!)
- Don't call `lake env lean` after every small change
- Don't restart LSP server unless absolutely necessary

### 3.4 Common Formalization Patterns

**Pattern 1: Using Mathlib Structures**
```lean
-- Check if Frame exists in mathlib
#check Frame  -- if exists, use it!

-- If not, but CompleteLattice exists:
structure Frame (α : Type u) extends CompleteLattice α where
  inf_sSup_eq : ∀ (a : α) (s : Set α), a ⊓ sSup s = sSup ((a ⊓ ·) '' s)
```

**Pattern 2: Frame Homomorphisms**
```lean
structure FrameHom (L M : Type*) [Frame L] [Frame M] where
  toFun : L → M
  map_sSup' : ∀ s : Set L, toFun (sSup s) = sSup (toFun '' s)
  map_inf' : ∀ a b : L, toFun (a ⊓ b) = toFun a ⊓ toFun b
  map_top' : toFun ⊤ = ⊤
```

**Pattern 3: Category Instance**
```lean
instance : Category Locale where
  Hom X Y := FrameHom Y.toFrame X.toFrame  -- contravariant!
  id X := FrameHom.id
  comp f g := FrameHom.comp g f  -- reversed!
```

**Pattern 4: Universal Properties**
```lean
/-- Universal property of presented frames -/
theorem presentedFrame_universal {G R : Type*} {M : Frame}
    (φ : G → M) (h : RespectsRelations φ R) :
    ∃! f : FrameHom (Fr⟨G | R⟩) M, ∀ g : G, f (ι g) = φ g := by
  constructor
  · -- Existence
    sorry
  · -- Uniqueness
    sorry
```

### 3.5 Proof Techniques and Tactics

**Basic Tactics:**
- `intro` - introduce variables/hypotheses
- `apply` - apply lemma/function
- `exact` - provide exact proof term
- `rfl` - reflexivity (definitional equality)
- `simp` - simplification with simp lemmas
- `rw` - rewrite with equality

**Structural Tactics:**
- `constructor` - prove by building structure
- `cases` - case analysis
- `induction` - proof by induction
- `obtain` - destructure existentials
- `refine` - provide partial term with holes

**Automation:**
- `aesop` - automated reasoning
- `omega` - linear arithmetic
- `ring` - ring equations
- `field_simp` - field simplification
- `decide` - decidable propositions

**Search and Apply:**
- `apply?` - search for applicable lemmas
- `exact?` - search for exact proof
- `simp?` - show which simp lemmas were used

**Strategy for Stuck Proofs:**
1. Check goal: `lean_goal`
2. Search for lemmas: `lean_state_search` or `lean_leansearch`
3. Try `apply?` or `exact?`
4. If still stuck: break into helper lemma
5. Use `sorry` temporarily, mark in blueprint as incomplete

### 3.6 Instance and Type Class Management

**Instance Synthesis Issues:**
```lean
-- If Lean can't find instance automatically:
theorem my_result [Frame α] (h : IsProbabilityMeasure μ) : ... := by
  haveI : Instance := h  -- make it available
  sorry

-- Alternative: inline instance
theorem my_result [Frame α] : @Property α inferInstance := by
  sorry
```

**Avoiding Diamonds:**
- Use consistent type class hierarchy
- Don't define redundant instances
- Use `convert` to resolve mismatches

### 3.7 Error Handling Guide

**Type Mismatch:**
```
Error: type mismatch
  term has type X
  but is expected to have type Y

Fix: Check if coercion needed, or if wrong lemma applied
```

**Unknown Identifier:**
```
Error: unknown identifier 'Frame'

Fix: Add import or check spelling
Use: lean_local_search "Frame"
```

**Failed to Synthesize Instance:**
```
Error: failed to synthesize instance
  Frame α

Fix: Add instance explicitly or check imports
```

**Universe Issues:**
```
Error: type expected, got Type u → Type v

Fix: Check universe polymorphism, may need .{u, v} annotations
```

### 3.8 Commit and Documentation Strategy

**Commit Frequency:**
- After completing Pass 1 for a chapter
- After Pass 2 compilation succeeds
- After proving each major theorem cluster
- Use descriptive messages: "formalize Frame definition", "prove locale composition"

**Documentation in Code:**
```lean
/-- A frame is a complete lattice satisfying the infinite distributive law.
This definition corresponds to [blueprint def:frame]. -/
structure Frame (α : Type u) extends CompleteLattice α where
  inf_sSup_eq : ∀ (a : α) (s : Set α), a ⊓ sSup s = sSup ((a ⊓ ·) '' s)
```

**Blueprint References:**
- Link Lean declarations to blueprint labels
- Maintain bidirectional traceability
- Update blueprint tags immediately after formalization

---

## Part 4: Quality Checklist

### Before Marking \leanok (Statement):
- [ ] Statement compiles without errors
- [ ] All dependencies imported correctly
- [ ] Semantic meaning matches blueprint
- [ ] Appropriate generality (not too specific)
- [ ] Type class instances provided
- [ ] `\lean{FullName}` tag added to blueprint
- [ ] First `\leanok` tag added to definition/statement

### Before Marking \leanok (Proof):
- [ ] Proof complete (no `sorry`)
- [ ] No axioms used (check with `/check-axioms`)
- [ ] File compiles: `lake env lean File.lean`
- [ ] Proof is readable and maintainable
- [ ] Helper lemmas documented
- [ ] Second `\leanok` tag added to proof environment

### Before Committing:
- [ ] All tags in blueprint are correct
- [ ] No broken `\label{}` or `\uses{}` references
- [ ] Lean file compiles completely
- [ ] Diagnostics show no errors (warnings ok if explained)
- [ ] Code formatted and documented

---

## Part 5: Workflow Summary

### High-Level Process:

**Phase 1: Blueprint Understanding**
1. Read all chapters in dependency order
2. Build dependency graph
3. Identify mathlib overlaps
4. Fix broken tags and references

**Phase 2: Formalization (Per Chapter)**
1. **Pass 1:** Formalize all definitions and statements (proofs `sorry`)
   - Search mathlib first for each concept
   - Fill definitions completely
   - Ensure statements compile
   - Update blueprint with `\lean{}` and first `\leanok`

2. **Pass 2:** Verify compilation and semantics
   - Use LSP diagnostics extensively
   - Fix all compilation errors
   - Verify semantic alignment with blueprint
   - Checkpoint with `lake env lean File.lean`

3. **Pass 3:** Fill in all proofs
   - Start with simple lemmas
   - Use search tools (leansearch, loogle, leanfinder, state_search)
   - Break complex proofs into helper lemmas
   - Update blueprint with second `\leanok` in proofs
   - Commit after each major theorem

**Phase 3: Quality Assurance**
1. Run `/check-axioms` to verify no axioms used
2. Check all `\leanok` tags are accurate
3. Verify bidirectional traceability (blueprint ↔ Lean)
4. Final compilation check

---

## Part 6: Tool Reference Quick Guide

### Lean LSP Tools (Use Frequently)
- `lean_file_outline` - Get file structure
- `lean_diagnostic_messages` - Check errors/warnings
- `lean_goal` - See proof state at position
- `lean_hover_info` - Get type of symbol
- `lean_completions` - IDE autocomplete

### Search Tools (Use When Stuck)
- `lean_local_search` - Fast local declaration search
- `lean_leansearch` - Natural language mathlib search (3/30s limit)
- `lean_loogle` - Type pattern search (3/30s limit)
- `lean_leanfinder` - Semantic concept search (10/30s limit)
- `lean_state_search` - Find lemmas to close goal (3/30s limit)
- `lean_hammer_premise` - Get premises for automation (3/30s limit)

### Build Tools (Use Sparingly)
- `lake env lean File.lean` - Check single file (occasional)
- `lake build` - **Never use** (too slow)

### Lean 4 Skills (Use as Needed)
- `/build-lean` - Build with error analysis
- `/search-mathlib` - Search mathlib
- `/fill-sorry` - Interactive sorry filling
- `/repair-goal` - Repair specific goal
- `/check-axioms` - Verify no axioms

---

## Part 7: Common Pitfalls and Solutions

### Pitfall 1: Not Searching Mathlib First
**Problem:** Defining concepts that already exist in mathlib
**Solution:** Always use `lean_leansearch` or `lean_loogle` before defining anything

### Pitfall 2: Calling lake build Too Often
**Problem:** Wasting time recompiling entire project
**Solution:** Use LSP diagnostics for inner loop, `lake env lean` for checkpoints only

### Pitfall 3: Ignoring Blueprint Semantics
**Problem:** Lean statement compiles but means something different
**Solution:** Carefully verify each quantifier, implicit argument, and type

### Pitfall 4: Using Axioms Unintentionally
**Problem:** Accidentally using `Classical.choice` or other axioms
**Solution:** Run `/check-axioms` regularly, avoid `sorry` that might hide axioms

### Pitfall 5: Not Breaking Down Proofs
**Problem:** Monolithic proofs that are hard to debug
**Solution:** Extract helper lemmas early, keep proofs modular

### Pitfall 6: Poor Helper Lemma Names
**Problem:** Helper lemmas like `helper1`, `aux_lemma` are not reusable
**Solution:** Give descriptive names reflecting mathematical content

### Pitfall 7: Forgetting to Update Blueprint
**Problem:** Blueprint and code out of sync
**Solution:** Update `\lean{}` and `\leanok` tags immediately during formalization

---

## Final Notes

This workflow is designed for **systematic mathematical formalization** where:
- Blueprint drives the formalization
- Mathematical correctness is paramount
- Code quality and maintainability matter
- Traceability between informal and formal math is maintained

**Remember:**
- Read before you write
- Search before you define
- Test before you commit
- Document as you go

Good luck with your formalization! 🎯
