# Stuck Proof Patterns - Complete Analysis

This document maps the 3 stuck axioms in KernelClean.lean to specific curriculum lessons that isolate and demonstrate the exact patterns needed to complete them.

---

## Executive Summary

| Stuck Proof | Line | Curriculum | Pattern | Difficulty |
|-------------|------|-----------|---------|------------|
| `subst_preserves_head_of_const0` | 328 | Lesson 4 + Lesson 2 | List splitting + fold induction | Medium |
| `subst_ok_flatMap_tail` | 370 | Lesson 6 + Lesson 3 | FoldlM case analysis + two-level induction | Hard |
| `subst_preserves_head` | 401 | Lesson 4 | List splitting (depends on parser lemma) | Low |

---

## Detailed Pattern Mapping

### 1. **Line 328: `subst_preserves_head_of_const0`** - List Splitting Pattern

**Location in code:**
```lean
theorem subst_preserves_head_of_const0
    {σ : Std.HashMap String Verify.Formula}
    {f g : Verify.Formula}
    (hf : 0 < f.size)
    (hhead : ∃ c, f[0]! = Verify.Sym.const c)
    (h_sub : f.subst σ = Except.ok g) :
  ∃ (hg : 0 < g.size), g[0]'hg = f[0]'hf
```

**What it's trying to do:**
- Take a formula `f` with size > 0
- Assert first symbol is a constant (from parser invariant)
- Prove that after substitution, the first symbol is still the same

**Stuck at:**
Converting between array representation (`f.size > 0`, `f[0]!`) and list representation (`∃ head tail, f.toList = head :: tail`).

**Curriculum Solution:**
Use **Lesson 4: List Splitting** patterns:
1. `list_nonempty_split`: Convert `0 < f.toList.length` → `∃ head tail, f.toList = head :: tail`
2. `head_after_split`: Extract the head and connect it to array indexing
3. Pattern matching on cons case to discharge nil impossibility

**Proof sketch:**
```lean
theorem subst_preserves_head_of_const0 ... := by
  have hf : 0 < f.size := ...
  have hconst : ∃ c, f[0]! = Verify.Sym.const c := ...

  -- Split f.toList using Lesson 4 pattern
  obtain ⟨head, tail, h_split⟩ := list_nonempty_split f.toList (by omega)

  -- Now f.toList = head :: tail and head = f[0]!
  -- Use fold induction (Lesson 2) on tail

  -- First step: substStep σ #[] (Verify.Sym.const c) = .ok #[Verify.Sym.const c]
  -- Remaining: tail fold preserves head via head_push_stable
```

**Related Lessons:**
- **Lesson 4** (primary): List splitting patterns
- **Lesson 2** (secondary): Fold induction with generalized accumulator
- **Helper lemmas needed**: `head_push_stable`, `head_append_many_stable`

---

### 2. **Line 370: `subst_ok_flatMap_tail`** - FoldlM Case Analysis Pattern

**Location in code:**
```lean
theorem subst_ok_flatMap_tail
  {σ : Std.HashMap String Formula} {f g : Formula}
  (hsub : f.subst σ = .ok g) :
  g.toList.tail
    =
  (f.toList.tail).flatMap (fun s =>
    match s with
    | .const _ => [s]
    | .var v   =>
      match σ[v]? with
      | none    => []
      | some e  => e.toList.drop 1)
```

**What it's trying to do:**
- Show that after substitution, the tail of `g` matches the functional specification
- Each constant stays as-is, each variable expands according to HashMap lookup

**Stuck at:**
Multiple issues:
1. **Case analysis blocker** (Lesson 6): At each step, `substStep σ acc s` can either:
   - Return `.ok acc'` (continue with new accumulator)
   - Return `.error _` (contradicts goal that fold succeeded)

2. **Accumulator threading blocker** (Lesson 2): When `substStep` modifies accumulator,
   induction hypothesis only applies to original accumulator.
   Solution: Generalize accumulator in helper lemma.

3. **FlatMap correspondence blocker** (Lesson 3): Must show each fold step
   produces exactly the flatMap output.

**Curriculum Solution:**
Use **Lesson 6: FoldWithCaseAnalysis** two-level induction:

```lean
theorem subst_ok_flatMap_tail ... := by
  -- Helper: generalize the accumulator
  have helper : ∀ (acc : Array Sym),
      f.toList.tail.foldlM (substStep σ) acc = .ok result →
      result = acc.toList ++ (f.toList.tail).flatMap (...) := by
    intro acc h_fold
    -- Induction on f.toList.tail
    induction f.toList.tail generalizing acc result with
    | nil =>
        -- Base: [].foldlM ... acc = .ok result
        simp [List.foldlM] at h_fold
        exact h_fold ▸ ...
    | cons s syms ih =>
        -- Step: (s :: syms).foldlM ... acc = .ok result
        simp [List.foldlM] at h_fold
        -- Case on substStep σ acc s
        cases h_step : substStep σ acc s with
        | error _ =>
            -- Fold fails, contradicts .ok
            simp [h_step] at h_fold
        | ok acc' =>
            -- Continue with acc'
            simp [h_step] at h_fold
            -- Now: syms.foldlM (substStep σ) acc' = .ok result
            -- Use IH with acc'
            have := ih acc' h_fold
            -- Relate to flatMap spec
            simp [this]

  -- Apply helper with empty accumulator
  exact helper #[] hsub
```

**Related Lessons:**
- **Lesson 6** (primary): FoldlM case analysis
- **Lesson 2** (secondary): Fold induction with generalized accumulator
- **Lesson 3** (secondary): Monadic fold patterns

**Key Insight:**
The `generalizing accumulator` pattern from Lesson 2, applied to monadic folds.
When the fold step modifies the accumulator, the helper lemma must account for this.

---

### 3. **Line 401: `subst_preserves_head`** - List Splitting (Parser Invariant)

**Location in code:**
```lean
have hconst : ∃ c, f[0]! = Verify.Sym.const c := by
  -- Option A: replace this with your parser lemma
  -- Option B: thread from call-site (`assert_step_ok`) when `f` comes from the DB
  -- TODO: Wire this from ParserInvariants.lean once "all formulas start with const" is proven
  admit
```

**What it's trying to do:**
- Assert that every well-formed formula from the Metamath database has a constant as its first symbol
- This is a parser invariant: formulas always start with a typecode (constant)

**Stuck at:**
Dependency on `ParserInvariants.lean` which must provide the lemma stating this.

**Curriculum Solution:**
This is **not really a proof pattern issue** - it's a **missing lemma**.

Once `ParserInvariants.lean` provides:
```lean
theorem formula_first_is_const (f : Formula) (h : f.isWellFormed) :
    ∃ c, f[0]! = Sym.const c
```

Then line 401 becomes trivial:
```lean
have hconst := formula_first_is_const f h
```

**Workaround for now:**
Thread the proof from the call site where `f` comes from the database:
```lean
theorem subst_preserves_head ... {h_well_formed : f.isWellFormed} :
    ... := by
  have hconst : ∃ c, f[0]! = Verify.Sym.const c :=
    formula_first_is_const f h_well_formed
  ...
```

---

## Pattern Index

### List Splitting (Lesson 4)
Used in: Lines 328, 401

**Key patterns:**
```lean
-- Convert size > 0 to list split
list_nonempty_split (xs : List α) (h : 0 < xs.length) :
    ∃ head tail, xs = head :: tail

-- Case analysis automatically discharges nil impossibility
cases xs with
| nil => simp at h  -- h : 0 < [].length is false
| cons head tail => -- Now we have xs = head :: tail
```

**Application:**
When you have array size > 0 but need structural list pattern, use splitting.

---

### Fold Induction with Generalized Accumulator (Lesson 2)
Used in: Lines 328, 370

**Key pattern:**
```lean
-- Generalize the accumulator in induction
induction xs generalizing acc with
| nil => ...
| cons x xs ih =>
    -- ih now has: xs.foldl f (f acc x) = ...
    -- Can relate to full list result
```

**Application:**
When fold modifies accumulator at each step, must generalize in induction.

---

### FoldlM Case Analysis (Lesson 6)
Used in: Line 370

**Key pattern:**
```lean
-- Two-level induction: helper + main
have helper : ∀ acc, syms.foldlM f acc = .ok result → ... := by
  intro acc h_fold
  induction syms generalizing acc result with
  | nil => ...
  | cons s syms ih =>
      simp [List.foldlM] at h_fold
      cases h_step : f acc s with
      | error _ => simp [h_step] at h_fold  -- Contradiction
      | ok acc' =>
          simp [h_step] at h_fold
          -- Use ih with new accumulator
```

**Application:**
When foldlM step can fail, case on success/failure at each step.

---

### Function Pattern Mismatch (Lesson 5)
**Status**: Identified but not currently blocking (would affect `toSubstTyped_of_allM_true` at line 861 if we tackled it)

**Pattern:**
```lean
-- Two lambda patterns:
fun (c, v) => body  -- tuple destructuring
fun x => ... x.fst x.snd  -- pair access

-- Solution: simp or Function.ext to normalize
simp only [...]  -- reduces to normal form
```

---

## Completion Priority

### Phase 1 (Critical - Complete first)
1. **Line 401**: Wire from `ParserInvariants.lean` (requires just a lemma call)
2. **Line 328**: Use Lesson 4 + Lesson 2 patterns (medium effort, enables others)

### Phase 2 (Core functionality)
3. **Line 370**: Use Lesson 6 two-level induction (hard but core substitution correspondence)

### Phase 3 (If time permits)
- **Line 861**: Use Lesson 5 function pattern normalization
- **Remaining sorry proofs**: Follow proof roadmap in `STUCK_PROOFS_ANALYSIS.md`

---

## Testing the Patterns

Each curriculum lesson has:
- **Working examples**: Theorems that compile and pass
- **Commented exercises**: Try implementing with hints

To test the stuck proofs:
1. Start with corresponding curriculum lesson
2. Work through the exercises
3. Apply the exact pattern to the stuck proof
4. Verify with `lake build`

---

## Files Reference

- **Curriculum Lessons**: `/Lean Curriculum/0{1-6}*.lean`
- **Stuck Proofs Analysis**: `STUCK_PROOFS_ANALYSIS.md`
- **Proof Patterns Reference**: `.claude/PROOF_PATTERNS.md`
- **Main Proofs**: `Metamath/KernelClean.lean` (lines 328, 370, 401)
- **Helper Lemmas**: `Metamath/ArrayListExt.lean`, `Metamath/KernelExtras.lean`
