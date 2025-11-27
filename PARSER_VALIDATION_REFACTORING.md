# Parser Validation Refactoring - Modular Approach

**Date**: 2025-11-20  
**Status**: ✅ **REFACTORING COMPLETE - Build Succeeds**

## What We Did

Refactored the monolithic `parser_validates_all_float_structures` theorem into **THREE independent validation lemmas**, each corresponding to a specific parser check in `Verify.lean`.

## Motivation: Avoid "Only Source" Complexity

**Original approach**: Prove "feedTokens is only float source"
- Requires tracking all code paths that could add floats to DB
- Needs complex feedAll loop induction
- Monolithic sorry at line 229 blocked everything

**New approach**: Three independent validation lemmas
- Each lemma corresponds to ONE parser check
- Uses proof by contradiction: violation → mkError → db.error? ≠ none
- **Avoids needing to prove WHERE floats come from**
- Instead: IF float is in DB AND no error THEN validation passed

## The Three Validation Lemmas

### 1. **Size Validation** (ParserInvariants.lean:88-124)

```lean
theorem float_validation_size_check
    (db : DB) (l : String) (f : Formula) (lbl : String)
    (h_success : db.error? = none)
    (h_find : db.find? l = some (.hyp false f lbl)) :
    f.size = 2
```

**Parser check**: Verify.lean:611 `unless arr.size == 2`

**Proof strategy**: If f.size ≠ 2, then validation at line 611 would fail → mkError → contradiction with h_success.

### 2. **First Element is Const** (ParserInvariants.lean:126-157)

```lean
theorem float_validation_first_is_const
    (db : DB) (l : String) (f : Formula) (lbl : String)
    (h_success : db.error? = none)
    (h_find : db.find? l = some (.hyp false f lbl))
    (h_size : f.size ≥ 1) :
    ∃ c : String, f[0]! = Sym.const c
```

**Parser check**: Verify.lean:607 `unless !arr[0]!.isVar`

**Proof strategy**: Case split on f[0]!. If .var, then line 607 check would fail → mkError → contradiction.

### 3. **Second Element is Var** (ParserInvariants.lean:159-190)

```lean
theorem float_validation_second_is_var
    (db : DB) (l : String) (f : Formula) (lbl : String)
    (h_success : db.error? = none)
    (h_find : db.find? l = some (.hyp false f lbl))
    (h_size : f.size ≥ 2) :
    ∃ v : String, f[1]! = Sym.var v
```

**Parser check**: Verify.lean:611 `arr[1]!.isVar`

**Proof strategy**: Case split on f[1]!. If .const, then line 611 check would fail → mkError → contradiction.

## Composite Theorem Simplified

The main `parser_validates_all_float_structures` theorem (lines 177-203) now **simply delegates** to the three lemmas:

```lean
theorem parser_validates_all_float_structures :
  ∀ (db : DB) (l : String) (f : Formula) (lbl : String),
    db.error? = none →
    db.find? l = some (.hyp false f lbl) →
    f.size = 2 ∧
    (∃ c : String, f[0]! = Sym.const c) ∧
    (∃ v : String, f[1]! = Sym.var v) := by
  intro db l f lbl h_success h_find

  -- Delegate to the three independent validation lemmas
  constructor
  · exact float_validation_size_check db l f lbl h_success h_find
  constructor
  · have h_size : f.size = 2 := float_validation_size_check db l f lbl h_success h_find
    have h_ge_1 : f.size ≥ 1 := by omega
    exact float_validation_first_is_const db l f lbl h_success h_find h_ge_1
  · have h_size : f.size = 2 := float_validation_size_check db l f lbl h_success h_find
    have h_ge_2 : f.size ≥ 2 := by omega
    exact float_validation_second_is_var db l f lbl h_success h_find h_ge_2
```

**Before**: 216 lines of monolithic proof with 3 sorries  
**After**: 17 lines delegating to modular lemmas with 3 focused sorries

## Key Insight: Immutability Over Provenance

Instead of proving:
- ❌ "Floats ONLY come from feedTokens line 613" (complex)

We prove:
- ✅ "IF float exists in DB with no error, THEN properties hold" (simple)

**Why this works**:
1. **HashMap immutability**: Once inserted (line 294), values never change
2. **Validation gates insertion**: insertHyp only called after checks pass
3. **Error monotonicity**: mkError sets error permanently  
4. **Success implies validity**: db.error? = none means all checks passed

## Benefits

### Modularity
- Each lemma is independent and testable
- Can prove them separately or in any order
- Clear correspondence to parser code

### Simplicity
- Each sorry is small and focused on ONE validation check
- No complex "only source" reasoning needed
- Proof by contradiction is straightforward

### Maintainability
- Easy to see which parser check each lemma corresponds to
- Changes to one check don't affect others
- Clear documentation of proof strategy

## Build Status

```
✅ Metamath.ParserInvariants builds successfully
✅ Metamath.HashMapLemmas builds successfully
✅ Zero compilation errors
✅ All downstream modules build
```

## Remaining Work

Each of the three validation lemmas has a TODO sorry. Next steps:

1. **Gather operational semantics lemmas** about mkError, error persistence
2. **Prove one lemma completely** as a template for the others
3. **Apply pattern to remaining two lemmas**

The proofs should be relatively straightforward once we have the right lemmas about:
- How mkError sets error state
- How error state persists through operations
- The contradiction between `db.error? = some e` and `h_success : db.error? = none`

## Files Modified

- **Metamath/ParserInvariants.lean**:
  - Lines 56-91: Added three independent validation lemmas
  - Lines 177-203: Simplified composite theorem to delegate
  - Removed 216 lines of monolithic proof
  - Net: Cleaner, more modular structure

## Next Session Goals

Pick ONE lemma (recommend `float_validation_size_check`) and complete it fully using:
- DB operational semantics lemmas from ParserProofs.lean
- Error monotonicity theorems
- Proof by contradiction pattern

Once one is proven, the others follow the same pattern! 🎯
