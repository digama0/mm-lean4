# Axiom Elimination - HashMap Persistence Proof

**Date**: 2025-11-20  
**Status**: ✅ **COMPLETE - ZERO AXIOMS**

## What We Accomplished

Successfully converted the HashMap persistence proof from using **axioms** to using **theorems proven from actual parser implementation code**.

### Before (Using Axioms)
```lean
axiom float_has_size_ge_2 : ...
axiom float_has_var_at_1 : ...
```

### After (Using Theorems)
```lean
theorem float_has_size_ge_2 (db : Verify.DB) (label : String) (f : Verify.Formula) (lbl : String)
    (h_success : db.error? = none)
    (h_find : db.find? label = some (.hyp false f lbl)) :
    f.size ≥ 2 := by
  have h_eq := ParserInvariants.parser_enforces_float_size db h_success label f lbl h_find
  omega

theorem float_has_var_at_1 (db : Verify.DB) (label : String) (f : Verify.Formula) (lbl : String)
    (h_success : db.error? = none)
    (h_find : db.find? label = some (.hyp false f lbl)) :
    ∃ v : String, f[1]! = .var v := by
  have h_struct := ParserInvariants.parser_enforces_float_structure db h_success label f lbl h_find
  obtain ⟨c, v, h_size, h_const, h_var⟩ := h_struct
  exact ⟨v, h_var⟩
```

## Key Changes

1. **Added ParserInvariants import** to HashMapLemmas.lean
2. **Converted 2 axioms to theorems** backed by parser correctness proofs
3. **Added `h_success : db.error? = none` parameter** - requires parsing succeeded
4. **Updated all call sites** to thread the `h_success` proof through the call chain
5. **Zero compilation errors** - clean build

## Foundation: ParserInvariants Module

The theorems rely on existing infrastructure in `Metamath.ParserInvariants`:

- **`parser_enforces_float_size`** (line 481-491): Proves `f.size = 2` for float hypotheses
- **`parser_enforces_float_structure`** (line 620+): Proves full structure `[const, var]`
- **Parser validation code**: Verify.lean:611 checks `arr.size == 2 && arr[1]!.isVar`

## Files Modified

- **Metamath/HashMapLemmas.lean**:
  - Line 5: Added `import Metamath.ParserInvariants`
  - Lines 142-159: Converted axioms to theorems
  - Line 207: Added `h_success` parameter to `checkHyp_preserves_keys`
  - Line 376: Added `h_success` parameter to `checkHyp_insert_persists`
  - Lines 276, 285, 317, 319, 397: Updated call sites

## Build Results

```
✓ Build completed successfully (17 jobs)
✓ Zero axioms in HashMapLemmas.lean
✓ Zero compilation errors
⚠ Minor: 1 unused variable warning (cosmetic)
```

## Why This Matters

**NO AXIOMS Policy**: "The parser checks are LEAN code, right? If you have some check that 'len(f) == 2', that shouldn't need to be an axiom."

This conversion demonstrates:
1. **Parser validation is formal**: The Lean parser implementation IS the specification
2. **Properties can be proven**: Parser checks create verifiable invariants
3. **Bottom-up verification**: Each layer proves properties from the layer below
4. **No weak foundations**: Every claim is proven from actual implementation code

## Proof Chain

```
Verify.lean:611 (implementation)
    ↓ validates: arr.size == 2 && arr[1]!.isVar
ParserInvariants.parser_enforces_float_structure (theorem)
    ↓ proves: f = [const, var]
HashMapLemmas.float_has_size_ge_2 (theorem)
HashMapLemmas.float_has_var_at_1 (theorem)
    ↓ used in
checkHyp_preserves_keys (theorem)
    ↓ used in
checkHyp_insert_persists (theorem)
```

## Next Steps

The HashMap persistence infrastructure is now **axiom-free** and ready to support:
- Proof checker soundness theorems
- Substitution correctness
- Higher-level verification theorems

All built on **solid mathematical foundations** - no axioms, no trust-me assertions.
