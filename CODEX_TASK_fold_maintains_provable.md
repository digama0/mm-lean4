# Task for Codex: Prove `fold_maintains_provable`

## Location
File: `Metamath/KernelClean.lean`, lines 3811-3856

## Current State
```lean
theorem fold_maintains_provable
    (db : Verify.DB)
    (proof : Array String)
    (pr_init pr_final : Verify.ProofState)
    (Γ : Spec.Database) (fr : Spec.Frame)
    (e_final : Verify.Formula) :
  WF.WellFormedDB db →
  toDatabase db = some Γ →
  toFrame db pr_init.frame = some fr →
  proof.foldlM (fun pr step => Verify.DB.stepNormal db pr step) pr_init = Except.ok pr_final →
  pr_init.stack = #[] →  -- Start with empty stack
  pr_final.stack.size = 1 →  -- End with singleton stack
  pr_final.stack[0]? = some e_final →  -- Extract the final expression
  Spec.Provable Γ fr (toExpr e_final) := by
  intro h_db_wf h_db h_fr h_fold h_init h_size h_final

  -- Current proof sketch (lines 3827-3856)
  unfold Spec.Provable
  refine ⟨[], [toExpr e_final], ?proof_valid, rfl⟩
  sorry  -- TODO: Array.foldlM induction with stepNormal_sound correspondence
```

## What This Theorem Says

**THE CROWN JEWEL of Phase 7**: If we fold `stepNormal` over a proof array starting from empty stack and ending with a singleton stack `[e_final]`, then `e_final` is **Provable** in the spec.

This is the final bridge between:
- **Implementation**: `proof.foldlM stepNormal` succeeds with singleton stack
- **Specification**: `Spec.Provable Γ fr (toExpr e_final)` holds mathematically

Once proven, this **unlocks `verify_impl_sound`** (the main soundness theorem)!

## Key Definitions

### Spec.Provable (Spec.lean:195)
```lean
def Provable (Γ : Database) (fr : Frame) (e : Expr) : Prop :=
  ∃ (steps : List ProofStep) (finalStack : List Expr),
    ProofValid Γ fr finalStack steps ∧
    finalStack = [e]
```

### Spec.ProofValid (Spec.lean:167)
```lean
inductive ProofValid (Γ : Database) : Frame → List Expr → List ProofStep → Prop where
  | nil : ∀ fr, ProofValid Γ fr [] []
  | useEssential : ... → ProofValid Γ fr (e :: stack) (ProofStep.useHyp ... :: steps)
  | useFloating : ... → ProofValid Γ fr (...) (...)
  | useAxiom : ... → ProofValid Γ fr (applySubst fr'.vars σ e :: remaining) (...)
```

### ProofStateInv (KernelClean.lean:1965)
```lean
structure ProofStateInv (db : Verify.DB) (pr_impl : Verify.ProofState)
    (Γ : Spec.Database) (fr_spec : Spec.Frame) (stack_spec : List Spec.Expr) : Prop where
  db_wf : WF.WellFormedDB db
  db_ok : toDatabase db = some Γ
  frame_ok : toFrame db pr_impl.frame = some fr_spec
  stack_ok : viewStack pr_impl.stack = stack_spec
```

## Available Infrastructure (ALL COMPLETE!)

### 1. **ProofStateInv_init** (line 2000) - Initial invariant
```lean
theorem ProofStateInv_init (db : Verify.DB) (Γ : Spec.Database) (fr_spec : Spec.Frame)
    (label : String) (f : Verify.Formula) :
  WF.WellFormedDB db →
  toDatabase db = some Γ →
  toFrame db db.frame = some fr_spec →
  ProofStateInv db ⟨⟨0, 0⟩, label, f, db.frame, #[], #[], ...⟩ Γ fr_spec []
```

### 2. **assert_step_ok** (line 3605) - Step preservation ✅ COMPLETE!
```lean
theorem assert_step_ok
  (db : Verify.DB) (pr pr' : Verify.ProofState) (label : String)
  (Γ : Spec.Database) (fr_spec : Spec.Frame) (stack_spec : List Spec.Expr)
  (fr_assert : Spec.Frame) (e_assert : Spec.Expr)
  (f_impl : Verify.Formula) (fr_impl : Verify.Frame) :
  ProofStateInv db pr Γ fr_spec stack_spec →
  db.find? label = some (Verify.Object.assert f_impl fr_impl label) →
  toFrame db fr_impl = some fr_assert →
  toExprOpt f_impl = some e_assert →
  Γ label = some (fr_assert, e_assert) →
  Verify.DB.stepNormal db pr label = Except.ok pr' →
  ∃ (stack_new : List Spec.Expr) (e_conclusion : Spec.Expr),
    ProofStateInv db pr' Γ fr_spec stack_new ∧
    (∃ needed : List Spec.Expr,
      stack_new = (stack_spec.dropLastN fr_impl.hyps.size) ++ [e_conclusion])
```

### 3. Array.foldlM infrastructure
- `Array.foldlM_cons` - Decompose fold into head + tail
- `Array.foldlM_nil` - Base case for empty array
- List induction patterns for building ProofValid

## Proof Strategy

**Key Insight**: We need to build a `ProofValid` derivation by induction on the proof array, using `assert_step_ok` to show each step preserves the invariant and extends the proof.

### Approach 1: Direct Array Induction (Recommended)

**Step 1**: Generalize to allow induction
```lean
-- We need to prove for ANY starting stack, not just []
-- Change the goal to support induction:
suffices ∀ (pr : ProofState) (stack_spec : List Expr),
  ProofStateInv db pr Γ fr stack_spec →
  proof.foldlM stepNormal pr = ok pr_final →
  pr_final.stack.size = 1 →
  pr_final.stack[0]? = some e_final →
  Spec.Provable Γ fr (toExpr e_final)
from this pr_init [] (ProofStateInv_init ...) h_fold h_size h_final
```

**Step 2**: Induction on proof array
```lean
induction proof using Array.size_induction with
| _ proof ih =>
  intro pr stack_spec inv h_fold h_size h_final
  cases proof using Array.cases with
  | empty =>
    -- Base case: proof = #[]
    -- h_fold: pr = pr_final (no steps)
    -- h_size: pr_final.stack.size = 1
    -- But pr_init.stack = #[] (size 0), contradiction!
    -- Actually: if proof is empty, no change, so pr.stack = pr_final.stack
    -- So pr.stack.size = 1, but we started with stack_spec
    sorry
  | push proof_rest step =>
    -- Inductive case: proof = proof_rest.push step
    -- Apply Array.foldlM_push to decompose:
    -- proof.foldlM f pr = do { pr' ← proof_rest.foldlM f pr; f pr' step }
    sorry
```

**Step 3**: In the push case, use `assert_step_ok`
```lean
-- We have: (proof_rest.push step).foldlM stepNormal pr = ok pr_final
-- Decompose to: proof_rest.foldlM stepNormal pr >>= (fun pr' => stepNormal pr' step)

cases h_rest : proof_rest.foldlM stepNormal pr with
| error e => simp [h_rest] at h_fold  -- Contradiction
| ok pr' =>
  -- Now: stepNormal pr' step = ok pr_final

  -- Apply IH to pr' (if needed for building ProofValid incrementally)
  -- OR: Use assert_step_ok to show pr' → pr_final preserves invariant

  -- Key: assert_step_ok gives us the new stack and conclusion
  have ⟨stack_new, e_concl, inv', h_stack_new⟩ := assert_step_ok ...

  -- Build ProofValid by composing previous steps (from IH) with new step
  sorry
```

### Approach 2: Use ProofValidSeq (Alternative)

The spec has `ProofValidSeq` (Spec.lean:212) for building proofs incrementally:
```lean
inductive ProofValidSeq (Γ : Database) : Frame → List Expr → Frame → List Expr → Prop where
  | nil : ∀ fr stk, ProofValidSeq Γ fr stk fr stk
  | cons : ∀ fr₀ stk₀ fr₁ stk₁ fr₂ stk₂ steps,
      ProofValid Γ fr₀ stk₁ steps →
      ProofValidSeq Γ fr₁ stk₁ fr₂ stk₂ →
      ProofValidSeq Γ fr₀ stk₀ fr₂ stk₂
```

And `ProofValidSeq.toProvable` (Spec.lean:237) converts to Provable:
```lean
theorem ProofValidSeq.toProvable {Γ : Database} {fr : Frame} {stk : List Expr} {e : Expr} :
  ProofValidSeq Γ fr stk fr [e] → Provable Γ fr e
```

**Note**: This theorem has a `sorry` (line 239 in Spec.lean), but the TODO suggests it's provable by induction. You could:
1. Prove `ProofValidSeq.toProvable` first (side quest)
2. OR: Build the ProofValid directly without using ProofValidSeq

### Approach 3: Backwards from Final Stack (Simplest?)

Since we end with singleton `[e_final]` and start with `[]`:
```lean
-- Work backwards from the final state
-- We know pr_final.stack = [e_final] and viewStack pr_final.stack = [toExpr e_final]
-- We need ProofValid Γ fr [toExpr e_final] steps for some steps

-- The proof array builds this stack step by step
-- Each assert adds one conclusion, each hyp use adds one element
-- Can we extract the ProofValid directly from the fold?
```

## Key Challenges

1. **ProofValid construction**: Need to build the `steps : List ProofStep` witness
   - Each `stepNormal` call corresponds to a ProofStep
   - Must track which steps were executed and in what order

2. **Array vs List induction**: `proof` is an Array, but ProofValid works with Lists
   - Use `Array.toList` and `Array.foldlM_toList` to bridge

3. **Invariant threading**: Each step preserves ProofStateInv
   - Use `assert_step_ok` to maintain invariant through the fold
   - The invariant ensures `viewStack` matches spec stack

4. **Final stack extraction**: We have `pr_final.stack[0]? = some e_final`
   - Need to show `viewStack pr_final.stack = [toExpr e_final]`
   - This follows from `inv.stack_ok` for the final invariant

## Expected Proof Length
80-150 lines (array induction + invariant preservation + ProofValid construction)

## Build Command
```bash
lake build Metamath.KernelClean
```

## Success Criteria
- Remove the `sorry` at line 3856
- Proof compiles without errors
- No new axioms introduced
- Uses existing infrastructure (`assert_step_ok`, `ProofStateInv`, array lemmas)

## Notes
- **Critical dependency**: `assert_step_ok` is ✅ COMPLETE (lines 3605-3785)
- **Well-formedness wiring**: Already in place via `ProofStateInv.db_wf`
- **Main theorem impact**: Once this is proven, `verify_impl_sound` becomes trivial!
- The proof structure is already sketched (lines 3827-3856) - just need to fill the induction
- Consider whether you need to prove `stepNormal_sound` (line 3787) first, or if `assert_step_ok` is sufficient

## Strategic Priority
**This is THE highest-value theorem** in the entire codebase:
- Unlocks the main soundness theorem `verify_impl_sound`
- All infrastructure is ready (WellFormedDB wiring, assert_step_ok complete)
- Estimated as "30-60 minute kill" by strategic analysis
- This completes Phase 7 and validates the entire verification chain!

Good luck! This theorem proves that the Metamath verifier is **sound**! 🎯
