# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**Metamath Lean 4 Verifier Soundness Proof** - A formal verification in Lean 4 that the Metamath proof checker correctly validates mathematical theorems. This is a bottom-up architecture implementing the verifier from first principles, with each phase proving the previous layer correct.

**Key Achievement**: A mathematically sound proof checker implementation with formal soundness theorem (`verify_impl_sound`) connecting runtime behavior to mathematical validity.

## Build & Test Commands

### Build the project
```bash
lake build
```

### Build specific modules
```bash
lake build Metamath.Verify           # Parser implementation
lake build Metamath.KernelClean      # Main soundness proof
lake build Metamath.ParserInvariants # Parser correctness theorems
```

### Check a single file for errors (without building dependencies)
```bash
lean /path/to/file.lean
```

### Run the verifier executable
```bash
lake build validateDB
./.lake/build/bin/validateDB
```

### View build warnings/errors
```bash
lake build 2>&1 | grep -E "^(error|warning):" | head -20
```

## Architecture Overview

### Layer Structure (Bottom-Up)

The project uses a **phased bottom-up architecture** where each layer depends only on lower layers:

**Phase 1: Core Specifications** (`Metamath.Spec`)
- Formal definition of Metamath proof state and validity
- What the verifier should achieve mathematically

**Phase 2: Runtime Implementation** (`Metamath.Verify`)
- Byte-level parser (feed function, feedTokens)
- Database operations (insertHyp, checkHyp)
- Proof checker state machine
- **Critical fact**: Feed processes bytes with error monotonicity (error once set never clears)

**Phase 3: Parser Correctness** (`Metamath.ParserInvariants`)
- **What's proven**: Parser success implies well-formed objects in database
- Float hypothesis structure: size=2, first element is const, second is var
- Float hypothesis uniqueness: no two floats bind same variable
- **Key blocking lemma**: `feedTokens_is_only_float_source` - proves floats can ONLY be added via feedTokens.float case

**Phase 4: Bridge Functions** (`Metamath.Bridge.Basics`)
- Conversion from runtime DB representation to specification frames
- Pattern extraction from Metamath objects

**Phase 5-8: Kernel Soundness** (`Metamath.KernelClean`)
- Stepwise proof that each verifier operation maintains mathematical soundness
- Main theorem: `verify_impl_sound` - proves parser success implies valid theorem

### Critical Dependencies

**Error Monotonicity Pattern**:
- Once parser sets error, it persists to final state (`feed_stops_on_error`)
- Used in all parser correctness proofs via proof-by-contradiction
- If assumption contradicts a parser check → check would fail → error would be set → contradiction with "no error"

**Master Key Lemma** (`feedAll_hyps_from_valid_inserts`):
- Proven in Phase 3 (1-line direct proof)
- States: If parsing succeeds, every object in final DB came from valid insert
- Provides witness needed to show objects satisfy parser-enforced invariants

## File Organization

### Core Implementation (Do Not Modify)
- `Metamath/Verify.lean` (900+ lines) - Parser implementation with all checks
- `Metamath/Spec.lean` - Mathematical specification

### Proof Modules (Active Development)
- `Metamath/ParserInvariants.lean` - Parser correctness: where floats come from, their structure
- `Metamath/ParserLoopInduction.lean` - Infrastructure for feed loop induction proofs
- `Metamath/ParserProofs.lean` - Proof sketches for parser axiom conversion
- `Metamath/KernelClean.lean` - Main soundness proof (150+ KB file)

### Helper Modules
- `Metamath/ArrayListExt.lean` - Array/list lemmas for Batteries 4.24.0
- `Metamath/AllM.lean` - Fully-proven allM extraction lemmas
- `Metamath/Bridge/*.lean` - Implementation-to-spec bridges
- `Metamath/DBCaseAnalysis.lean` - Case analysis patterns for DB operations

## Current Proof Status

### ✅ Proven (Complete Proofs)
- Master key lemma `feedAll_hyps_from_valid_inserts` (1-line proof)
- Error monotonicity infrastructure (feed_stops_on_error, feedAll_error_monotonic)
- Step 1 & 2 positive cases (using pattern matching and by_cases)
- 50+ helper lemmas

### 📝 In Progress (Blocked on Missing Lemmas)

**Step 1 Negative Cases (3 sorries)**:
```
1. f.size ≠ 2 case     → Blocked by: feedTokens_is_only_float_source
2. f[0]! = var case    → Blocked by: feedTokens_is_only_float_source
3. f[1]! = const case  → Blocked by: feedTokens_is_only_float_source
```

**Step 2 Negative Case (1 sorry)**:
```
1. vi = vj case        → Blocked by: feedTokens_is_only_float_source + insertHyp_call_order proof
```

**The Critical Blocker**: `feedTokens_is_only_float_source` (ParserProofs.lean:1429)
- **What it proves**: Floats can ONLY be inserted via feedTokens.float case (line 613)
- **Why needed**: Line 613 only reachable after line 611 check (arr.size==2), so floats must have size 2
- **Proof required**: Induction over feedAll execution showing line 613 is exhaustive source
- **Estimated effort**: 3-4 hours of parser loop induction

### ❌ Not Started
- Step 3 & 4 (Frame induction frameworks, main theorem integration)
- ~130 sorries in other modules (lower priority)

## Key Proof Patterns

### Proof-by-Contradiction Pattern (Used Everywhere)
```lean
exfalso  -- Setup to prove False
-- Assume negative case (e.g., f.size ≠ 2)
-- Trace parser code showing mkError would be called
-- Use feed_stops_on_error to show error persists
-- Derive: db.error? ≠ none
-- But h_success says: db.error? = none
-- Contradiction! ✓
```

### Code Path Tracing Pattern
1. Find the check in Verify.lean (e.g., line 611: `arr.size == 2`)
2. Show if assumption contradicts the check (f.size ≠ 2)
3. If check fails, mkError is called (line 612)
4. Apply feed_stops_on_error: error persists to final state
5. Contradiction with "parsing succeeded" (no error in final state)

### Parser State Machine Induction
```lean
-- Induction over feedAll execution:
-- Base: Initial state has no floats
-- Step: feedAll can only add floats via feedTokens.float (lines 610-614)
--       Line 607 check: arr.size > 0 && !arr[0]!.isVar
--       Line 611 check: arr.size == 2 && arr[1]!.isVar
--       Only then insertHyp called, so new float satisfies checks
-- Conclusion: All floats in final DB satisfy structure checks
```

## Verify.lean: The Ground Truth

**Key Sections to Understand**:

- **Lines 605-614**: feedTokens function
  - Line 607: Float precondition (first must be const)
  - Line 610-614: Float case
  - Line 611: Float size check (arr.size == 2 && arr[1]!.isVar)
  - Line 613: Only place where insertHyp called with ess=false

- **Lines 296-310**: insertHyp function
  - Lines 303-306: Duplicate check loop
  - Line 310: withHyps - frame.hyps grows by one element

- **Lines 762-790**: feed function (main parser loop)
  - Line 777-779: Error checking (if error set, keep it set and return)
  - Shows error is "sticky"

- **Lines 792-799**: feedAll function
  - Chains feed calls for byte sequence
  - Maintains error monotonicity

**When unsure about parser behavior**: Consult these line numbers in Verify.lean to verify code path logic.

## Common Development Tasks

### Adding a New Parser Invariant Theorem

1. State the theorem in `ParserInvariants.lean` (e.g., "Parser success implies property X")
2. Mark negative cases with `exfalso` and `sorry`
3. Document the proof sketch in comments:
   - Verify.lean line where check happens
   - How assuming negation contradicts the check
   - How feed_stops_on_error applies
4. For positive cases, use pattern matching where possible (proven by `rfl`)

### Completing a Blocked Sorry

Most blocked sorries follow this pattern:

```lean
sorry  -- Blocked by: feedTokens_is_only_float_source proof (parser loop induction)
```

Check what lemma blocks it, then work up the dependency chain.

### Debugging Build Failures

1. Check if it's a type error or unsolved goals:
   ```bash
   lake build 2>&1 | grep -A 10 "error:"
   ```

2. For unsolved goals, the error shows the goal state. Look for:
   - Type mismatches (usually indicate wrong lemma applied)
   - Missing hypotheses (need to introduce them with `intro` or pattern matching)

3. Use `sorry` temporarily to see if downstream depends on this proof

## Important Notes for Next Sessions

### Master Key Lemma is Proven ✓
Don't reprove `feedAll_hyps_from_valid_inserts` - it's done (1-line direct proof using final DB as witness).

### The Real Blocker is Parser Exhaustiveness
The 4 ParserInvariants sorries don't need loop induction separately - they all depend on proving feedTokens is the exclusive source of floats. Once `feedTokens_is_only_float_source` is proven, all 4 sorries follow mechanically.

### Build Health is Critical
Always build before committing. Build should show:
```
Build completed successfully (59 jobs)
```
With only expected warnings about sorries.

### Document Proof-by-Contradiction Clearly
When a sorry uses proof-by-contradiction, document:
1. What assumption leads to contradiction
2. Which Verify.lean lines contain the check
3. How the contradiction arises (check fails → mkError → error persists)

### Pattern Matching is Your Friend
For union types (Sym, Object, etc.), pattern matching often completes proofs by `rfl`. The unreachable cases become `exfalso` + `sorry` with clear justification.

## References

- **Previous Session Summary**: See `/tmp/SESSION_2025_11_15_CONTINUATION.md` and `/tmp/CURRENT_STATUS_2025_11_15.md`
- **STATUS.md**: Current project status and completed work
- **Verify.lean lines 605-799**: Parser implementation (consult frequently)

---

**Last Updated**: 2025-11-15 (After identifying feedTokens_is_only_float_source as the critical blocker)

**Build Status**: ✅ 59/59 jobs passing, 0 errors, ~130 sorries remaining

**Next Critical Task**: Prove feedTokens_is_only_float_source via feedAll loop induction (~3-4 hours)
