# STRICT AXIOM POLICY

**This file establishes mandatory rules for working with axioms in this project.**

## Core Rule

**NEVER claim an axiom has been eliminated unless you have verified with `rg "^axiom axiom_name"` that it no longer exists as an axiom in the codebase.**

## Before Claiming Completion

When you believe you've eliminated an axiom, you MUST:

1. **Verify with grep:**
   ```bash
   rg "^axiom axiom_name" Metamath/
   ```
   If this returns ANY results, the axiom is NOT eliminated.

2. **Verify it's now a theorem:**
   ```bash
   rg "^theorem axiom_name" Metamath/
   ```
   This MUST return results for the axiom to be considered proven.

3. **Verify build succeeds:**
   ```bash
   lake build
   ```
   Must complete without errors.

4. **Count remaining axioms:**
   ```bash
   rg "^axiom " Metamath/{KernelClean,Spec}.lean | wc -l
   ```
   Report the ACTUAL count, not a guess.

## Reporting Progress

When reporting status to the user:

- ✅ **CORRECT:** "`getElem!_idxOf` is now a proven theorem (verified with rg)"
- ❌ **WRONG:** "We completed `checkHyp_operational_semantics`" (without verification)
- ✅ **CORRECT:** "9 axioms remain (verified count from rg)"
- ❌ **WRONG:** "We're down to 7 axioms" (without running rg)

## Status Reports Must Include

Every status report MUST include:
```bash
# Actual axiom count
rg "^axiom " Metamath/{KernelClean,Spec}.lean | wc -l

# List of remaining axioms
rg "^axiom " Metamath/KernelClean.lean
rg "^axiom " Metamath/Spec.lean
```

## When Working on Axioms

1. **Before starting:** Confirm the axiom exists with `rg`
2. **Research first:** Use WebSearch to look up Lean 4 tactics, proof strategies, and similar theorems
3. **While working:** Use `sorry` temporarily, NEVER new axioms
4. **After completing:** Verify with the 4-step checklist above
5. **Report honestly:** If you hit a blocker, SAY SO - don't pretend it's done

## Web Search Policy

**Proactively use WebSearch when:**
- You need Lean 4 tactic documentation (e.g., "Lean 4 induction tactic", "Lean 4 cases syntax")
- You're stuck on a proof and need examples (e.g., "Lean 4 list fold induction proof")
- You need to understand mathlib lemmas (e.g., "Lean 4 List.foldlM lemmas")
- You encounter unfamiliar Lean 4 syntax or errors

**Do NOT wait for the user to tell you to search.** If you don't know something about Lean 4, look it up immediately.

## Absolute Prohibitions

**NEVER:**
- Claim an axiom is eliminated without running `rg` to verify
- Introduce new axioms without explicit user approval
- Use `axiom` to work around proof difficulties (use `sorry` instead)
- Report progress based on intention rather than verification

## Why This Matters

The user is relying on accurate status reports to:
- Track progress toward zero axioms
- Plan next steps
- Make decisions about the project

**Inaccurate reports waste the user's time and break trust.**

## Enforcement

This policy is **mandatory**. Any violation should be immediately corrected with:
1. Honest acknowledgment of the error
2. Actual verified status
3. Correction of any documentation that relied on the false claim

## Current Verified Status (2025-11-09)

```
Axioms remaining: 9
- KernelClean.lean: 7 axioms
- Spec.lean: 2 axioms

Recently completed (VERIFIED):
✅ mapM_get_some - now a theorem
✅ getElem!_idxOf - now a theorem

Still axioms (VERIFIED):
❌ checkHyp_operational_semantics - still an axiom
❌ toFrame_float_correspondence - still an axiom
❌ toSubstTyped_of_allM_true - still an axiom
❌ 3 substitution axioms - still axioms
❌ compressed_proof_sound - still an axiom
❌ 2 spec combinators - still axioms
```

---

**Last updated:** 2025-11-09
**Policy version:** 1.0
