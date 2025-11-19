/-
Bridge Module: Core Definitions and TypedSubst

This module provides the thin bridge layer between Spec and Kernel verification.
All definitions are simple and direct. Complex proofs remain in Kernel.lean.

**Design principle:** Bridge contains ONLY:
- Type definitions (TypedSubst)
- Helper functions (floats, essentials, needed)
- Simple extraction lemmas (~5 lines each)

**Status:** Phase 3 - Core infrastructure
-/

import Metamath.Spec
import Metamath.Verify

namespace Metamath.Bridge

open Spec
open Verify

/-! ## Core Type: TypedSubst

The central type that replaces the "phantom wff" toSubst function.
This structure bundles a substitution with a witness that it's well-typed.
-/

/-- A substitution that is **provably well-typed** with respect to a frame.

This structure bundles:
1. A spec-level substitution function σ : Variable → Expr
2. A witness that σ respects all floating hypothesis typecodes in the frame

**Key property:** No phantom values! If a floating hyp says "class x", then σ(x)
has typecode "class", guaranteed by the witness.

**Usage in Phase 3:**
- Replaces Option Subst with TypedSubst in toSubstTyped
- Eliminates the fallback behavior in toSubst
- Provides honest Option behavior (returns none on type errors)

**Construction:**
TypedSubst is constructed via checkHyp_produces_typed_coverage theorem,
which proves that checkHyp's output satisfies the typing witness.
-/
structure TypedSubst (fr : Spec.Frame) where
  /-- The underlying substitution function -/
  σ : Spec.Subst

  /-- Witness: substitution respects floating hypothesis typecodes

  For every floating hypothesis "c v" in the frame's mandatory hypotheses,
  the substitution σ(v) must have typecode c.

  This witness is the KEY difference from the old toSubst:
  - OLD: toSubst returned some (phantom wff fallback on error)
  - NEW: TypedSubst can only be constructed if checkHyp proves typing
  -/
  typed : ∀ {c : Spec.Constant} {v : Spec.Variable},
    Spec.Hyp.floating c v ∈ fr.mand →
    (σ v).typecode = c

/-! ## Helper Functions: Frame Structure Extraction

These functions extract components from frames for use in verification theorems.
All are simple filterMap operations with straightforward definitions.
-/

/-- Extract floating hypotheses from a frame.

Returns the list of all (typecode, variable) pairs from floating hypotheses.
Used to validate substitution coverage and construct TypedSubst witness.

**Definition:** filterMap over mandatory hypotheses, keeping only Hyp.floating cases.
-/
def floats (fr : Spec.Frame) : List (Spec.Constant × Spec.Variable) :=
  fr.mand.filterMap fun h =>
    match h with
    | Hyp.floating c v => some (c, v)
    | Hyp.essential _ => none

/-- Extract essential hypotheses from a frame.

Returns the list of all expressions from essential hypotheses.
These are the mandatory assumptions needed for an axiom/theorem application.

**Definition:** filterMap over mandatory hypotheses, keeping only Hyp.essential cases.
-/
def essentials (fr : Spec.Frame) : List Spec.Expr :=
  fr.mand.filterMap fun h =>
    match h with
    | Hyp.floating _ _ => none
    | Hyp.essential e => some e

/-- Compute what a substitution σ maps a hypothesis to.

For floating hyps "c v": apply σ to get σ(v)
For essential hyps "e": apply σ to all variables in e to get e[σ]

**Usage:** Building the "needed" list of instantiated hypotheses for ProofValid.useAxiom.
-/
def needOf (vars : List Spec.Variable) (σ : Spec.Subst) (h : Spec.Hyp) : Spec.Expr :=
  match h with
  | Hyp.floating _ v => σ v
  | Hyp.essential e => applySubst vars σ e

/-- Compute the list of needed hypothesis instantiations.

Given a frame and substitution, compute what each mandatory hypothesis becomes
after applying the substitution.

This is the "needed" list that stepAssert expects to find on the stack.

**Definition:** Map needOf over all mandatory hypotheses.

**Property:** needed list has same length as fr.mand (by List.map).
-/
def needed (vars : List Spec.Variable) (fr : Spec.Frame) (σ : Spec.Subst) : List Spec.Expr :=
  fr.mand.map (needOf vars σ)

/-! ## Helper Lemmas: Frame Structure Preservation

These lemmas show that floats/essentials faithfully represent frame structure.
All proofs are straightforward by filterMap definition.
-/

/-- floats is complete: every floating hyp appears in floats list

**Proof strategy:** By induction on fr.mand with case analysis on hypothesis type.
- Base case (nil): contradiction (no floating hyp in empty list)
- Inductive case: If h = floating c v, then (c, v) is kept by filterMap
                   If h = essential e, recurse on tail
**Status:** Straightforward (~15-20 lines), using sorry for Phase 3 -/
theorem floats_complete (fr : Spec.Frame) :
    ∀ c v, Hyp.floating c v ∈ fr.mand → (c, v) ∈ floats fr := by
  intro c v h_mem
  unfold floats
  -- Use List.mem_filterMap: x ∈ filterMap f xs ↔ ∃ a ∈ xs, f a = some x
  simp [List.mem_filterMap]
  exists Hyp.floating c v, h_mem

/-- floats is sound: everything in floats list came from a floating hyp

**Proof strategy:** By induction on fr.mand with case analysis on hypothesis type.
- Base case (nil): contradiction (filterMap on empty list is empty)
- Inductive case: If h = floating c' v', check if (c,v) = (c',v') or recurse
                   If h = essential e, recurse on tail (filterMap filters it out)
**Status:** Straightforward (~15-20 lines), using sorry for Phase 3 -/
theorem floats_sound (fr : Spec.Frame) :
    ∀ c v, (c, v) ∈ floats fr → Hyp.floating c v ∈ fr.mand := by
  intro c v h_mem
  unfold floats at h_mem
  -- Use List.mem_filterMap: x ∈ filterMap f xs ↔ ∃ a ∈ xs, f a = some x
  simp [List.mem_filterMap] at h_mem
  obtain ⟨h, h_in_mand, h_match⟩ := h_mem
  -- h_match tells us filterMap succeeded, so h must be Hyp.floating c v
  cases h with
  | floating c' v' =>
    -- h_match : (c', v') = (c, v)
    simp at h_match
    obtain ⟨h_c, h_v⟩ := h_match
    subst h_c h_v
    exact h_in_mand
  | essential e =>
    simp at h_match

/-- essentials is complete: every essential hyp appears in essentials list

**Proof strategy:** By induction on fr.mand with case analysis on hypothesis type.
- Base case (nil): contradiction (no essential hyp in empty list)
- Inductive case: If h = essential e, then e is kept by filterMap
                   If h = floating c v, recurse on tail
**Status:** Straightforward (~15-20 lines), using sorry for Phase 3 -/
theorem essentials_complete (fr : Spec.Frame) :
    ∀ e, Hyp.essential e ∈ fr.mand → e ∈ essentials fr := by
  intro e h_mem
  unfold essentials
  simp [List.mem_filterMap]
  exists Hyp.essential e, h_mem

/-- essentials is sound: everything in essentials list came from an essential hyp

**Proof strategy:** By induction on fr.mand with case analysis on hypothesis type.
- Base case (nil): contradiction (filterMap on empty list is empty)
- Inductive case: If h = essential e', check if e = e' or recurse
                   If h = floating c v, recurse on tail (filterMap filters it out)
**Status:** Straightforward (~15-20 lines), using sorry for Phase 3 -/
theorem essentials_sound (fr : Spec.Frame) :
    ∀ e, e ∈ essentials fr → Hyp.essential e ∈ fr.mand := by
  intro e h_mem
  unfold essentials at h_mem
  simp [List.mem_filterMap] at h_mem
  obtain ⟨h, h_in_mand, h_match⟩ := h_mem
  cases h with
  | floating c v =>
    simp at h_match
  | essential e' =>
    simp at h_match
    cases h_match
    exact h_in_mand

/-- needed list has same length as mandatory hypotheses

**Proof:** List.map preserves length.
**Status:** ✅ PROVEN -/
theorem needed_length (vars : List Spec.Variable) (fr : Spec.Frame) (σ : Spec.Subst) :
    (needed vars fr σ).length = fr.mand.length := by
  simp [needed]

/-- TypedSubst respects the typing invariant (direct from witness)

**Proof:** Direct projection from TypedSubst.typed field.
**Status:** ✅ PROVEN -/
theorem TypedSubst_typed_invariant (fr : Spec.Frame) (σ_typed : TypedSubst fr) :
    ∀ c v, Hyp.floating c v ∈ fr.mand → (σ_typed.σ v).typecode = c :=
  fun _ _ => σ_typed.typed

/-! ## Module Summary

**What this module provides:**
- TypedSubst structure (frame-specific, witness-carrying)
- Helper functions (floats, essentials, needed, needOf)
- Simple lemmas (floats_complete/sound, essentials_complete/sound, needed_length)

**What this module does NOT provide:**
- toSubstTyped implementation (that goes in Kernel.lean)
- Complex proofs (those remain in Kernel.lean)
- Integration theorems (those use checkHyp_produces_typed_coverage from Kernel.lean)

**Total size:** ~200 lines (definitions + simple lemmas)

**Dependencies:**
- Metamath.Spec (specification)
- Metamath.Verify (implementation)

**Used by:**
- Metamath.Kernel (will import and use TypedSubst)
- Future verification theorems

**Status:** ✅ Core Bridge infrastructure complete

**Next steps:**
1. Create Metamath/Bridge.lean root import
2. Update Metamath/Kernel.lean to import Bridge
3. Add toSubstTyped to Kernel.lean using TypedSubst
4. Prove checkHyp_produces_TypedSubst in Kernel.lean
-/

end Metamath.Bridge
