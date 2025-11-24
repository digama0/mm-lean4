/-
# Metamath.ParserOperations

Proofs that parser operations can be modeled as structure-preserving operations.

This connects the parser implementation (Verify.lean) to the correctness infrastructure.

## Strategy

For each parser operation (insertHyp, insertAssert, etc.), we prove that **given**
the parser has validated inputs correctly, **then** the operation maintains WellFormedDB.

The validation conditions become hypotheses that the parser must prove when calling these operations.

This bridges parser implementation → StructurePreservingOp → WellFormedDB.
-/

import Metamath.Verify
import Metamath.ParserCorrectness
import Metamath.WellFormedness

namespace Metamath
namespace ParserOps

open Verify
open WF
open ParserCorrectness

/-! ## Core Lemmas

These establish the key properties needed to model parser operations as StructurePreservingOps.
-/

/-- Constructing a StructurePreservingOp for insertHyp's insert operation.
    Given parser validation, the insert of a hyp object preserves structure. -/
theorem insertHyp_insert_is_structure_preserving
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
    -- Parser validation: formula is well-formed
    (h_validates : (ess = false → WellFormedFloat f) ∧ (ess = true → WellFormedFormula f))
    -- Parser freshness: label doesn't exist yet
    (h_fresh_db : db.find? l = none)
    -- Parser freshness: label not in current frame
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    -- Parser freshness: label not in any assertion frame
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l) :
    StructurePreservingOp db (fun db' => db'.insert pos l (fun _ => .hyp ess f l)) := by
  apply StructurePreservingOp.insert
  · -- h_validated: prove the object is well-formed
    cases ess with
    | false => exact h_validates.1 rfl
    | true => exact h_validates.2 rfl
  · -- h_obj_var_names_match: trivial for hyp (not a var)
    intro lbl v h_eq
    -- h_eq : (fun _ => Object.hyp ess f l) lbl = Object.var v
    -- But .hyp ≠ .var, so this is a contradiction
    cases h_eq
  · -- h_fresh_db
    exact h_fresh_db
  · -- h_fresh_label
    exact h_fresh_label
  · -- h_fresh_in_asserts
    exact h_fresh_in_asserts

/-! ## Main Theorems

These show that parser operations maintain WellFormedDB by composing structure-preserving operations.
-/

/-- insertHyp maintains WellFormedDB when parser has validated inputs -/
theorem insertHyp_maintains_wf_with_validation
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    -- Parser provides these guarantees:
    (h_validates : (ess = false → WellFormedFloat f) ∧ (ess = true → WellFormedFormula f))
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    -- And insert succeeds:
    (h_insert_ok : (db.insert pos l (fun _ => .hyp ess f l)).error? = none)
    -- Then insertHyp maintains WF:
    -- (Note: we're proving for just the insert part, not the full insertHyp with withHyps)
    : WellFormedDB (db.insert pos l (fun _ => .hyp ess f l)) := by
  -- Use the StructurePreservingOp we just constructed
  have h_struct := insertHyp_insert_is_structure_preserving db pos l ess f
    h_validates h_fresh_db h_fresh_label h_fresh_in_asserts
  exact structure_preserving_maintains_wf db h_struct h_wf h_no_err_before h_insert_ok

/-- Constructing a StructurePreservingOp for insertAxiom's insert operation.
    Given parser validation, the insert of an assert object preserves structure. -/
theorem insertAxiom_insert_is_structure_preserving
    (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame)
    -- Parser validation: formula is well-formed and frame is well-formed for all DBs
    (h_validates : WellFormedFormula fmla ∧ (∀ db_any, WellFormedFrame db_any fr))
    -- Parser freshness: label doesn't exist yet
    (h_fresh_db : db.find? l = none)
    -- Parser freshness: label not in current frame
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    -- Parser freshness: label not in any assertion frame
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla' : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla' fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l) :
    StructurePreservingOp db (fun db' => db'.insert pos l (fun _ => .assert fmla fr l)) := by
  apply StructurePreservingOp.insert
  · -- h_validated: prove the object is well-formed
    exact ⟨h_validates.1, h_validates.2⟩
  · -- h_obj_var_names_match: trivial for assert (not a var)
    intro lbl v h_eq
    cases h_eq
  · -- h_fresh_db
    exact h_fresh_db
  · -- h_fresh_label
    exact h_fresh_label
  · -- h_fresh_in_asserts
    exact h_fresh_in_asserts

/-- insertAxiom maintains WellFormedDB when parser has validated inputs -/
theorem insertAxiom_maintains_wf_with_validation
    (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    -- Parser provides these guarantees:
    (h_validates : WellFormedFormula fmla ∧ (∀ db_any, WellFormedFrame db_any fr))
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla' : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla' fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    -- And insert succeeds:
    (h_insert_ok : (db.insert pos l (fun _ => .assert fmla fr l)).error? = none) :
    WellFormedDB (db.insert pos l (fun _ => .assert fmla fr l)) := by
  -- Use the StructurePreservingOp we just constructed
  have h_struct := insertAxiom_insert_is_structure_preserving db pos l fmla fr
    h_validates h_fresh_db h_fresh_label h_fresh_in_asserts
  exact structure_preserving_maintains_wf db h_struct h_wf h_no_err_before h_insert_ok

/-- Constructing a StructurePreservingOp for insertConst operation.
    Constants have trivial validation (True). -/
theorem insertConst_is_structure_preserving
    (db : DB) (pos : Pos) (l : String)
    -- Parser freshness: label doesn't exist yet
    (h_fresh_db : db.find? l = none)
    -- Parser freshness: label not in current frame
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    -- Parser freshness: label not in any assertion frame
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l) :
    StructurePreservingOp db (fun db' => db'.insert pos l (fun _ => .const l)) := by
  apply StructurePreservingOp.insert
  · -- h_validated: trivial for const
    trivial
  · -- h_obj_var_names_match: trivial for const (not a var)
    intro lbl v h_eq
    cases h_eq
  · -- h_fresh_db
    exact h_fresh_db
  · -- h_fresh_label
    exact h_fresh_label
  · -- h_fresh_in_asserts
    exact h_fresh_in_asserts

/-- insertConst maintains WellFormedDB -/
theorem insertConst_maintains_wf
    (db : DB) (pos : Pos) (l : String)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_insert_ok : (db.insert pos l (fun _ => .const l)).error? = none) :
    WellFormedDB (db.insert pos l (fun _ => .const l)) := by
  have h_struct := insertConst_is_structure_preserving db pos l
    h_fresh_db h_fresh_label h_fresh_in_asserts
  exact structure_preserving_maintains_wf db h_struct h_wf h_no_err_before h_insert_ok

/-- Constructing a StructurePreservingOp for insertVar operation.
    Variables must satisfy the label=name invariant. -/
theorem insertVar_is_structure_preserving
    (db : DB) (pos : Pos) (l : String)
    -- Parser freshness: label doesn't exist yet
    (h_fresh_db : db.find? l = none)
    -- Parser freshness: label not in current frame
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    -- Parser freshness: label not in any assertion frame
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l) :
    StructurePreservingOp db (fun db' => db'.insert pos l (fun lbl => .var lbl)) := by
  apply StructurePreservingOp.insert
  · -- h_validated: var requires v = label, which holds when obj lbl = .var lbl
    rfl
  · -- h_obj_var_names_match: for vars with (fun lbl => .var lbl), this is automatic
    intro lbl v h_eq
    -- h_eq : (fun lbl => Object.var lbl) lbl = Object.var v
    -- So lbl = v, which is exactly what we need!
    simp only at h_eq
    cases h_eq
    rfl
  · -- h_fresh_db
    exact h_fresh_db
  · -- h_fresh_label
    exact h_fresh_label
  · -- h_fresh_in_asserts
    exact h_fresh_in_asserts

/-- insertVar maintains WellFormedDB -/
theorem insertVar_maintains_wf
    (db : DB) (pos : Pos) (l : String)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_insert_ok : (db.insert pos l (fun lbl => .var lbl)).error? = none) :
    WellFormedDB (db.insert pos l (fun lbl => .var lbl)) := by
  have h_struct := insertVar_is_structure_preserving db pos l
    h_fresh_db h_fresh_label h_fresh_in_asserts
  exact structure_preserving_maintains_wf db h_struct h_wf h_no_err_before h_insert_ok

/-! ## Parser Provides Witnesses

These theorems show that the parser's validation checks ensure the witnesses
required by the structure-preserving theorems above.
-/

/-- Parser's validation checks for floats ensure WellFormedFloat.

The parser checks (Verify.lean:607-612):
1. arr.size > 0 && !arr[0]!.isVar  (line 607-608)
2. arr.size == 2 && arr[1]!.isVar  (line 611-612)

These checks ensure WellFormedFloat: arr.size = 2 ∧ arr[0] is const ∧ arr[1] is var
-/
theorem parser_float_checks_imply_wellformed
    (arr : Array Sym)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_second : arr.size = 2 ∧ arr[1]!.isVar) :
    WellFormedFloat arr := by
  -- Extract the individual checks
  have h_size := h_second.1
  have h_not_var_0 := h_first.2
  have h_is_var_1 := h_second.2

  -- Prove WellFormedFloat: arr.size = 2 ∧ ∃ c v, arr[0]! = .const c ∧ arr[1]! = .var v
  constructor
  · -- Size = 2
    exact h_size
  · -- Existential witnesses
    -- The check !arr[0]!.isVar means arr[0]! = .const c for some c
    -- The check arr[1]!.isVar means arr[1]! = .var v for some v
    have ⟨c, h_const⟩ : ∃ c, arr[0]! = Sym.const c := by
      cases h : arr[0]! with
      | const c => exact ⟨c, rfl⟩
      | var _ =>
          exfalso
          rw [h] at h_not_var_0
          simp only [Sym.isVar] at h_not_var_0
          -- h_not_var_0 : (!true) = true, which is false = true
          cases h_not_var_0

    have ⟨v, h_var⟩ : ∃ v, arr[1]! = Sym.var v := by
      cases h : arr[1]! with
      | var v => exact ⟨v, rfl⟩
      | const _ =>
          exfalso
          rw [h] at h_is_var_1
          simp only [Sym.isVar] at h_is_var_1
          -- h_is_var_1 : false = true
          cases h_is_var_1

    exact ⟨c, v, h_const, h_var⟩

/-- Parser's validation checks for essential formulas ensure WellFormedFormula.

The parser checks (Verify.lean:607-608):
1. arr.size > 0 && !arr[0]!.isVar  (line 607-608)

These checks ensure WellFormedFormula: arr.size > 0 ∧ arr[0] is const
-/
theorem parser_essential_checks_imply_wellformed
    (arr : Array Sym)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar) :
    WellFormedFormula arr := by
  -- Prove WellFormedFormula: arr.size > 0 ∧ ∃ c, arr[0]! = .const c
  constructor
  · -- Size > 0
    exact h_first.1
  · -- Existential witness for const
    have h_not_var_0 := h_first.2
    cases h : arr[0]! with
    | const c => exact ⟨c, rfl⟩
    | var _ =>
        exfalso
        rw [h] at h_not_var_0
        simp only [Sym.isVar] at h_not_var_0
        cases h_not_var_0

/-! ## Convenience Theorems

These wire the parser witness theorems directly into the structure-preserving theorems,
eliminating the abstract validation hypotheses.
-/

/-- insertHyp maintains WellFormedDB when given parser's concrete boolean checks.
    This is the convenient form that directly uses parser implementation details. -/
theorem insertHyp_maintains_wf_from_parser_checks
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    -- Parser boolean checks (directly from Verify.lean:607-612):
    (h_first : f.size > 0 ∧ !f[0]!.isVar)
    (h_second : f.size = 2 ∧ f[1]!.isVar)
    -- Freshness (same as before):
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    -- And insert succeeds:
    (h_insert_ok : (db.insert pos l (fun _ => .hyp ess f l)).error? = none)
    -- For float hypothesis (ess = false):
    (h_is_float : ess = false) :
    WellFormedDB (db.insert pos l (fun _ => .hyp ess f l)) := by
  -- Convert parser boolean checks to WellFormedFloat using our witness theorem
  have h_validates : (ess = false → WellFormedFloat f) ∧ (ess = true → WellFormedFormula f) := by
    constructor
    · intro _
      -- Use the witness theorem we just proved!
      exact parser_float_checks_imply_wellformed f h_first h_second
    · intro h_ess_true
      -- Contradiction: we know ess = false
      rw [h_is_float] at h_ess_true
      cases h_ess_true
  -- Apply the existing theorem with the validation witness
  exact insertHyp_maintains_wf_with_validation db pos l ess f
    h_wf h_no_err_before h_validates h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok

/-- Unified convenience theorem for insertHyp that handles both float and essential formulas.
    This directly uses parser's concrete boolean checks for both cases. -/
theorem insertHyp_maintains_wf_unified
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    -- Parser boolean checks (Verify.lean:607-612):
    (h_first : f.size > 0 ∧ !f[0]!.isVar)
    (h_second : ess = false → (f.size = 2 ∧ f[1]!.isVar))
    -- Freshness:
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    -- Success:
    (h_insert_ok : (db.insert pos l (fun _ => .hyp ess f l)).error? = none) :
    WellFormedDB (db.insert pos l (fun _ => .hyp ess f l)) := by
  -- Derive validation witness by case analysis on ess
  have h_validates : (ess = false → WellFormedFloat f) ∧ (ess = true → WellFormedFormula f) := by
    constructor
    · intro h_ess_false
      -- Float case: use parser_float_checks_imply_wellformed
      have h_second' := h_second h_ess_false
      exact parser_float_checks_imply_wellformed f h_first h_second'
    · intro _
      -- Essential case: use parser_essential_checks_imply_wellformed
      exact parser_essential_checks_imply_wellformed f h_first
  -- Apply the existing theorem
  exact insertHyp_maintains_wf_with_validation db pos l ess f
    h_wf h_no_err_before h_validates h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok

/-- Convenience theorem for insertConst - trivial since constants need no validation.
    This is just an alias for the existing theorem since no parser checks are needed. -/
theorem insertConst_maintains_wf_from_parser
    (db : DB) (pos : Pos) (l : String)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_insert_ok : (db.insert pos l (fun _ => .const l)).error? = none) :
    WellFormedDB (db.insert pos l (fun _ => .const l)) :=
  -- No parser validation needed - constants are trivially well-formed
  insertConst_maintains_wf db pos l h_wf h_no_err_before h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok

/-- Convenience theorem for insertVar - trivial since the label=name invariant is automatic.
    This is just an alias for the existing theorem since no parser checks are needed. -/
theorem insertVar_maintains_wf_from_parser
    (db : DB) (pos : Pos) (l : String)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_insert_ok : (db.insert pos l (fun lbl => .var lbl)).error? = none) :
    WellFormedDB (db.insert pos l (fun lbl => .var lbl)) :=
  -- No parser validation needed - var name matches label by construction
  insertVar_maintains_wf db pos l h_wf h_no_err_before h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok

/-- Convenience theorem for insertAxiom using parser's concrete checks.
    The formula validation uses parser checks; frame well-formedness is assumed for now. -/
theorem insertAxiom_maintains_wf_from_parser
    (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    -- Parser check for formula (same as essential hypothesis):
    (h_fmla_check : fmla.size > 0 ∧ !fmla[0]!.isVar)
    -- Frame well-formedness (from trimFrame' operation):
    (h_frame_wf : WellFormedFrame db fr)
    -- Freshness:
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla' : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla' fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    -- Success:
    (h_insert_ok : (db.insert pos l (fun _ => .assert fmla fr l)).error? = none) :
    WellFormedDB (db.insert pos l (fun _ => .assert fmla fr l)) := by
  -- Derive validation witness
  have h_validates : WellFormedFormula fmla ∧ (∀ db_any, WellFormedFrame db_any fr) := by
    constructor
    · -- Use parser_essential_checks_imply_wellformed
      exact parser_essential_checks_imply_wellformed fmla h_fmla_check
    · -- Frame well-formedness
      -- Note: h_frame_wf gives WellFormedFrame db fr
      -- The abstract framework asks for ∀ db_any, which is a quirk
      -- For now, we just provide db-specific WF for all db_any
      -- TODO: Fix abstract framework to use WellFormedFrame db fr instead
      intro db_any
      -- This is a type mismatch we're papering over
      -- The frame fr was extracted from db, not from db_any!
      sorry
  -- Apply the existing theorem
  exact insertAxiom_maintains_wf_with_validation db pos l fmla fr
    h_wf h_no_err_before h_validates h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok

/-! ## Parser Execution

These theorems connect the convenience theorems to the actual parser execution in feedTokens.
-/

/-- The insert part of insertHyp maintains WellFormedDB.
    This is the core theorem connecting parser checks to DB well-formedness. -/
theorem insertHyp_insert_part_maintains_wf
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (arr : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err : db.error? = none)
    -- Parser checks:
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_second : ess = false → (arr.size = 2 ∧ arr[1]!.isVar))
    -- Freshness:
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    -- Insert succeeds:
    (h_insert_ok : (db.insert pos l (fun _ => .hyp ess arr l)).error? = none) :
    WellFormedDB (db.insert pos l (fun _ => .hyp ess arr l)) := by
  -- Direct application of our unified convenience theorem!
  exact insertHyp_maintains_wf_unified db pos l ess arr
    h_wf h_no_err h_first h_second
    h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok

/-- The insert part of insertAxiom maintains WellFormedDB.
    This is the core theorem for axiom/theorem declarations. -/
theorem insertAxiom_insert_part_maintains_wf
    (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame)
    (h_wf : WellFormedDB db)
    (h_no_err : db.error? = none)
    -- Parser checks:
    (h_first : fmla.size > 0 ∧ !fmla[0]!.isVar)
    -- Frame well-formedness (from trimFrame'):
    (h_frame_wf : WellFormedFrame db fr)
    -- Freshness:
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla' : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla' fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    -- Insert succeeds:
    (h_insert_ok : (db.insert pos l (fun _ => .assert fmla fr l)).error? = none) :
    WellFormedDB (db.insert pos l (fun _ => .assert fmla fr l)) := by
  -- Direct application of our axiom convenience theorem!
  exact insertAxiom_maintains_wf_from_parser db pos l fmla fr
    h_wf h_no_err h_first h_frame_wf
    h_fresh_db h_fresh_label h_fresh_in_asserts h_insert_ok

/-! ## feedTokens Correctness

This section proves that feedTokens maintains WellFormedDB for each token kind.
This is the key composition theorem connecting individual operations to parser execution.
-/

/-- feedTokens maintains WellFormedDB when processing tokens.
    This covers all token kinds from Verify.lean:605-627. -/
-- First, we need a helper: insertHyp (full) maintains WellFormedDB
-- This is what we need from Phase A!
theorem insertHyp_full_maintains_wf
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (arr : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err : db.error? = none)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_second : ess = false → (arr.size = 2 ∧ arr[1]!.isVar))
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_success : (db.insertHyp pos l ess arr).error? = none) :
    WellFormedDB (db.insertHyp pos l ess arr) := by
  -- TODO: Phase A1 - Prove full insertHyp maintains WellFormedDB
  -- Strategy:
  --   1. Uniqueness check (float only, lines 298-308 in Verify.lean): error or no-op
  --   2. Insert operation (line 309): Use insertHyp_insert_part_maintains_wf ✅
  --   3. Frame extension (line 310, withHyps): Need withHyps_push_maintains_wf lemma
  -- Compose these three stages!
  sorry

-- Subsequence: arr2 is a subsequence of arr1 if every element in arr2 exists in arr1
-- (preserving the string value, though not necessarily the position)
def IsSubsequence (arr1 arr2 : Array String) : Prop :=
  ∀ (i : Nat) (hi : i < arr2.size), ∃ (j : Nat) (hj : j < arr1.size), arr2[i]'hi = arr1[j]'hj

-- Extraction lemma: trimFrame' success iff trimFrame returned (true, fr)
@[simp]
theorem trimFrame'_ok_iff {db : DB} {fmla : Formula} {fr : Frame} :
    db.trimFrame' fmla = .ok fr ↔ db.trimFrame fmla = (true, fr) := by
  unfold DB.trimFrame'
  obtain ⟨ok, fr'⟩ := db.trimFrame fmla
  sorry  -- TODO: if-then-else iff proof

-- trimFrame produces a subsequence of the input frame's hypothences
theorem trimFrame_produces_subsequence {db : DB} {fmla : Formula} {ok : Bool} {fr : Frame}
    (h : db.trimFrame fmla = (ok, fr)) : IsSubsequence db.frame.hyps fr.hyps := by
  -- trimFrame (Verify.lean:326-337) filters db.frame.hyps by pushing only elements where ess = true
  -- Each pushed element maintains its string value
  -- This creates a subsequence relationship
  sorry  -- TODO: Computational proof - unfold trimFrame and track push-loop invariant

-- Lemma 3: trimFrame preserves UniqueFloatVars (subset monotonicity!)
theorem trimFrame_preserves_uniqueness {db : DB} {fr : Frame}
    (h_subseq : IsSubsequence db.frame.hyps fr.hyps)
    (h_unique : UniqueFloatVars db db.frame) :
    UniqueFloatVars db fr := by
  intro i j hi hj h_ne fi fj lbli lblj h_fi h_fj hsizei hsizej
  -- Get corresponding indices in db.frame
  obtain ⟨i', hi', h_eq_i⟩ := h_subseq i hi
  obtain ⟨j', hj', h_eq_j⟩ := h_subseq j hj
  -- Need to show i' ≠ j' to apply h_unique
  have h_i'_ne_j' : i' ≠ j' := by
    intro h_eq
    -- If i' = j', then db.frame.hyps[i'] = db.frame.hyps[j']
    -- Combined with h_eq_i and h_eq_j, we get fr.hyps[i] = fr.hyps[j]
    -- But i ≠ j for distinct array indices, so this means array has duplicate elements
    -- For arrays built by push-loop, this is impossible
    sorry  -- Needs: subsequence from push-loop is injective on indices
  -- Rewrite to use db.frame.hyps
  rw [h_eq_i] at h_fi
  rw [h_eq_j] at h_fj
  -- Apply uniqueness on db.frame
  exact h_unique i' j' hi' hj' h_i'_ne_j' fi fj lbli lblj h_fi h_fj hsizei hsizej

-- Similarly for insertAxiom (full)
-- TODO: Need to prove frame well-formedness from trimFrame'
theorem trimFrame'_success_implies_wellformed_frame
    (db : DB) (fmla : Formula) (fr : Frame)
    (h_wf : WellFormedDB db)
    (h_trimFrame : db.trimFrame' fmla = .ok fr) :
    WellFormedFrame db fr := by
  -- WellFormedFrame has two parts
  constructor
  · -- Part 1: All hypotheses in fr are HypOK db
    intro i hi
    -- Strategy: fr.hyps is a subsequence of db.frame.hyps, so fr.hyps[i] came from db.frame.hyps
    -- HypOK depends only on the label (via db.find?), not on position in frame

    -- Extract that trimFrame succeeded
    have h_trim : db.trimFrame fmla = (true, fr) := trimFrame'_ok_iff.mp h_trimFrame

    -- Use subsequence lemma
    have h_subseq := trimFrame_produces_subsequence h_trim
    have h_ex := h_subseq i hi
    obtain ⟨j, hj, h_eq⟩ := h_ex

    -- From h_wf, get that db.frame is well-formed
    have ⟨h_frame_wf, _⟩ := h_wf
    have ⟨h_all_hypok, _⟩ := h_frame_wf

    -- Apply to db.frame.hyps[j]
    have h_hypok_j := h_all_hypok j hj

    -- Since fr.hyps[i] = db.frame.hyps[j], and HypOK depends only on the string value
    rw [h_eq]
    exact h_hypok_j

  · -- Part 2: UniqueFloatVars db fr
    -- Extract that trimFrame succeeded
    have h_trim : db.trimFrame fmla = (true, fr) := trimFrame'_ok_iff.mp h_trimFrame

    -- Get subsequence property
    have h_subseq := trimFrame_produces_subsequence h_trim

    -- Get UniqueFloatVars for db.frame
    have ⟨h_frame_wf, _⟩ := h_wf
    have ⟨_, h_unique_frame⟩ := h_frame_wf

    -- Apply the uniqueness preservation lemma!
    exact trimFrame_preserves_uniqueness h_subseq h_unique_frame

theorem insertAxiom_full_maintains_wf
    (db : DB) (pos : Pos) (l : String) (arr : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err : db.error? = none)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_fresh_db : db.find? l = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size), db.frame.hyps[i]'hi ≠ l)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ l)
    (h_success : (db.insertAxiom pos l arr).error? = none) :
    WellFormedDB (db.insertAxiom pos l arr) := by
  -- TODO: Complete insertAxiom_full proof
  -- Strategy (GPT-5's case analysis is correct!):
  --   1. Unfold DB.insertAxiom (match on trimFrame')
  --   2. Case .error msg: mkError sets error?, contradicts h_success
  --   3. Case .ok fr: case on interrupt
  --      a. true: sets error?, contradicts h_success
  --      b. false: apply insertAxiom_insert_part_maintains_wf
  --
  -- Challenge: split tactic doesn't preserve equalities between h_success and goal
  -- Need either:
  --   - Better tactic usage (cases? generalize?)
  --   - Helper lemma that explicitly cases on trimFrame' result
  --   - Work with match expression directly
  sorry

-- Phase B: feedTokens correctness (blocked on Phase A completion)
-- TODO: Complete after proving insertHyp_full and insertAxiom_full
theorem feedTokens_maintains_wf
    (s : ParserState) (arr : Array Sym) (tokp : TokensParser)
    (h_wf : WellFormedDB s.db)
    (h_no_err : s.db.error? = none)
    (h_first : arr.size > 0 ∧ !arr[0]!.isVar)
    (h_float : tokp.k = TokensKind.float → (arr.size = 2 ∧ arr[1]!.isVar))
    (h_fresh_db : s.db.find? tokp.label = none)
    (h_fresh_label : ∀ (i : Nat) (hi : i < s.db.frame.hyps.size), s.db.frame.hyps[i]'hi ≠ tokp.label)
    (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        s.db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), fr_assert.hyps[i]'hi ≠ tokp.label)
    (h_success : (s.feedTokens arr tokp).db.error? = none) :
    WellFormedDB (s.feedTokens arr tokp).db := by
  -- TODO: Phase B - Case analysis on token kind
  -- Strategy: cases tokp.k with
  --   | .float => apply insertHyp_full_maintains_wf (once Phase A is done!)
  --   | .ess   => apply insertHyp_full_maintains_wf
  --   | .ax    => apply insertAxiom_full_maintains_wf
  --   | .thm   => [proof checking - separate work]
  sorry

end ParserOps
end Metamath

