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
    -- TODO: Prove this from trimFrame' properties using existing AllM lemmas
    (h_frame_wf : ∀ db_any, WellFormedFrame db_any fr)
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
    · -- Frame well-formedness assumed (to be proven from trimFrame')
      exact h_frame_wf
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
    (h_frame_wf : ∀ db_any, WellFormedFrame db_any fr)
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

end ParserOps
end Metamath

