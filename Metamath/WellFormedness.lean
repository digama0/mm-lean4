/-
# Metamath.WellFormedness
Foundational well-formedness predicates that capture parser guarantees.
-/
import Metamath.Verify

namespace Metamath
namespace WF
open Verify

/-- A formula is well-formed iff it is nonempty and its head is a constant. -/
def WellFormedFormula (f : Formula) : Prop :=
  0 < f.size ∧ ∃ c : String, f[0]! = Sym.const c

/-- A floating hypothesis formula has *exactly* the Metamath shape `$f C v`. -/
def WellFormedFloat (f : Formula) : Prop :=
  f.size = 2 ∧ ∃ c v : String, f[0]! = Sym.const c ∧ f[1]! = Sym.var v

/-- Extract the variable of a floating hypothesis (partial; used in uniqueness). -/
def floatVar? (f : Formula) : Option String :=
  if h : f.size = 2 then
    match f[1] with
    | .var v   => some v
    | _        => none
  else
    none

/-- Every label in a frame resolves to a hypothesis and its formula is well-formed. -/
def HypOK (db : DB) (label : String) : Prop :=
  ∃ ess f lbl,
    db.find? label = some (.hyp ess f lbl) ∧
    (ess = false → WellFormedFloat f) ∧
    (ess = true  → WellFormedFormula f)

/-- No two distinct $f-binders attach to the same variable in this frame. -/
def UniqueFloatVars (db : DB) (fr : Frame) : Prop :=
  ∀ (i j : Nat) (hi : i < fr.hyps.size) (hj : j < fr.hyps.size),
    i ≠ j →
    ∀ (fi fj : Formula) (lbli lblj : String),
      db.find? fr.hyps[i] = some (.hyp false fi lbli) →
      db.find? fr.hyps[j] = some (.hyp false fj lblj) →
      fi.size ≥ 2 → fj.size ≥ 2 →
      let vi := match fi[1]! with | .var v => v | _ => ""
      let vj := match fj[1]! with | .var v => v | _ => ""
      vi ≠ vj

/-- Frame well-formedness -/
def WellFormedFrame (db : DB) (fr : Frame) : Prop :=
  (∀ i (hi : i < fr.hyps.size), HypOK db fr.hyps[i]) ∧
  UniqueFloatVars db fr

/-- Database well-formedness -/
def WellFormedDB (db : DB) : Prop :=
  WellFormedFrame db db.frame ∧
  (∀ lbl obj, db.find? lbl = some obj →
    match obj with
    | .hyp ess f _   => (if ess then WellFormedFormula f else WellFormedFloat f)
    | .assert f fr _ => WellFormedFormula f ∧ WellFormedFrame db fr
    | .var v         => v = lbl  -- Invariant: var labels = var names
    | _              => True)

theorem var_label_eq_name_of_db
    {db : DB} {lbl v : String}
    (h_db : WellFormedDB db)
    (h_find : db.find? lbl = some (Object.var v)) :
    v = lbl := by
  have h := h_db.2 lbl (Object.var v) h_find
  exact h

theorem assert_formula_wf_of_db
    {db : DB} {lbl name : String} {f : Formula} {fr : Frame}
    (h_db : WellFormedDB db)
    (h_find : db.find? lbl = some (Object.assert f fr name)) :
    WellFormedFormula f := by
  have h := h_db.2 lbl (Object.assert f fr name) h_find
  exact h.1

theorem assert_frame_wf_of_db
    {db : DB} {lbl name : String} {f : Formula} {fr : Frame}
    (h_db : WellFormedDB db)
    (h_find : db.find? lbl = some (Object.assert f fr name)) :
    WellFormedFrame db fr := by
  have h := h_db.2 lbl (Object.assert f fr name) h_find
  exact h.2

@[simp] theorem WellFormedFormula.size_pos {f} :
  WellFormedFormula f → 0 < f.size := fun h => h.1

theorem WellFormedFormula.head_const {f} :
  WellFormedFormula f → ∃ c, f[0]! = Sym.const c := fun h => h.2

theorem WellFormedFloat.size_pos {f} :
  WellFormedFloat f → 0 < f.size := by
  intro h
  rw [h.1]
  omega

end WF
end Metamath
