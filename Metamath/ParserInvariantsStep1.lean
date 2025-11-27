import Metamath.Verify
import Metamath.WellFormedness
import Metamath.ParserCorrectness

namespace Metamath.ParserInvariantsStep1

open Verify
open Metamath.WF
open Metamath.ParserCorrectness

/-- Helper: db.insert for .hyp implies freshness -/
theorem insert_hyp_implies_fresh
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
    (h_ok : (db.insert pos l (.hyp ess f)).error? = none) :
    db.find? l = none := by
  -- Proof requires detailed case analysis of DB.insert which is failing to simplify cleanly.
  -- Logic: db.insert checks for duplicates. For .hyp, it errors if found.
  -- Since h_ok says no error, it wasn't found.
  sorry

/-- Parser check: Verify.lean:feedTokens (lines 561-567)
    The parser enforces that all $f hypotheses have the form #[.const c, .var v]
    BEFORE calling insertHyp. -/
theorem feedTokens_validates_float
    (s : ParserState) (arr : Array Sym) (pos : Pos) (l : String)
    (h_success : (s.feedTokens arr (TokensParser.mk .float pos l)).db.error? = none) :
    WellFormedFloat arr := by
  -- Proof requires splitting the `if` conditions inside feedTokens.
  -- Logic: checks arr.size > 0, arr[0].isVar, arr.size == 2, arr[1].isVar.
  -- If any fail, mkError. h_success excludes this.
  sorry

/-- insertHyp ensures label freshness (if it inserts). -/
theorem insertHyp_ensures_fresh_db
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
    (h_success : (db.insertHyp pos l ess f).error? = none) :
    db.find? l = none := by
  -- Proof relies on insert_hyp_implies_fresh and showing the float check loop preserves db.
  sorry

/-- General validation: feedTokens ensures any inserted formula has size > 0 and const head. -/
theorem feedTokens_validates_formula
    (s : ParserState) (arr : Array Sym) (p : TokensParser)
    (h_success : (s.feedTokens arr p).db.error? = none) :
    WellFormedFormula arr := by
  -- Proof requires splitting the first check in feedTokens.
  sorry

/-- Composite theorem: feedTokens validates both essential and float hypotheses. -/
theorem feedTokens_validates_hyp
    (s : ParserState) (arr : Array Sym) (pos : Pos) (l : String) (k : TokensKind)
    (h_k : k = .float ∨ k = .ess)
    (h_success : (s.feedTokens arr (TokensParser.mk k pos l)).db.error? = none) :
    (k = .ess → WellFormedFormula arr) ∧ (k = .float → WellFormedFloat arr) := by
  constructor
  · intro _ -- k = .ess
    exact feedTokens_validates_formula s arr (TokensParser.mk k pos l) h_success
  · intro h_float
    rw [h_float] at h_success
    exact feedTokens_validates_float s arr pos l h_success

end Metamath.ParserInvariantsStep1