import Lean
import Metamath.Spec
import Metamath.Verify

-- Simulate the convertHyp floating case
example (db : Verify.DB) (label : String) (f : Verify.Formula) (lbl : String)
    (e : Spec.Expr) (s : Spec.Sym)
    (h_find : db.find? label = some (.hyp false f lbl))
    (h_toExpr : toExprOpt f = some e)
    (h_singleton : e.syms = [s]) :
    convertHyp db label = some (Spec.Hyp.floating e.typecode ⟨s⟩) := by
  -- Unfold convertHyp and apply the conditions
  unfold convertHyp
  simp [h_find, h_toExpr]
  -- After simp, goal should be: match e with | ⟨c, [v]⟩ => some (Spec.Hyp.floating c ⟨v⟩) | _ => none = some (Spec.Hyp.floating e.typecode ⟨s⟩)
  -- Use h_singleton to show the pattern matches
  have h_e_eq : e = {typecode := e.typecode, syms := [s]} := by
    cases e
    simp [h_singleton]
  rw [h_e_eq]
  simp
