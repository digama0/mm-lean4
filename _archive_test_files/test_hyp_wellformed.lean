import Metamath.Verify

open Metamath.Verify

-- Minimal test for HypsWellFormed syntax issue

def TestWF1 (db : DB) (hyps : Array String) : Prop :=
  ∀ i, i < hyps.size →
    ∃ ess f lbl, db.find? hyps[i]! = some (Object.hyp ess f lbl)

def TestWF2 (db : DB) (hyps : Array String) : Prop :=
  ∀ i, i < hyps.size →
    ∃ ess f lbl, db.find? hyps[i]! = some (.hyp ess f lbl)

--def TestWF3 (db : DB) (hyps : Array String) : Prop :=
--  ∀ i, i < hyps.size →
--    ∃ ess, ∃ f, ∃ lbl, db.find? hyps[i]! = some (Verify.Object.hyp ess f lbl)
