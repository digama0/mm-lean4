import Lean

example (l : List Nat) (i : Nat) (hi : i < l.length) (x : Nat) 
    (h_eq : l.get ⟨i, hi⟩ = x) :
    l[i]! = x := by
  -- Unfold the getElem! definition
  unfold GetElem.getElem instGetElem HGetElem.hGetElem
  sorry
