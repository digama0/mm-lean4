import Lean

-- Test the exact relationship
example (l : List Nat) (i : Nat) (hi : i < l.length) :
    l[i]! = l.get ⟨i, hi⟩ := by
  -- Check what lemmas are available
  #check List.get_eq_getElem
  #check List.getElem_eq_get
  sorry
