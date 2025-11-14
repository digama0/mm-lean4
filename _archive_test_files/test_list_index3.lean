import Lean

-- Try other names
#check @List.get_eq_getElem
#check @List.getElem_eq_get

example (l : List Nat) (i : Nat) (hi : i < l.length) :
    l[i]! = l.get ⟨i, hi⟩ := by
  rw [List.get_eq_getElem]
  sorry
