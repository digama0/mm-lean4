import Lean

#check @List.get_of_getElem?
#check @List.getElem?_eq_get

example (l : List Nat) (i : Nat) (hi : i < l.length) (x : Nat) 
    (h_eq : l.get ⟨i, hi⟩ = x) :
    l[i]! = x := by
  -- Maybe omega can solve this?
  omega
