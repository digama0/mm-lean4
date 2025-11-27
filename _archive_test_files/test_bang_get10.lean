import Lean

-- Maybe the getElem! for lists is defined via getElem?
#check @List.getElem?

example (l : List Nat) (i : Nat) (hi : i < l.length) (x : Nat) 
    (h_eq : l.get ⟨i, hi⟩ = x) :
    l[i]! = x := by
  -- getElem! is defined as getElem? followed by Bang
  -- Let's try using the definition of getElem! 
  show l.getElem! i = x
  -- Now we have l.getElem! which should be in terms of getElem?
  unfold List.getElem!
  sorry
