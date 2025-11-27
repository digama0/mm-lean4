import Lean

#check List.getElem!
#print List.getElem!

example (l : List Nat) (i : Nat) (hi : i < l.length) :
    l.getElem! i = l.get ⟨i, hi⟩ := by
  unfold List.getElem!
  -- Should reduce to match and unwrap
  sorry
