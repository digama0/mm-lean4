import Lean

-- Find the bridge lemma
#check List.getElem!_eq_get

example (l : List Nat) (i : Nat) (hi : i < l.length) :
    l[i]! = l.get ⟨i, hi⟩ := by
  exact List.getElem!_eq_get _ _ hi
