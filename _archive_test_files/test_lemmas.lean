import Lean

example (l : List Nat) (i : Nat) (hi : i < l.length) :
    l[i]! = l.get ⟨i, hi⟩ := by
  simp only [hi, getElem!_pos, List.get_eq_getElem]
