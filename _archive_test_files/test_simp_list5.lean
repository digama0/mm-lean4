import Lean

example (l : List Nat) (i : Nat) (hi : i < l.length) (x : Nat) (h_eq : l.get ⟨i, hi⟩ = x) :
    l[i]! = x := by
  -- Just convert using the get lemma
  calc l[i]! 
      = l.getElem! i := rfl
    _ = l.get ⟨i, by omega⟩ := by omega
    _ = l.get ⟨i, hi⟩ := rfl
    _ = x := h_eq
