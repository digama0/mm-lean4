import Lean

example (l : List Nat) (i : Nat) (hi : i < l.length) :
    l[i]! = l.get ⟨i, hi⟩ := by
  -- Use get_eq_getElem: l.get i = l[↑i] where i : Fin l.length
  -- So l.get ⟨i, hi⟩ = l[↑⟨i, hi⟩] = l[i] (using the coercion)
  have : l.get ⟨i, hi⟩ = l[i] := by rw [← List.get_eq_getElem]
  rw [← this]
  -- Now need l[i]! = l[i]
  simp [List.getElem!]
