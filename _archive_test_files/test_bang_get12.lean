import Lean

-- Try proving that l[i]! unfolds correctly
theorem list_bang_eq_get (l : List Nat) (i : Nat) (hi : i < l.length) :
    l[i]! = l.get ⟨i, hi⟩ := by
  -- Both sides compute to the same thing
  sorry

example (l : List Nat) (i : Nat) (hi : i < l.length) (x : Nat) 
    (h_eq : l.get ⟨i, hi⟩ = x) :
    l[i]! = x := by
  rw [list_bang_eq_get l i hi, h_eq]
