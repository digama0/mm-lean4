import Lean

example (l : List Nat) (i : Nat) (hi : i < l.length) (x : Nat) 
    (h_eq : l.get ⟨i, hi⟩ = x) :
    l[i]! = x := by
  -- After we have getElem!_toList connecting array to list bang,
  -- we now need list bang to get
  
  -- Let's try using Eq.symm and h_eq
  have : l.get ⟨i, hi⟩ = l[i]! := by
    -- Try rfl with definitional unfolding
    trivial
  rw [← this]
  exact h_eq
