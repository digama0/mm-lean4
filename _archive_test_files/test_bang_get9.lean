import Lean

-- Check if we can use decide-like tactics
example (l : List Nat) (i : Nat) (hi : i < l.length) (x : Nat) 
    (h_eq : l.get ⟨i, hi⟩ = x) :
    l[i]! = x := by
  -- The real insight: both l[i]! and l.get ⟨i, hi⟩ ultimately compute the same value
  -- So we just need to show the computation paths are equivalent
  
  -- Try using calc to bridge through the common value
  calc l[i]! 
      = (if h : i < l.length then l.get ⟨i, h⟩ else default) := sorry
    _ = l.get ⟨i, hi⟩ := by simp [hi]
    _ = x := h_eq
