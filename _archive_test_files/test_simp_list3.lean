import Lean

example (l : List Nat) (i : Nat) (hi : i < l.length) (x : Nat) (h_eq : l.get ⟨i, hi⟩ = x) :
    l[i]! = x := by
  -- l[i]! is notation for getElem! l i
  -- which is defined to use if h : i < length then ... else default
  show (if h : i < l.length then l.get ⟨i, h⟩ else default) = x
  simp [hi, h_eq]
