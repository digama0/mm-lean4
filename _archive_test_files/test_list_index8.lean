import Lean

-- When we have a proof that i < length, is l[i]! = l.get?
example (l : List Nat) (i : Nat) (hi : i < l.length) :
    l[i]! = l.get ⟨i, hi⟩ := by
  -- l[i]! unfolds to if h : i < l.length then l.get ⟨i, h⟩ else default
  -- When we have hi : i < l.length, the if should reduce
  simp [hi]

