import Lean

example (l : List Nat) (i : Nat) (hi : i < l.length) (x : Nat) (h_eq : l.get ⟨i, hi⟩ = x) :
    l[i]! = x := by
  -- l[i]! reduces to (if h : i < l.length then l.get ⟨i, h⟩ else default)
  -- When we have hi : i < l.length, this becomes l.get ⟨i, hi⟩
  dsimp [hi]
  exact h_eq
