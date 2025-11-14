import Lean

example (l : List Nat) (i : Nat) :
    l[i]! = (if h : i < l.length then l.get ⟨i, h⟩ else default) := by
  rfl
