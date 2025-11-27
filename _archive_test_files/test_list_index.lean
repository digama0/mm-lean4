import Lean

-- Test list indexing: is [i]! = .get ⟨i, h⟩?
example (l : List Nat) (i : Nat) (hi : i < l.length) :
    l[i]! = l.get ⟨i, hi⟩ := by
  rfl

-- Even simpler
example : [1, 2, 3][1]! = [1, 2, 3].get ⟨1, by norm_num⟩ := by
  rfl
