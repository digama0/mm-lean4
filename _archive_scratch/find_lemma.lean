import Lean

-- Try to find the relevant lemma
example (l : List Nat) (i : Nat) (hi : i < l.length) :
    l[i]! = l.get ⟨i, hi⟩ := by
  -- Try various simp sets
  simp? [hi]
