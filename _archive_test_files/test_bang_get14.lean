import Lean

theorem list_bang_eq_get (l : List Nat) (i : Nat) (hi : i < l.length) :
    l[i]! = l.get ⟨i, hi⟩ := by
  -- Try using simp to unfold the definition
  simp only [getElem!, Nat.getElem!, ite_self]
  sorry
