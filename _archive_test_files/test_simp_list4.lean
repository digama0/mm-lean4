import Lean

example (l : List Nat) (i : Nat) (hi : i < l.length) (x : Nat) (h_eq : l.get ⟨i, hi⟩ = x) :
    l[i]! = x := by
  unfold HGetElem.hGetElem instHGetElem
  sorry
