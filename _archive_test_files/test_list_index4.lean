import Lean

example (l : List Nat) (i : Nat) (hi : i < l.length) :
    l[i]! = l.get ⟨i, hi⟩ := by
  -- l.get ⟨i, hi⟩ uses Fin, but l[i]! uses Nat
  -- Let's try unfolding getElem!
  unfold HGetElem.hGetElem Membership.mem Array.instHGetElem List.instHGetElem
  sorry
