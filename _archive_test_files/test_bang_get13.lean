import Lean

-- Strategy: l[i]! is defined via HGetElem.hGetElem
-- For lists with Bang, it uses getElem!
-- which is defined as: if h : i < l.length then l.get ⟨i, h⟩ else default

theorem list_bang_eq_get (l : List Nat) (i : Nat) (hi : i < l.length) :
    l[i]! = l.get ⟨i, hi⟩ := by
  -- The definition of getElem! is:
  -- getElem! i := if h : i < length then get ⟨i, h⟩ else default
  -- When we have hi : i < l.length, the if reduces and we get l.get ⟨i, _⟩
  -- The underscore is unified with hi
  unfold HGetElem.hGetElem instGetElem List.instGetElem
  sorry
