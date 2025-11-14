import Lean

-- Test a concrete case first
example : [1, 2, 3][1]! = 2 := by
  native_decide

-- Now the general case
example (l : List Nat) (i : Nat) (hi : i < l.length) (x : Nat) 
    (h_eq : l.get ⟨i, hi⟩ = x) :
    l[i]! = x := by
  -- Try using unsafe coercion of equality
  exact absurd h_eq sorry
