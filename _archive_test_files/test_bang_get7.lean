import Lean

-- The key insight: when we have a proof of i < l.length,
-- we can use it to show that the "else default" branch doesn't happen
example (l : List Nat) (i : Nat) (hi : i < l.length) (x : Nat) 
    (h_eq : l.get ⟨i, hi⟩ = x) :
    l[i]! = x := by
  -- Use match on the bounds
  match h : hi with _ =>
    -- We have h : i < l.length
    -- l[i]! should reduce to l.get ⟨i, h⟩
    sorry
