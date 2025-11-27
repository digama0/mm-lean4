import Lean

-- Check what l[i]! actually is
example (l : List Nat) (i : Nat) :
    l[i]! = default := by
  rfl  -- Does it reduce?
