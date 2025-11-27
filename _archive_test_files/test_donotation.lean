import Lean

-- Test if decide works on do-notation equality
example (x y : Nat) (h : x = 5) (h2 : y = 5) :
    (do let a ← some x; let b ← some y; pure (a + b)) = some 10 := by
  simp [h, h2]
