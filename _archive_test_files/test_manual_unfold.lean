import Lean

-- Test manual unfolding of do-notation
example : (do let x ← some 5; pure (x + 1)) = some 6 := by
  simp

-- Test with pattern matching
example : (let e := (5, [6]); 
           match e with | ⟨c, [v]⟩ => pure (c + v) | _ => none) = some 11 := by
  simp
