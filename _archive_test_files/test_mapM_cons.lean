import Lean

-- Check the mapM_cons structure
#print List.mapM_cons

-- Try to understand what it produces
example (f : Nat → Option Nat) (a : Nat) (as : List Nat) :
    (a :: as).mapM f = do
      let y ← f a
      let ys ← as.mapM f  
      pure (y :: ys) := by
  rfl
