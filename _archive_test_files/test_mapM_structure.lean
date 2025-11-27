import Lean

-- Test base case
example : ([] : List Nat).mapM (fun x => some (x + 1)) = some [] := by
  rfl

-- Test cons case  
example : ([1, 2] : List Nat).mapM (fun x => some (x + 1)) = some [2, 3] := by
  rfl

-- Test failure case
example : ([1, 2] : List Nat).mapM (fun x => if x = 2 then none else some (x + 1)) = none := by
  rfl

-- Test the membership property we're trying to prove
example (f : Nat → Option Nat) (xs : List Nat) (ys : List Nat) (y : Nat)
    (h : xs.mapM f = some ys) (h_mem : y ∈ ys) :
    ∃ x ∈ xs, f x = some y := by
  -- Base strategy: induction on xs
  sorry
