-- Test file to understand List.allM behavior

-- Check what allM returns
#check @List.allM
#print List.allM

-- Look at definition
#check List.allM._unfold_1

-- Simple example
def testList : List Nat := [1, 2, 3]

def checkEven (n : Nat) : Option Bool :=
  some (n % 2 == 0)

#eval testList.allM checkEven
-- Should return some false (since 1 is odd)

def checkPositive (n : Nat) : Option Bool :=
  some (n > 0)

#eval testList.allM checkPositive
-- Should return some true

-- What we need: if allM returns some true, then all elements satisfy the check
-- Let's look for theorems about this

-- Try to see what's available
example : [1, 2].allM (fun n => some (n > 0)) = some true := by
  rfl

-- The key property we need
example (f : α → Option Bool) (xs : List α) (x : α) :
    xs.allM f = some true → x ∈ xs → f x = some true := by
  sorry

-- Let me try to prove it by induction
lemma allM_mem_of_eq_true {α : Type _} (f : α → Option Bool) (xs : List α) :
    xs.allM f = some true → ∀ x ∈ xs, f x = some true := by
  intro h_all x h_mem
  induction xs with
  | nil =>
      contradiction
  | cons hd tl ih =>
      -- allM on cons
      unfold List.allM at h_all
      sorry
