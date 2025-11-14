import Lean

-- What we need: if mapM succeeds, membership in output means membership in input
example {α β : Type u_1} (f : α → Option β) (xs : List α) (ys : List β) (y : β)
    (h : xs.mapM f = some ys) (h_mem : y ∈ ys) :
    ∃ x ∈ xs, f x = some y := by
  sorry
