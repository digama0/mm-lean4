import Lean

#print List.mapM.loop

-- Try proving with loop
theorem List.mapM_some' {α β : Type _} (f : α → Option β) (xs : List α) :
  (∀ x ∈ xs, ∃ y, f x = some y) →
  ∃ ys, List.mapM f xs = some ys := by
  intro h
  unfold List.mapM
  sorry
