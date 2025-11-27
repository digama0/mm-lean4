-- Test simpler approach: use match on the list directly
theorem mapM_nil {α β : Type _} [Monad m] (f : α → m β) :
  List.mapM f [] = pure [] := by
  rfl

theorem mapM_cons {α β : Type _} [Monad m] (f : α → m β) (x : α) (xs : List α) :
  List.mapM f (x :: xs) = do
    let y ← f x
    let ys ← List.mapM f xs
    pure (y :: ys) := by
  sorry

#check mapM_nil
#check mapM_cons
