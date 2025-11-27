import Batteries.Data.Array.Lemmas
import Batteries.Data.List.Lemmas

theorem Array.foldl_eq_foldl_extract {α β} (arr : Array α) (init : β) (start : Nat) (f : β → α → β) :
    arr.foldl f init start = (arr.extract start arr.size).foldl f init := by
  sorry

theorem foldl_eq_list_foldl_drop
    {α β} (arr   : Array α)
          (init  : β)
          (start : Nat)
          (f     : β → α → β) :
    arr.foldl (init := init) (start := start) f =
      (arr.toList.drop start).foldl f init := by
  rw [Array.foldl_eq_foldl_extract]
  -- Now (arr.extract ...).foldl f init
  -- We know Array.foldl f init = (arr.extract ...).toList.foldl f init
  -- And (arr.extract ...).toList = arr.toList.drop start
  sorry
