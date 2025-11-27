import Metamath.Verify

theorem foldl_push_size_pos {α : Type u} (arr : Array α) (init : Array α) (start : Nat)
    (h_init : 0 < init.size) :
    0 < (arr.foldl (init := init) (start := start) Array.push).size := by
  sorry
