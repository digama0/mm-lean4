import Lean

example (l : List Nat) (i : Nat) (hi : i < l.length) :
    l[i]! = l.get ⟨i, hi⟩ := by
  -- l.get works with Fin, we have i : Nat and hi : proof
  -- l[i]! is the bang notation which is getElem! on lists
  -- We need to connect these
  
  -- The key is that l[↑fin] = l.get fin where fin : Fin l.length
  -- And l[i]! = if h : i < l.length then l.get ⟨i, h⟩ else default
  
  -- Let's use the fact that we have hi : i < l.length
  show l[i]! = l.get ⟨i, hi⟩
  
  -- The bang notation should reduce using hi
  simp only [hi]
  -- This should reduce l[i]! to l.get ⟨i, hi⟩
  sorry
