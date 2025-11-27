import Lean

-- Check available lemmas
example : True := by
  apply Iff.intro
  · intro _; trivial
  · intro _; trivial
  
#check @getElem
