import Lean

-- Check what other lemmas relate to getElem! and get
#check @getElem!_eq_iff_exists
#check @List.getElem!_neg
#check @List.getElem!_cons
#check @List.getElem_cons
#check @List.get_cons
#check @List.get_nil

-- Check for list-specific lemmas
#check @List.getElem!_zero
#check @List.getElem!_succ
