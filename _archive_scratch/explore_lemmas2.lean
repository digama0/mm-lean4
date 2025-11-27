import Lean

-- Check for relevant lemmas on get/getElem with specific structures
#check @List.get_eq_getElem
#check @List.getElem_cons
#check @getElem!_pos
#check @getElem!_eq_getElem
#check @List.mem_iff_get
#check @Array.getElem!_eq_getElem_get

-- Check for toList-related lemmas
#check @Array.toList_get
#check @Array.toList_getElem
#check @Array.get_toList
