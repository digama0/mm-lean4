import Lean

#check List.mapM
#print List.mapM

-- Test what mapM actually does
def testMapM : List.mapM (fun x => some (x + 1)) [1, 2, 3] = some [2, 3, 4] := by
  rfl

#check testMapM
