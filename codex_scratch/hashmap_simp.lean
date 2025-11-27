import Std.Data.HashMap.Basic
open Std

example : ((Std.HashMap.empty.insert "x" 3) : Std.HashMap String Nat)["x"]? = some 3 := by
  classical
  simp
