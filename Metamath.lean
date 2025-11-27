import Metamath.Spec
import Metamath.Verify
import Metamath.KernelExtras
import Metamath.KernelClean  -- Phase 1: Minimal axiomatic skeleton (bottom-up strategy)
import Metamath.ParserInvariantsStep1
-- import Metamath.ParserSoundnessDemo  -- Parser soundness demonstration (WIP)
-- import Metamath.KernelSkeleton  -- Archived (parse errors)
-- import Metamath.Kernel  -- Archived (185 errors)

open Metamath.Verify in
def main (args : List String) : IO UInt32 := do
  let (permissive, fname) := match args with
  | "--permissive" :: fname :: _ => (true, fname)
  | fname :: "--permissive" :: _ => (true, fname)
  | fname :: _ => (false, fname)
  | [] => (false, "set.mm")

  let db ← check fname permissive
  match db.error? with
  | none =>
    IO.println s!"verified, {db.objects.size} objects"
    pure 0
  | some ⟨Error.error pos err, _⟩ =>
    IO.println s!"at {pos}: {err}"
    pure 1
  | some _ => unreachable!
