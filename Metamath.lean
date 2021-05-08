import Metamath.Verify

open Metamath.Verify in
def main (n : List String) : IO UInt32 := do
  let db ← check $ n.getD 0 "set.mm"
  match db.error? with
  | none =>
    IO.println s!"verified, {db.objects.size} objects"
    pure 0
  | some ⟨Error.error pos err, _⟩ =>
    IO.println s!"at {pos}: {err}"
    pure 1
  | some _ => unreachable!
