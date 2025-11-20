import Metamath.KernelClean
open Metamath Verify
open Std

set_option pp.notation false

noncomputable section

abbrev σ : Std.HashMap String Formula :=
  (Std.HashMap.empty.insert "x" #[Sym.const "C", Sym.var "a", Sym.var "b"])

abbrev f : Formula := #[Sym.var "x"]

abbrev g : Formula := #[Sym.var "a", Sym.var "b"]

lemma test : f.subst σ = Except.ok g := by
  classical
  -- reduce substitution to list fold
  simpa [Formula.subst, f, g, σ, Array.foldlM_toList, List.foldlM, Bind.bind, Except.bind,
    Formula.substStep]
