import Lake
open Lake DSL

package «mm-lean4» where
  -- TODO: Enable strict mode once Verify.lean is updated
  -- moreLeanArgs := #["-DwarningAsError=true", "-DautoImplicit=false"]

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.24.0"

@[default_target]
lean_lib Metamath where
  -- Active modules (all compile cleanly):
  -- Spec: Formal specification of Metamath verification
  -- ByteSliceCompat: Compatibility layer for Std.ByteSlice (Batteries 4.24.0+)
  -- Verify: Implementation of proof checker
  -- WellFormedness: Foundational well-formedness predicates (parser guarantees)
  -- ParserBasics: Trivial parser properties (warm-up proofs!)
  -- ParserCorrectness: Ground-up parser correctness architecture (Layer 0-5)
  -- ArrayListExt: Centralized array/list infrastructure lemmas (Batteries 4.24.0+)
  -- Bridge: Implementation-to-spec bridge functions
  -- KernelExtras: Helper lemmas for kernel verification
  -- AllM: Phase 2 allM extraction lemmas
  -- KernelClean: Main kernel soundness proof (Phase 1-7)
  -- ValidateDB: Database format validation tests
  -- ParserInvariants: Parser correctness theorems (eliminate axioms!)
  -- ParserProofs: Proofs of parser axioms by code inspection
  -- HashMapLemmas: Infrastructure for HashMap reasoning (eliminates axioms!)
  -- ParserLoopInduction: Infrastructure for feed loop induction
  -- LoopInvariant: Reusable loop invariant infrastructure (general-purpose)
  -- DBCaseAnalysis: Helpers for complex case analysis in DB operations
  -- CounterexampleInsertError: Proves insert with error can modify DB
  -- ParserOperations: Parser operations as StructurePreservingOps
  -- AutoTest: ATP automation test cases (requires lean-auto, not included in build)
  -- ZipperTest: Zipperposition integration test (requires lean-auto, not included in build)
  -- Tests.ParserInvariantTests: Executable verification tests
  roots := #[`Metamath.Spec, `Metamath.ByteSliceCompat, `Metamath.Verify, `Metamath.WellFormedness, `Metamath.ParserBasics, `Metamath.ParserCorrectness, `Metamath.ArrayListExt, `Metamath.Bridge, `Metamath.KernelExtras, `Metamath.AllM, `Metamath.KernelClean, `Metamath.ValidateDB, `Metamath.ParserInvariants, `Metamath.ParserProofs, `Metamath.HashMapLemmas, `Metamath.ParserLoopInduction, `Metamath.LoopInvariant, `Metamath.DBCaseAnalysis, `Metamath.CounterexampleInsertError, `Metamath.ParserInvariantsStep1, `Metamath.ParserOperations]

@[default_target]
lean_lib MetamathExperimental where
  roots := #[`Metamath.Translate]

@[default_target]
lean_exe «mm-lean4» where
  root := `Metamath

lean_exe validateDB where
  root := `Metamath.ValidateDB
  supportInterpreter := true
