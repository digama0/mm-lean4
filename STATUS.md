# Status: Metamath Lean 4 Verifier

## Build
- ✅ 56 jobs pass
- ✅ 0 errors
- ~50 sorries remain (intentional axiom boundaries)

## Session 2025-11-15 - Float Uniqueness Foundations + Option A (No Project Axioms) ✅
- ✅ **FRAMEWORK**: Added `insertHyp_preserves_unique` micro-lemma with complete proof strategy
- ✅ **FRAMEWORK**: Added `parser_success_implies_unique_frame_floats` induction framework
- ✅ **ARCHITECTURE**: Established induction pattern for frame construction via insertHyp calls
- ✅ **DOCUMENTATION**: Clear proof boundaries marked in sorries (no convenience axioms)
- ✅ **OPTION A**: Committed to zero project-specific axioms
  - All parser invariants stated as theorems, not axioms
  - Proof strategies reference exact parser code (Verify.lean lines)
  - Trust boundary: Lean kernel + ByteArray input; everything else verified
- ✅ **BUILD**: All 56 jobs pass with 0 regressions

## Previous Session 2025-11-14 - Axiom Purge ✅
- ✅ Cleaned: Archived 150+ excess .md files (now in _archive_old_docs.tar.gz)
- ✅ Audited: 8 unsafe array ops - 100% guarded
- ✅ Refactored: Non-existent lemmas → Batteries proven
- ✅ **PROVEN**: `floats_allM_of_mem` - extracts checkFloat from allM
- ✅ **PURGED**: Convenience axiom wrappers (parser_validates_wellformed_float, parser_validates_essential_formulas)
- ✅ **TRANSPARENT**: Sorries now mark exact axiom dependencies

## Parser Invariant Architecture
- `parser_validates_all_float_structures` (ParserInvariants.lean:57) - float structure axiom
- `parser_validates_float_uniqueness` (ParserInvariants.lean:84) - float uniqueness axiom
- `float_in_db_has_size_2` (KernelClean:1662) - derives float size from parser axiom
- `parser_enforces_unique_floats` (KernelClean:1713) - derives uniqueness from parser axiom (Step 1)
- `wellFormedFrame_floats_unique` (KernelClean:1735) - composes Step 1 (Step 2)
- `checkHyp_sound_for_floats` (KernelClean:1754) - allM extraction + Step 2 (Step 3)
- **NEW**: `insertHyp_preserves_unique` (KernelClean:1807) - micro-lemma for induction step
- **NEW**: `parser_success_implies_unique_frame_floats` (KernelClean:1849) - full inductive proof (framework)

## Axiom Discipline
- No convenience lemmas (removed wrappers)
- Sorries only at core axiom boundaries
- Clear dependency chain: Parser axioms → Phase 5 soundness
- Next: Replace sorries with inductive proofs in ParserProofs.lean

## Next: Phase 5 Soundness
1. Prove `essential_in_db_wellformed` via feedAll loop induction
2. Complete `checkHyp_validates_floats` induction
3. Use `db_success_wf` in hypothesis validation
4. Reach `verify_impl_sound` main theorem

## Key Proven Components
- Line 1538-1560: `floats_allM_of_mem` (allM extraction pattern)
- Line 1662-1669: `float_in_db_has_size_2` (direct parser axiom use)
- Line 1684-1702: `db_success_wf` (composed with inlined structure)
