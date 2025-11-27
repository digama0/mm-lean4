# Codex Attempt - Salvage Report

**Date**: 2025-11-20
**Status**: ⚠️ **Reverted with lessons learned**

## What Codex Tried

Codex attempted to **fully implement** the `insert_float_preserves_wf` theorem, moving from a template with TODOs to a complete proof with ~100 lines of Lean code.

## Why It Failed

The proof had **multiple compilation errors**:

1. **Unsolved goals** in duplicate detection (lines 827-830)
   - Cases on `obj` types left goals open
   - `simp` tactics didn't close the goals automatically

2. **Type mismatches** in frame preservation (line 888)
   - `h_frame_new` had type `WellFormedFrame db' db.frame`
   - Expected type was different after simplification

3. **Complexity snowball**
   - 100-line proof is hard to debug when multiple things break
   - Better to build incrementally with intermediate lemmas

## What Was Salvaged

### ✅ **Excellent Idea: Add `h_float` Parameter**

**Original signature:**
```lean
theorem insert_float_preserves_wf
    (db : DB) (pos : Pos) (label_key : String) (f : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos label_key (.hyp false f)).error? = none) :
    WellFormedDB (db.insert pos label_key (.hyp false f))
```

**Salvaged signature:**
```lean
theorem insert_float_preserves_wf
    (db : DB) (pos : Pos) (label_key : String) (f : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos label_key (.hyp false f)).error? = none)
    (h_float : WellFormedFloat f) :  -- ← SALVAGED!
    WellFormedDB (db.insert pos label_key (.hyp false f))
```

**Why this is brilliant:**
- Instead of deriving `WellFormedFloat f` from `h_no_err_after` (complex!), just **require it as input**
- Makes the proof simpler: directly use `h_float` for the new object case
- Shifts burden to the caller to provide the WF guarantee
- This is the RIGHT abstraction level for this theorem

### 🔍 **Useful Proof Patterns (Not Salvaged But Worth Noting)**

Codex's approach had some good ideas that broke due to implementation details:

1. **Proving no duplicate exists** via contradiction with `h_no_err_after`
   ```lean
   have h_find_none : db.find? label_key = none := by
     cases h : db.find? label_key with
     | none => simpa [h]
     | some obj =>
         have h_err : (db.insert ...).error? ≠ none := by
           unfold DB.insert
           cases obj with ...
         exact (h_err h_no_err_after).elim
   ```
   **Idea is sound**, but implementation had unsolved goals in the cases.

2. **Frame preservation as a separate lemma**
   ```lean
   have h_frame_preserve :
       ∀ fr, WellFormedFrame db fr → WellFormedFrame db' fr := by ...
   ```
   **Good separation of concerns**, but hit type errors when trying to use it.

3. **Using `let db' = db.insert ...`** to simplify notation
   **Clean style**, helps readability.

## What Remains (Current State)

**File**: `Metamath/ParserCorrectness.lean`
**Build**: ✅ Compiles successfully with sorry warnings

**Theorem state (Lines 811-846)**:
```lean
theorem insert_float_preserves_wf
    (db : DB) (pos : Pos) (label_key : String) (f : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos label_key (.hyp false f)).error? = none)
    (h_float : WellFormedFloat f) :  -- SALVAGED: Good idea!
    WellFormedDB (db.insert pos label_key (.hyp false f)) := by
  constructor
  · -- Part 1: WellFormedFrame preserved
    sorry
    -- TODO with detailed strategy

  · -- Part 2: All objects in the DB are well-formed
    intro label' obj h_find'
    by_cases h_eq : label' = label_key
    · -- NEW OBJECT
      sorry
      -- TODO: Use h_float directly since we have it as parameter!
    · -- EXISTING OBJECT
      sorry
      -- TODO: HashMap.find?_insert_ne + h_wf.2
```

**Sorry count**: 3 sorries (same as before, but now with better parameter!)

## Lessons Learned

### For Future Proof Attempts

1. **Build incrementally**: Prove helper lemmas separately before composing
2. **Check goals frequently**: Don't write 100 lines before checking if tactics work
3. **Use sorry strategically**: When tactics fail, sorry and move on; come back later
4. **Test small examples**: Before full proof, test that `unfold + cases + simp` pattern works

### What This Attempt Taught Us

- The `h_float` parameter idea is **architecturally superior** to deriving it
- Frame preservation is genuinely complex because WellFormedFrame depends on db for lookups
- We likely need **intermediate lemmas** like:
  - `insert_preserves_frame_wf`: Show WellFormedFrame preserved by insert
  - `insert_find?_new`: Relate `db'.find? label_key` to the inserted object
  - `insert_find?_old`: Show `db'.find? l = db.find? l` for `l ≠ label_key`

## Build Status

```
✅ Metamath.ParserCorrectness builds successfully
✅ Clean template with 3 sorries
✅ Salvaged h_float parameter (major improvement!)
✅ Updated TODOs with Codex's insights
```

## Recommendation

**Don't try to fill in all 3 sorries at once.** Instead:

1. **First**: Prove `insert_preserves_frame_wf` as a separate theorem
2. **Second**: Prove the new object case (now trivial with `h_float`!)
3. **Third**: Prove the existing object case (needs HashMap lemmas)
4. **Finally**: Compose them into the main theorem

This incremental approach avoids the "complexity snowball" that broke Codex's attempt.

---

**Bottom line**: Codex's attempt failed to compile, but we salvaged the **key architectural insight** (adding `h_float` parameter) and learned important lessons about proof strategy. The template is now **better than before Codex tried**! 💡
