# Structure-Preserving Operations Template - COMPLETE

**Date**: 2025-11-20  
**Status**: ✅ **TEMPLATE CREATED - Pattern Established**

## What We Built

Created the **structure-preserving operations framework** in ParserCorrectness.lean, which is the KEY composition theorem for parser soundness.

### The Framework (Lines 703-768)

```lean
/-- Database operations that preserve structural invariants -/
inductive StructurePreservingOp : (DB → DB) → Prop where
  | insert (pos : Pos) (label : String) (obj : String → Object)
  | pushScope
  | popScope (pos : Pos)
  | withFrame (f : Frame → Frame)

/-- Main theorem: Structure-preserving operations maintain WellFormedDB -/
theorem structure_preserving_maintains_wf
    {op : DB → DB}
    (h_struct : StructurePreservingOp op)
    (db : DB)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (op db).error? = none) :
    WellFormedDB (op db)
```

### The Template: Insert Float Case (Lines 748-767)

```lean
theorem insert_float_preserves_wf
    (db : DB) (pos : Pos) (label_key : String) (f : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos label_key (.hyp false f)).error? = none) :
    WellFormedDB (db.insert pos label_key (.hyp false f)) := by
  constructor
  · -- Part 1: WellFormedFrame unchanged (insert doesn't modify frame)
    sorry
  · -- Part 2: All objects well-formed
    -- Key: Case split on new vs. existing object
    -- For new object: use ParserInvariants.float_came_from_validated_insertion
    sorry
```

## The Proof Pattern

### Step 1: WellFormedFrame Preserved

```lean
-- insert doesn't modify frame
have h_frame : (db.insert pos label (.hyp false f)).frame = db.frame
rw [h_frame]
exact h_wf.1  -- Original frame was well-formed
```

### Step 2: Objects Case Split

```lean
intro label' obj h_find'
by_cases h_eq : label' = label
· -- NEW OBJECT: label' = label
  -- Use ParserInvariants.float_came_from_validated_insertion
  -- This gives us: f.size = 2 ∧ (∃ c, f[0]! = .const c) ∧ (∃ v, f[1]! = .var v)
  -- Which is exactly WellFormedFloat f!
  
· -- EXISTING OBJECT: label' ≠ label  
  -- Use HashMap.find?_insert_ne to show: find? label' unchanged
  -- Apply h_wf.2 to existing object
```

## The Key Connection

**This is where ParserInvariants meets ParserCorrectness!**

```
ParserInvariants.float_came_from_validated_insertion
    ↓ (proven via WellFormedDB extraction)
Gives us: f.size = 2 ∧ (∃ c, f[0]! = .const c) ∧ (∃ v, f[1]! = .var v)
    ↓
Which is EXACTLY: WellFormedFloat f
    ↓
Used in: insert_float_preserves_wf
    ↓
Which proves: insert preserves WellFormedDB
    ↓
Used in: structure_preserving_maintains_wf
    ↓
Which will be used in: parser_success_wellformed
```

## What Remains (Todos)

### For insert_float_preserves_wf:

1. **Frame unchanged** - Needs `DB.insert_frame_unchanged` lemma (should be in ParserProofs)
2. **find? for new object** - Needs `DB.find?_insert_self_hyp` (exists in ParserProofs:182)
3. **find? for existing** - Needs `HashMap.find?_insert_ne` (axiom in ParserCorrectness:46)

### For structure_preserving_maintains_wf:

Once `insert_float_preserves_wf` is complete, fill in the other cases:
- `.hyp true` (essential): Similar pattern, use essential WF invariants
- `.assert`: Use assert WF invariants
- `pushScope/popScope/withFrame`: Trivial (don't modify objects)

## Build Status

```
✅ ParserCorrectness.lean compiles
✅ Framework defined (StructurePreservingOp)
✅ Main theorem stated (structure_preserving_maintains_wf)
✅ Template provided (insert_float_preserves_wf)
✅ Pattern documented (this file!)
```

## The Big Picture

This framework is the LINCHPIN for parser soundness:

```
empty_db_wellformed (base case)
    +
structure_preserving_maintains_wf (inductive step)
    +
db_construction_induction (composition over list of ops)
    +
parser_execution_trace (connect feedAll to list of ops)
    =
parser_success_wellformed: db.error? = none → WellFormedDB db
```

Once `parser_success_wellformed` is proven, the entire proof chain becomes:

```
HashMap Persistence
    ← float validation lemmas (DONE ✓)
    ← parser_validates_all_float_structures (DONE ✓)
    ← float_came_from_validated_insertion (1 sorry: WellFormedDB)
    ← parser_success_wellformed (THIS IS THE FINAL BOSS)
        ← structure_preserving_maintains_wf (TEMPLATE DONE ✓)
```

## Next Steps

**Concrete path to completion:**

1. **Fill in the 3 TODOs** in `insert_float_preserves_wf` using existing lemmas
2. **Test the pattern** - verify it actually composes correctly
3. **Apply to other cases** - `.hyp true`, `.assert`, scope ops
4. **Prove db_construction_induction** - mechanical list recursion
5. **Connect to feedAll** - trace parser execution
6. **DONE!** - Full parser soundness theorem

## Grok4's Verdict

> "This is the absolute correct next target... it is **95% definitional already**."

We're now at:
- ✅ Framework: DONE
- ✅ Pattern: DOCUMENTED
- ⚠️ Details: 3 lemmas + case analysis

**Estimated LOC to completion**: ~50 lines of actual proof code

The architecture is SOLID. The pattern is CLEAR. Ready to finish! 🎯
