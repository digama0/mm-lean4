# Proof Toolkit: Available Theorems

**Quick reference for proven theorems to reuse in sorry elimination**

## 🔧 From Verify.lean

### Insert Properties
- `DB.insert_no_dup_objects` (line 298)
  - When: `db.error = false`, `db.find? l = none`, `(db.insert pos l obj).error = false`
  - Proves: `(db.insert pos l obj).objects = db.objects.insert l (obj l)`

- `DB.insert_find?_self` (line 329)
  - When: `db.error = false`, `db.find? l = none`, `(db.insert pos l obj).error = false`
  - Proves: `(db.insert pos l obj).find? l = some (obj l)`

## 🔧 From ParserCorrectness.lean (Proven, no sorry)

### Error Preservation (The Workhorse Lemmas)
- `withFrame_preserves_error_state` (line 102) - Frame ops preserve error=true
- `mkError_creates_error` (line 109) - mkError always sets error=true
- `insert_preserves_error` (line 115) - insert preserves error=true
- `pushScope_preserves_error` (line 128) - pushScope preserves error=true
- `popScope_preserves_error` (line 138) - popScope preserves error=true
- `withDJ_preserves_error` (line 151) - withDJ preserves error=true
- `withHyps_preserves_error` (line 158) - withHyps preserves error=true

### Basic DB Properties
- `DB.find?_def` (line 78) - Definition of find?
- `DB.error_def` (line 82) - Definition of error
- `DB.withFrame_preserves_objects` (line 86) - Frame ops don't touch objects
- `DB.withFrame_preserves_error` (line 90) - Frame ops don't touch error?
- `insert_frame_unchanged` (line 165) - insert doesn't modify frame

### Insert Success Properties
- `mkError_has_error` (line 172) - mkError result has error? ≠ none
- `insert_success_no_mkError` (line 179) - If insert succeeds, no mkError was called
- `insert_new_object_updates` (line 192) - Insert with no dup updates objects
- `insert_success_objects_updated` (line 205) - More general objects update
- `insert_success_find?_self` (line 306) - Find self after insert
- `insert_success_find?_ne` (line 319) - Find others unchanged (with conditions)

### Frame Well-formedness
- `insert_preserves_frame_wf` (line 334) - Insert preserves WellFormedFrame

### Error Short-circuit
- `error_short_circuit` (line 559) - If error=true, insert returns unchanged db

## 🔧 From DBLemmas.lean (Newly Proven)

- `insert_with_error` - Error short-circuit in insert
- `insert_success_updates_objects` - Objects map updated on success
- `insert_success_find?` - Find inserted object after success
- `insert_preserves_no_error` - Error=false preserved when conditions met

## 🎯 Common Proof Patterns

### Pattern 1: Delegation
```lean
theorem my_theorem := ExistingTheorem args
```

### Pattern 2: Error Preservation Chain
```lean
theorem op_preserves_error :=
  intro h
  unfold operation
  split <;> simp [mkError_creates_error, h]
```

### Pattern 3: Case Split + Exfalso
```lean
theorem with_contradiction :=
  intro h_condition
  unfold definition
  split
  · exfalso; apply h_condition; simp_all
  · simp [h_condition]
```

### Pattern 4: Vacuous Truth
```lean
theorem empty_collection_property :=
  intro i hi
  simp at hi  -- derives False for i < 0
```

## ⚠️ Known Challenges

### Challenge 1: Preservation Through Monadic Code
**Issue**: `insertHyp_preserves_error` (lines 424-432 in ParserCorrectness.lean)
- Conceptually simple: should chain `insert_preserves_error` and `withHyps_preserves_error`
- Problem: Lean's elaboration of `Id.run do...` creates complex monadic structure
- Preservation theorems have type `DB → DB`, but elaborated goal has nested `let` and `forIn` constructs
- Attempted solutions that failed:
  - `apply` chain: Type mismatch between elaborated and theorem forms
  - `simp [preservation_theorem]`: Implications don't work as simp rules
  - `unfold` + `simp`: Elaborated form still doesn't match hypothesis type
  - Explicit `show` statements: Can't write `let mut` outside do-notation

**Potential solutions**:
1. Write custom lemma about preservation through `Id.run` and `forIn` combinators
2. Prove preservation at the monadic level before elaboration
3. Use `conv` mode to selectively rewrite parts of the goal
4. Accept as documented limitation and move to other sorries
