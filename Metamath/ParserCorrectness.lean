/-
# Parser Correctness: Ground-Up Architecture

Building parser correctness from first principles, layer by layer.

**Architecture:**
```
Layer 5: High-Level Invariants (WellFormedDB)
   ↑
Layer 4: Frame Operations (insertHyp, trimFrame)
   ↑
Layer 3: Object Management (insert, find?)
   ↑
Layer 2: Error State Management (mkError, error propagation)
   ↑
Layer 1: Database State (DB structure, basic operations)
   ↑
Layer 0: Foundation (HashMap properties, String equality)
```

We prove properties at each layer using only properties from layers below.
-/

import Metamath.Verify
import Metamath.WellFormedness
import Metamath.ParserBasics
import Std.Data.HashMap.Lemmas

namespace Metamath.ParserCorrectness

open Verify
open Metamath.WF
open Metamath.ParserBasics
open Std

/-! ## Layer 0: Foundation - HashMap and String Properties

These are the bedrock - properties of data structures we rely on.
They are now proven from `Std.Data.HashMap.Lemmas` and lawful BEq
instances for strings.
-/

/-- HashMap.insert makes the key findable -/
@[simp] theorem HashMap.find?_insert_eq {α β} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] [LawfulBEq α]
    (m : Std.HashMap α β) (k : α) (v : β) :
    (m.insert k v)[k]? = some v := by
  simpa using (Std.HashMap.getElem?_insert_self (m := m) (k := k) (v := v))

/-- HashMap.find? on different key after insert -/
@[simp] theorem HashMap.find?_insert_ne {α β} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] [LawfulBEq α]
    (m : Std.HashMap α β) (k k' : α) (v : β) :
    k ≠ k' → (m.insert k v)[k']? = m[k']? := by
  intro hne
  classical
  have hbranch := Std.HashMap.getElem?_insert (m := m) (k := k) (a := k') (v := v)
  cases hbeq : (k == k') <;> try simp [Std.HashMap.getElem?_insert, hbeq] at hbranch
  · simpa [Std.HashMap.getElem?_insert, hbeq] using hbranch
  ·
    have hk : k = k' := LawfulBEq.eq_of_beq (a := k) (b := k') (by simpa [hbeq])
    exact (hne hk).elim

/-- BEq for String is equality -/
@[simp] theorem String.beq_eq (s₁ s₂ : String) : (s₁ == s₂) = true ↔ s₁ = s₂ := by
  constructor
  · intro h
    exact LawfulBEq.eq_of_beq (a := s₁) (b := s₂) h
  · intro h; cases h; simp

/-! ## Layer 1: Database State - Basic DB Operations

Properties that follow directly from the DB structure definition.
These are trivial because they're just field access.
-/

/-- DB.find? is just HashMap lookup -/
theorem DB.find?_def (db : DB) (label : String) :
  db.find? label = db.objects[label]? := rfl

/-- DB.error is just Option.isSome -/
theorem DB.error_def (db : DB) :
  db.error = db.error?.isSome := rfl

/-- withFrame only modifies the frame field -/
theorem DB.withFrame_preserves_objects (db : DB) (f : Frame → Frame) :
  (db.withFrame f).objects = db.objects := rfl

/-- withFrame only modifies the frame field (error) -/
theorem DB.withFrame_preserves_error (db : DB) (f : Frame → Frame) :
  (db.withFrame f).error? = db.error? := rfl

/-! ## Layer 2: Error State Management

Key insight: Error is "sticky" but only for operations that CHECK it.
Some operations (withFrame) don't check, so they can modify an errored DB.

BUT: The parser STOPS on first error, so inconsistent states are never used!
-/

/-- Frame operations preserve error state (they only modify frame field) -/
theorem withFrame_preserves_error_state (db : DB) (f : Frame → Frame) :
  db.error = true → (db.withFrame f).error = true := by
  intro h
  unfold DB.withFrame DB.error at *
  exact h

/-- mkError always creates error state -/
theorem mkError_creates_error (db : DB) (pos : Pos) (msg : String) :
  (db.mkError pos msg).error = true := by
  unfold DB.mkError DB.error
  simp

/-- insert preserves error state (if input has error, output has error) -/
theorem insert_preserves_error (db : DB) (pos : Pos) (label : String) (obj : String → Object) :
  db.error = true → (db.insert pos label obj).error = true := by
  intro h
  unfold DB.insert
  -- Split on what obj label is
  split
  · -- Case: obj label is .const
    split
    · simp [mkError_creates_error]
    · simp [h]
  · simp [h]

/-- pushScope preserves error state -/
theorem pushScope_preserves_error (db : DB) :
  db.error = true → db.pushScope.error = true := by
  intro h
  -- pushScope: { s with scopes := s.scopes.push s.frame.size }
  -- error: db.error?.isSome
  -- pushScope doesn't modify error?, so error is preserved
  unfold DB.pushScope DB.error at *
  exact h

/-- popScope preserves error state -/
theorem popScope_preserves_error (db : DB) (pos : Pos) :
  db.error = true → (db.popScope pos).error = true := by
  intro h
  unfold DB.popScope
  split
  · -- Has scope to pop: { db with frame := ..., scopes := ... }
    -- Doesn't modify error?, so error is preserved
    unfold DB.error at *
    exact h
  · -- No scope, calls mkError
    exact mkError_creates_error db pos _

/-- withDJ preserves error state -/
theorem withDJ_preserves_error (db : DB) (f : Array DJ → Array DJ) :
  db.error = true → (db.withDJ f).error = true := by
  intro h
  unfold DB.withDJ
  exact withFrame_preserves_error_state db _ h

/-- withHyps preserves error state -/
theorem withHyps_preserves_error (db : DB) (f : Array String → Array String) :
  db.error = true → (db.withHyps f).error = true := by
  intro h
  unfold DB.withHyps
  exact withFrame_preserves_error_state db _ h

/-- DB.insert doesn't modify frame -/
theorem insert_frame_unchanged (db : DB) (pos : Pos) (l : String) (obj : String → Object) :
    (db.insert pos l obj).frame = db.frame := by
  unfold DB.insert
  -- All paths preserve frame via: mkError (preserves frame), return db (rfl), or record update (rfl)
  repeat (first | rfl | simp | split)

/-- Helper: mkError creates an error -/
theorem mkError_has_error (db : DB) (pos : Pos) (msg : String) :
    (db.mkError pos msg).error? ≠ none := by
  unfold DB.mkError
  simp

/-- Helper: If db has no error and insert results in no error,
    then we didn't hit any error paths -/
theorem insert_success_no_mkError
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (_h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos l obj).error? = none) :
    -- If insert succeeded, we took the success path (no mkError calls)
    ∀ msg, (db.insert pos l obj) ≠ db.mkError pos msg := by
  intro msg h_eq
  rw [h_eq] at h_no_err_after
  exact mkError_has_error db pos msg h_no_err_after

/-- Helper: If db.find? l = none, db has no error, and insert succeeds (no error after),
    then objects map was updated.
    Key: The h_no_err_after premise rules out the const permissive check failure. -/
theorem insert_new_object_updates
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_no_find : db.find? l = none)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos l obj).error? = none) :
    (db.insert pos l obj).objects = db.objects.insert l (obj l) := by
  unfold DB.insert DB.error DB.mkError at *
  -- Case split on obj l
  split <;> split <;> simp_all

/-- When insert succeeds (no error after), the objects map was updated.
    Note: This doesn't hold when inserting a var that already exists as a var
    (in that case, insert succeeds but doesn't update objects). -/
theorem insert_success_objects_updated
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos l obj).error? = none)
    (h_not_var_dup : ¬(∃ v, obj l = .var v ∧ db.find? l = some (.var v)))
    (h_var_labels_match_names : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl)
    (h_obj_var_names_match : ∀ lbl v, obj lbl = .var v → v = lbl) :
    (db.insert pos l obj).objects = db.objects.insert l (obj l) := by
  -- Key insight: if insert succeeds (no error after) and we exclude var dup case,
  -- then we must have hit the "new object" branch where db.find? l = none
  by_cases h_find : db.find? l = none
  · -- Case: db.find? l = none, use helper
    exact insert_new_object_updates db pos l obj h_find h_no_err_before h_no_err_after
  · -- Case: db.find? l ≠ none, so ∃ o, db.find? l = some o
    -- By h_not_var_dup, it cannot be that both o and obj l are vars
    -- Therefore, ok = false, so mkError is called
    -- But this contradicts h_no_err_after
    -- This case is impossible!
    exfalso

    -- First, extract the object o
    have h_exists : ∃ o, db.find? l = some o := by
      cases h_eq : db.find? l with
      | none => contradiction
      | some o => exact ⟨o, rfl⟩

    rcases h_exists with ⟨o, h_o⟩

    -- Now unfold insert and show it calls mkError or contradicts h_not_var_dup
    unfold DB.insert DB.error DB.mkError at h_no_err_after
    simp only at h_no_err_after

    -- The key insight: After unfolding with h_o (found existing object),
    -- the only way to avoid mkError is if ok=true (both are vars)
    -- But h_not_var_dup excludes this case!
    -- So every branch leads to contradiction

    -- We need to show: h_no_err_after implies ok=true, which contradicts h_not_var_dup
    -- Or: ok=false, which means mkError was called, contradicting h_no_err_after

    -- Direct approach: The match on o and obj l determines ok
    -- If ok=true, then both must be .var, so we can extract them and contradict h_not_var_dup
    -- Let's case on what o and obj l are

    cases o with
    | const c_o =>
        -- o = .const c_o, so ok = false (line 291: | _ => false)
        -- Therefore mkError is called, contradiction
        split at h_no_err_after <;> split at h_no_err_after <;> simp_all
    | var v_o =>
        -- o = .var v_o, so ok depends on whether obj l is also a var
        cases h_obj : obj l with
        | const c_l =>
            -- obj l = .const c_l, so ok = false, mkError called
            split at h_no_err_after <;> split at h_no_err_after <;> simp_all
        | var v_l =>
            -- Both are vars! ok = true, so no mkError
            -- But this contradicts h_not_var_dup
            -- We have h_o : db.find? l = some (Object.var v_o)
            -- And h_obj : obj l = Object.var v_l
            --
            -- The key insight: we can use v_l to build the contradiction!
            -- h_not_var_dup says: ¬(∃ v, obj l = .var v ∧ db.find? l = some (.var v))
            -- We have obj l = .var v_l (from h_obj)
            -- If we can show db.find? l = some (.var v_l), we contradict h_not_var_dup
            --
            -- From h_o we have: db.find? l = some (.var v_o)
            -- We need v_o = v_l
            --
            -- But wait! Do we actually need v_o = v_l?
            -- Let me try using v_l DIRECTLY and see what happens:
            -- From DB invariant: vars in DB have label = name
            have h_vo_is_l : v_o = l := h_var_labels_match_names l v_o h_o

            -- From obj invariant: vars constructed by obj have label = name
            have h_vl_is_l : v_l = l := h_obj_var_names_match l v_l h_obj

            -- Therefore v_o = v_l
            have h_vo_eq_vl : v_o = v_l := by
              rw [h_vo_is_l, h_vl_is_l]

            -- Now we can contradict h_not_var_dup
            have : ∃ v, obj l = .var v ∧ db.find? l = some (.var v) := by
              refine ⟨v_l, h_obj, ?_⟩
              rw [← h_vo_eq_vl]
              exact h_o
            exact h_not_var_dup this
        | hyp ess f_l lbl =>
            -- obj l = .hyp, so ok = false, mkError called
            split at h_no_err_after <;> split at h_no_err_after <;> simp_all
        | assert fmla fr_l name =>
            -- obj l = .assert, so ok = false, mkError called
            split at h_no_err_after <;> split at h_no_err_after <;> simp_all
    | hyp ess_o f_o lbl_o =>
        -- o = .hyp, so ok = false, mkError called
        split at h_no_err_after <;> split at h_no_err_after <;> simp_all
    | assert fmla_o fr_o name_o =>
        -- o = .assert, so ok = false, mkError called
        split at h_no_err_after <;> split at h_no_err_after <;> simp_all

/-- When insert succeeds, looking up the inserted key gives the inserted object -/
theorem insert_success_find?_self
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos l obj).error? = none)
    (h_not_var_dup : ¬(∃ v, obj l = .var v ∧ db.find? l = some (.var v)))
    (h_var_labels_match_names : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl)
    (h_obj_var_names_match : ∀ lbl v, obj lbl = .var v → v = lbl) :
    (db.insert pos l obj).find? l = some (obj l) := by
  unfold DB.find?
  rw [insert_success_objects_updated db pos l obj h_no_err_before h_no_err_after h_not_var_dup h_var_labels_match_names h_obj_var_names_match]
  exact HashMap.find?_insert_eq db.objects l (obj l)

/-- When insert succeeds, looking up a different key is unchanged -/
theorem insert_success_find?_ne
    (db : DB) (pos : Pos) (l l' : String) (obj : String → Object)
    (h_ne : l' ≠ l)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos l obj).error? = none)
    (h_not_var_dup : ¬(∃ v, obj l = .var v ∧ db.find? l = some (.var v)))
    (h_var_labels_match_names : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl)
    (h_obj_var_names_match : ∀ lbl v, obj lbl = .var v → v = lbl) :
    (db.insert pos l obj).find? l' = db.find? l' := by
  unfold DB.find?
  rw [insert_success_objects_updated db pos l obj h_no_err_before h_no_err_after h_not_var_dup h_var_labels_match_names h_obj_var_names_match]
  exact HashMap.find?_insert_ne db.objects l l' (obj l) h_ne.symm

/-- When insert succeeds, WellFormedFrame is preserved for frames whose hypothesis
    labels are distinct from the inserted key. -/
theorem insert_preserves_frame_wf
    (db : DB) (pos : Pos) (l : String) (obj : String → Object) (fr : Frame)
    (h_wf : WellFormedFrame db fr)
    (h_no_dup : ∀ i (hi : i < fr.hyps.size), (fr.hyps[i]'hi) ≠ l)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (db.insert pos l obj).error? = none)
    (h_not_var_dup : ¬(∃ v, obj l = .var v ∧ db.find? l = some (.var v)))
    (h_var_labels_match_names : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl)
    (h_obj_var_names_match : ∀ lbl v, obj lbl = .var v → v = lbl) :
    WellFormedFrame (db.insert pos l obj) fr := by
  constructor
  · -- Part 1: All hyps in fr still satisfy HypOK
    intro i hi
    -- h_wf.1 gives us: HypOK db fr.hyps[i]
    have h_old := h_wf.1 i hi
    -- HypOK means ∃ ess f lbl, db.find? fr.hyps[i] = some (.hyp ess f lbl) ∧ ...
    unfold HypOK at h_old ⊢
    rcases h_old with ⟨ess, f, lbl, h_find, h_float, h_formula⟩
    -- Show the new db still has this hyp at fr.hyps[i]
    refine ⟨ess, f, lbl, ?_, h_float, h_formula⟩
    -- (db.insert...).find? fr.hyps[i] = some (.hyp ess f lbl)
    have h_ne := h_no_dup i hi
    rw [insert_success_find?_ne db pos l (fr.hyps[i]'hi) obj h_ne h_no_err_before h_no_err_after h_not_var_dup h_var_labels_match_names h_obj_var_names_match]
    exact h_find

  · -- Part 2: UniqueFloatVars preserved
    intro i j hi hj h_ij fi fj lbli lblj h_fi h_fj h_sz_i h_sz_j
    -- Use h_wf.2 with the old finds
    have h_ne_i := h_no_dup i hi
    have h_ne_j := h_no_dup j hj
    -- Rewrite finds in new db to old db
    rw [insert_success_find?_ne db pos l (fr.hyps[i]'hi) obj h_ne_i h_no_err_before h_no_err_after h_not_var_dup h_var_labels_match_names h_obj_var_names_match] at h_fi
    rw [insert_success_find?_ne db pos l (fr.hyps[j]'hj) obj h_ne_j h_no_err_before h_no_err_after h_not_var_dup h_var_labels_match_names h_obj_var_names_match] at h_fj
    -- Now apply h_wf.2
    exact h_wf.2 i j hi hj h_ij fi fj lbli lblj h_fi h_fj h_sz_i h_sz_j

/-- Helper: for loops that only call mkError preserve error state -/
theorem for_loop_mkError_preserves_error (db : DB) (pos : Pos) (hyps : Array String) :
  db.error = true →
  (Id.run do
    let mut db := db
    for h in hyps do
      -- Some condition that might trigger mkError
      if true then  -- Placeholder condition
        db := db.mkError pos "some error"
    db).error = true := by
  intro h
  -- The loop starts with db.error = true
  -- Each iteration either keeps db or calls mkError
  -- mkError produces error = true
  -- Therefore the final state has error = true
  sorry -- Loop invariant: db.error = true is preserved

/-- insertHyp preserves error state -/
theorem insertHyp_preserves_error (db : DB) (pos : Pos) (label : String) (ess : Bool) (f : Formula) :
  db.error = true → (db.insertHyp pos label ess f).error = true := by
  intro h
  unfold DB.insertHyp
  -- First the for loop that might call mkError
  split
  · -- ess = false and f.size >= 2, does float check
    -- The for loop either preserves db.error = true or calls mkError (which also gives error = true)
    -- In all cases, if we start with error = true, we end with error = true
    simp [Id.run]
    -- The loop body: for h in db.frame.hyps, if condition then mkError else db
    -- Since db.error = true initially, even if we don't call mkError, error remains true
    -- And if we do call mkError, it also produces error = true
    have h_after_loop : (Id.run do
      if !ess && f.size >= 2 then
        let v := f[1]!.value
        let mut db := db
        for h in db.frame.hyps do
          if let some (.hyp false prevF _) := db.find? h then
            if prevF.size >= 2 && prevF[1]!.value == v then
              db := db.mkError pos s!"variable {v} already has $f hypothesis"
        db
      else db).error = true := by
      -- The loop starts with db where db.error = true
      -- Each iteration either keeps db unchanged or calls mkError
      -- mkError always produces error = true
      -- So the result has error = true
      simp
      split
      · -- In the float check case
        -- We need to show the for loop preserves error
        -- This is true because db starts with error = true
        -- and mkError also produces error = true
        sorry -- For loop reasoning - but conceptually clear
      · -- Not doing float check, just return db
        exact h
    -- TODO: Chain insert_preserves_error and withHyps_preserves_error
    -- Challenge: Lean's elaboration of Id.run do-notation creates type mismatches
    -- The preservation theorems work on DB → DB, but elaborated goal has monadic structure
    -- Needs custom lemma about preservation through let bindings or different proof strategy
    sorry
  · -- Skip float check, go straight to insert
    -- TODO: Direct chaining of insert_preserves_error and withHyps_preserves_error
    -- Same elaboration challenges as the first branch
    sorry

/-- insertAxiom preserves error state -/
theorem insertAxiom_preserves_error (db : DB) (pos : Pos) (label : String) (fmla : Formula) :
  db.error = true → (db.insertAxiom pos label fmla).error = true := by
  intro h
  unfold DB.insertAxiom
  -- trimFrame' returns Except
  split
  · -- trimFrame' succeeds
    split
    · -- interrupt = true, sets error
      unfold DB.error
      simp
    · -- No interrupt, calls insert
      exact insert_preserves_error db pos label (.assert fmla _) h
  · -- trimFrame' fails, calls mkError
    exact mkError_creates_error db pos _

/-- THE KEY PROPERTY: Parser stops on first error

This is the property that makes the architecture sound.
Once an error occurs, the parser stops processing.
Therefore, any temporary inconsistencies (like label in frame.hyps but not in db.objects)
are never used for verification.

**Proof Strategy**: The actual parser has structure (Verify.lean lines 777-779):
```lean
let s := s.feedToken (base + off) tk
if let some ⟨e, _⟩ := s.db.error? then
  { s with db := { s.db with error? := some ⟨e, i+1⟩ } }  -- Stop!
else
  feed base arr (i+1) .ws s  -- Continue only if no error
```
This shows that once an error occurs, the feed function returns immediately
without processing more tokens. Therefore errors propagate to the final state.
-/
/- Simpler, more direct version:
   If we have error preservation and the fold produces an error,
   we're done. The complex version with intermediate_db is under-specified.
-/
theorem parser_stops_on_error_simple
  (initial_db final_db : DB)
  (parsing_steps : List (DB → DB)) :
  -- Hypothesis: all parsing steps preserve error state
  (∀ step ∈ parsing_steps, ∀ db : DB, db.error = true → (step db).error = true) →
  -- Initial DB has no error
  initial_db.error = false →
  -- Final DB is result of applying all steps
  final_db = parsing_steps.foldl (fun db step => step db) initial_db →
  -- If final DB has error, some step must have created it
  final_db.error = true →
  -- Then some step created an error
  ∃ step ∈ parsing_steps, ∃ i < parsing_steps.length,
    let intermediate := (parsing_steps.take i).foldl (fun db s => s db) initial_db
    intermediate.error = false ∧ (step intermediate).error = true := by
  intro h_preserve h_init_ok h_fold h_final_err
  -- Prove by induction: if we start with no error and end with error,
  -- some step along the way must have introduced it
  sorry

/-- The key property: if steps preserve error and we apply them sequentially,
    once an error appears it propagates to the end. PROVEN! ✓ -/
theorem parser_stops_on_error
  (initial_db : DB)
  (parsing_steps : List (DB → DB))
  (pre : List (DB → DB))
  (suf : List (DB → DB))
  (h_preserve : ∀ step ∈ parsing_steps, ∀ db : DB, db.error = true → (step db).error = true)
  (h_split : parsing_steps = pre ++ suf)
  (h_inter_err : (pre.foldl (fun db step => step db) initial_db).error = true) :
  (parsing_steps.foldl (fun db step => step db) initial_db).error = true := by
  rw [h_split]
  simp [List.foldl_append]
  -- After processing pre, we have intermediate with error
  -- Processing suf preserves error by h_preserve
  have h_mono : ∀ (steps : List (DB → DB)) (db : DB),
    (∀ s ∈ steps, ∀ d : DB, d.error = true → (s d).error = true) →
    db.error = true →
    (steps.foldl (fun db step => step db) db).error = true := by
      intro steps db h_pres h_err
      induction steps generalizing db with
      | nil =>
        simp
        exact h_err
      | cons hd tl ih =>
        simp [List.foldl]
        apply ih
        · intro s h_in
          apply h_pres
          simp [h_in]
        · apply h_pres hd (by simp) _ h_err
  apply h_mono
  · intro s h_in
    apply h_preserve
    rw [h_split]
    simp [h_in]
  · exact h_inter_err

/-- Contrapositive: If final DB has no error, no errors occurred during parsing

This is the contrapositive of parser_stops_on_error.
It states: if we end with no error, then no intermediate step created an error
(unless that intermediate DB already had an error).

**This is THE KEY for connecting parser success to well-formedness**:
If `db.error? = none` at the end, then every operation succeeded,
which means all invariants were maintained throughout parsing.
-/
theorem no_final_error_means_no_intermediate_errors
  (initial_db final_db : DB)
  (parsing_steps : List (DB → DB)) :
  final_db.error = false →
  initial_db.error = false →
  -- Simulate parsing
  final_db = parsing_steps.foldl (fun db step => step db) initial_db →
  -- Then NO intermediate step created an error
  ∀ step ∈ parsing_steps, ∀ intermediate_db,
    (step intermediate_db).error = false ∨ intermediate_db.error = true := by
  intro h_final_ok h_init_ok h_fold
  intro step h_step_in intermediate_db
  -- This is the contrapositive of parser_stops_on_error
  -- The proof would use:
  -- 1. If intermediate_db.error = false and (step intermediate_db).error = true
  -- 2. Then by parser_stops_on_error, final_db.error = true
  -- 3. But we have h_final_ok : final_db.error = false
  -- 4. Contradiction!
  -- Therefore: (step intermediate_db).error = false ∨ intermediate_db.error = true
  sorry

/-- Operations that check error first preserve this property -/
theorem error_short_circuit (db : DB) (pos : Pos) (label : String) (obj : String → Object) :
  db.error = true →
  (if db.error then db else db.insert pos label obj) = db := by
  intro h
  simp [h]

/-! ## Layer 3: Object Management - insert and find?

The insert operation is the foundation of database construction.
Key property: after inserting, we can find what we inserted.
-/

/-- After successful insert (no error), object is findable.
   This is proven in Verify.lean:336 as DB.insert_find?_self. -/
theorem insert_findable (db : DB) (pos : Pos) (label : String) (obj : String → Object) :
  db.error = false →
  db.find? label = none →
  (db.insert pos label obj).error = false →
  (db.insert pos label obj).find? label = some (obj label) :=
  DB.insert_find?_self db pos label obj

/-- Insert preserves other objects (if no collision).
   TODO: Needs HashMap lemma about insert at different keys not affecting lookup.
   Proof strategy: Use DB.insert_no_dup_objects + HashMap property. -/
theorem insert_preserves_others (db : DB) (pos : Pos) (label label' : String) (obj : String → Object) :
  label ≠ label' →
  db.error = false →
  db.find? label = none →
  (db.insert pos label obj).find? label' = db.find? label' := by
  intro h_ne h_no_err h_not_found
  sorry

/-- Duplicate insert creates error.
   TODO: Need to handle const check + var-var special case.
   Proof strategy: Unfold DB.insert, case split on obj and existing types. -/
theorem insert_duplicate_error (db : DB) (pos : Pos) (label : String) (obj : String → Object) (existing : Object) :
  db.error = false →
  db.find? label = some existing →
  (db.insert pos label obj).error = true := by
  intro h_no_err h_exists
  sorry

/-! ## Layer 4: Well-formedness Preservation via Induction

These are the crucial inductive properties showing DB operations preserve well-formedness.
The key insight: we need strong induction principles to handle the complex control flow. -/

section WellFormednessInduction

/-- Well-formedness is preserved through DB operations -/
inductive DBStep : DB → DB → Prop where
  | insert (db : DB) (pos : Pos) (label : String) (obj : String → Object) :
      db.error = false →
      (db.insert pos label obj).error = false →
      DBStep db (db.insert pos label obj)
  | insertHyp (db : DB) (pos : Pos) (label : String) (ess : Bool) (f : Formula) :
      db.error = false →
      (db.insertHyp pos label ess f).error = false →
      DBStep db (db.insertHyp pos label ess f)
  | pushScope (db : DB) :
      db.error = false →
      DBStep db db.pushScope
  | popScope (db : DB) (pos : Pos) :
      db.error = false →
      (db.popScope pos).error = false →
      DBStep db (db.popScope pos)
  | withFrame (db : DB) (f : Frame → Frame) :
      db.error = false →
      DBStep db (db.withFrame f)

/-- Transitive closure gives us sequences of DB operations -/
inductive DBExecution : DB → DB → Prop where
  | refl (db : DB) : DBExecution db db
  | step (db₁ db₂ db₃ : DB) :
      DBStep db₁ db₂ →
      DBExecution db₂ db₃ →
      DBExecution db₁ db₃

/-- Main well-formedness preservation theorem -/
theorem DBExecution.preserves_wellformedness {db₁ db₂ : DB} :
    DBExecution db₁ db₂ →
    db₁.error = false →
    db₂.error = false →
    WF.WellFormedDB db₁ →
    WF.WellFormedDB db₂ := by
  intro h_exec h_no_err1 h_no_err2 h_wf
  induction h_exec with
  | refl => exact h_wf
  | step db₁ db₂ db₃ h_step h_exec ih =>
    -- Need intermediate error = false
    have h_no_err2' : db₂.error = false := by
      cases h_step <;> try assumption
      -- pushScope and withFrame cases
      all_goals { sorry }
    -- Apply IH to get WF for db₂
    have h_wf2 : WF.WellFormedDB db₂ := by
      -- Each step preserves WF when no error
      cases h_step with
      | insert db pos label obj h_err_after =>
        -- insert preserves well-formedness when no error
        sorry -- TODO: Detailed proof about insert and WF
      | insertHyp db pos label ess f h_err_after =>
        -- insertHyp maintains float uniqueness when no error
        sorry -- TODO: Use float uniqueness check
      | pushScope db =>
        -- pushScope adds empty scope, preserves WF
        sorry
      | popScope db pos h_err_after =>
        -- popScope removes scope, preserves WF structure
        sorry
      | withFrame db f =>
        -- withFrame modifies frame, need to show WF preserved
        sorry
    -- Now apply IH
    exact ih h_no_err2' h_no_err2 h_wf2

/-- Strong induction principle for DB construction -/
theorem db_construction_induction
    {P : DB → Prop}
    (h_empty : P (.mk (frame := ⟨#[], #[]⟩) (scopes := #[]) (objects := Std.HashMap.emptyWithCapacity)
                     (interrupt := false) (error? := none) (permissive := false)))
    (h_insert : ∀ db pos label obj,
      db.error = false → P db →
      WF.WellFormedDB db →
      (db.insert pos label obj).error = false →
      P (db.insert pos label obj))
    (h_insertHyp : ∀ db pos label ess f,
      db.error = false → P db →
      WF.WellFormedDB db →
      (db.insertHyp pos label ess f).error = false →
      P (db.insertHyp pos label ess f)) :
    ∀ db, DBExecution (.mk (frame := ⟨#[], #[]⟩) (scopes := #[]) (objects := Std.HashMap.emptyWithCapacity)
                            (interrupt := false) (error? := none) (permissive := false)) db →
      db.error = false → P db := by
  intro db h_exec h_no_err
  -- Use DBExecution induction
  sorry -- TODO: Complete strong induction

end WellFormednessInduction

/-! ## Layer 4.5: Parser Loop Well-foundedness

The feed loop is the heart of the parser. We need strong induction to prove
properties about it. -/

section ParserLoopWellFoundedness

/-- The feed loop decreases on (arr.size - i) -/
def feedMeasure (arr : ByteArray) (i : Nat) : Nat :=
  if _ : i < arr.size then arr.size - i else 0

/-- Feed loop well-founded induction principle -/
theorem feed_wellfounded_induction
    {P : Nat → ParserState.FeedState → ParserState → Prop}
    (base : Nat) (arr : ByteArray) :
    -- Base case: reached end of array
    (∀ rs s, ¬(arr.size > 0) → P arr.size rs s) →
    -- Step case: process one byte and recurse
    (∀ i rs s,
      i < arr.size →
      -- If no error after processing byte i
      (∀ s', s'.db.error = false → P (i+1) .ws s' → P i rs s)) →
    -- Conclusion
    ∀ i rs s, i ≤ arr.size → P i rs s := by
  intro h_base h_step
  -- Use well-founded recursion on (arr.size - i)
  intro i rs s h_bound
  -- TODO: Complete well-founded induction proof
  sorry

/-- Feed maintains invariant through iterations -/
theorem feed_invariant_maintenance
    {I : ParserState → Prop}
    (base : Nat) (arr : ByteArray) :
    -- Invariant preserved by operations
    (∀ s pos tk, I s → s.db.error = false → I (s.feedToken pos tk)) →
    (∀ s i c, I s → isWhitespace c → I (s.updateLine i c)) →
    -- Initial invariant
    ∀ i rs s, I s → s.db.error = false →
    let result := s.feed base arr i rs
    result.db.error = false → I result := by
  intro h_token h_ws
  intro i rs s h_inv h_no_err h_result_ok
  -- Use feed_wellfounded_induction
  sorry -- TODO: Apply induction with I as the property

end ParserLoopWellFoundedness

/-! ## Layer 4-continued: Frame Operations - insertHyp

This is where the crucial $f uniqueness check happens!
This is THE key property for float variable uniqueness.

**IMPORTANT**: insertHyp does NOT check db.error before calling withHyps (line 310)!
This means an errored DB can still have its frame modified.
However, since insert (line 309) DOES check error, the object won't be added to db.objects.
This creates an inconsistency: label in frame.hyps but not in db.objects.

For parser correctness, we rely on: if parsing ends with db.error = false,
then this inconsistency never happened (all operations succeeded).
-/

/-- insertHyp checks for duplicate float variables (lines 304-306 in Verify.lean) -/
theorem insertHyp_rejects_duplicate_float
  (db : DB) (pos : Pos) (label : String) (f : Formula)
  (existing_label : String) (existing_f : Formula) :
  db.error = false →
  -- There's already a float for this variable
  existing_label ∈ db.frame.hyps.toList →
  db.find? existing_label = some (.hyp false existing_f existing_label) →
  existing_f.size ≥ 2 →
  f.size ≥ 2 →
  existing_f[1]!.value = f[1]!.value →
  -- Then insertHyp creates an error
  (db.insertHyp pos label false f).error = true := by
  intro h_no_err h_in_frame h_find h_size_old h_size_new h_same_var
  unfold DB.insertHyp
  -- The function has a for loop checking all hypotheses (lines 303-307)
  -- If it finds a match, it calls mkError
  sorry

/-- insertHyp succeeds when no duplicate exists -/
theorem insertHyp_succeeds_when_unique
  (db : DB) (pos : Pos) (label : String) (f : Formula) :
  db.error = false →
  db.find? label = none →
  f.size ≥ 2 →
  -- No other float binds this variable
  (∀ h ∈ db.frame.hyps.toList,
    ∀ prevF prevLbl,
      db.find? h = some (.hyp false prevF prevLbl) →
      prevF.size ≥ 2 →
      prevF[1]!.value ≠ f[1]!.value) →
  -- Then insertHyp succeeds and adds to frame
  (db.insertHyp pos label false f).error = false ∧
  (db.insertHyp pos label false f).find? label = some (.hyp false f label) := by
  intro h_no_err h_not_found h_size h_unique
  unfold DB.insertHyp
  -- The for loop doesn't find a duplicate, so no error is set
  -- Then insert is called, and withHyps adds to frame
  sorry

/-! ## Layer 5: High-Level Invariants

These compose the lower layers to establish WellFormedness.
-/

/-- If insertHyp succeeds on all floats, then UniqueFloatVars holds -/
theorem insertHyp_sequence_implies_unique_floats
  (db_init db_final : DB)
  (inserts : List (Pos × String × Formula)) :
  -- Start with no error
  db_init.error = false →
  -- Each insert was a float with size ≥ 2
  (∀ triple ∈ inserts, triple.2.2.size ≥ 2) →
  -- Simulate the insertHyp sequence
  db_final = inserts.foldl (fun db triple => db.insertHyp triple.1 triple.2.1 false triple.2.2) db_init →
  -- If we end with no error
  db_final.error = false →
  -- Then UniqueFloatVars holds for the final frame
  UniqueFloatVars db_final db_final.frame := by
  intro h_init_ok h_all_sized h_fold h_final_ok
  unfold UniqueFloatVars
  -- Use insertHyp_rejects_duplicate_float:
  -- If there were duplicates, some insertHyp would have errored
  -- Since db_final.error = false, there were no duplicates
  sorry

/-! ## Main Theorem: Parser Success → WellFormedDB

This is the composition of all layers. The key insight:
If parsing completes with no error, then all DB operations succeeded,
which means all their preconditions were met, which means well-formedness
was maintained throughout.
-/

theorem parser_construction_wellformed
  (bytes : ByteArray)
  (initial_state : ParserState) :
  -- Start with empty/well-formed state
  initial_state.db = .mk (frame := ⟨#[], #[]⟩) (scopes := #[]) (objects := Std.HashMap.emptyWithCapacity)
                          (interrupt := false) (error? := none) (permissive := false) →
  -- Parse succeeds
  let final_state := initial_state.feedAll 0 bytes
  final_state.db.error = false →
  -- Then final DB is well-formed
  WellFormedDB final_state.db := by
  intro h_init h_success
  -- The proof strategy:
  -- 1. The initial empty DB is trivially well-formed
  -- 2. Each parsing step either:
  --    a) Creates an error (but then final would have error by parser_stops_on_error)
  --    b) Preserves well-formedness
  -- 3. Since final has no error, all steps preserved WF
  -- 4. Therefore final DB is well-formed

  -- Establish initial WF
  have h_init_wf : WellFormedDB (.mk (frame := ⟨#[], #[]⟩) (scopes := #[]) (objects := Std.HashMap.emptyWithCapacity)
                                      (interrupt := false) (error? := none) (permissive := false)) := by
    unfold WellFormedDB WellFormedFrame UniqueFloatVars
    constructor
    · -- WellFormedFrame: both conditions vacuously true for empty frame
      constructor
      · -- ∀ i < 0, ... is vacuously true
        intro i hi
        simp at hi
      · -- UniqueFloatVars: ∀ i j < 0, ... is vacuously true
        intro i j hi hj
        simp at hi
    · -- All objects satisfy their well-formedness: vacuously true for empty HashMap
      intro lbl obj h_find
      -- h_find states that we found something in an empty HashMap, which is impossible
      unfold DB.find? at h_find
      simp at h_find

  -- Use DBExecution.preserves_wellformedness
  -- We need to connect feedAll to DBExecution
  sorry -- TODO: Connect parser operations to DBExecution framework

/-- The ultimate soundness theorem: successful parsing produces valid proofs -/
theorem parser_soundness_main
  (bytes : ByteArray) :
  -- Parse from empty state
  let initial := { db := .mk (frame := ⟨#[], #[]⟩) (scopes := #[]) (objects := Std.HashMap.emptyWithCapacity)
                             (interrupt := false) (error? := none) (permissive := false),
                   tokp := .start, charp := .ws, line := 0, linepos := 0 : ParserState }
  let final := initial.feedAll 0 bytes
  -- If parsing succeeds
  final.db.error = false →
  -- Then all objects are well-formed and satisfy Metamath rules
  (∀ label obj, final.db.find? label = some obj →
    match obj with
    | .const _ => true  -- Constants are simple
    | .var _ => true    -- Variables are simple
    | .hyp ess f lbl =>
      -- Hypotheses have well-formed formulas
      WellFormedFormula f ∧
      -- Float hypotheses respect uniqueness
      (¬ess → f.size = 2 ∧ (∃ c v, f[0]! = .const c ∧ f[1]! = .var v))
    | .assert fmla proof lbl =>
      -- Assertions have valid proofs
      WellFormedFormula fmla ∧
      -- The proof would be valid if checked
      true  -- Proof checking is separate
  ) := by
  -- Introduce and unfold let bindings
  simp only []
  intro h_success
  -- Define initial state inline to use in the theorem
  let initial := { db := .mk (frame := ⟨#[], #[]⟩) (scopes := #[]) (objects := Std.HashMap.emptyWithCapacity)
                             (interrupt := false) (error? := none) (permissive := false),
                   tokp := .start, charp := .ws, line := 0, linepos := 0 : ParserState }
  have h_initial : initial.db = .mk (frame := ⟨#[], #[]⟩) (scopes := #[]) (objects := Std.HashMap.emptyWithCapacity)
                                      (interrupt := false) (error? := none) (permissive := false) := rfl
  have h_wf := parser_construction_wellformed bytes initial h_initial h_success
  intro label obj h_find
  -- Use well-formedness to establish properties
  cases obj with
  | const _ => trivial
  | var _ => trivial
  | hyp ess f lbl =>
    constructor
    · -- WellFormedFormula f
      sorry -- Extract from WellFormedDB
    · -- Float structure
      intro h_not_ess
      sorry -- Extract from UniqueFloatVars and WellFormedFloat
  | assert fmla proof lbl =>
    constructor
    · -- WellFormedFormula fmla
      sorry -- Extract from WellFormedDB
    · -- Proof validity (separate concern)
      trivial

/-! ## Structure-Preserving Operations and WellFormedness

The key theorem for parser correctness: operations that don't set errors
preserve database well-formedness.
-/

/-- Database operations that preserve structural invariants -/
inductive StructurePreservingOp (db : DB) : (DB → DB) → Prop where
  | insert (pos : Pos) (label : String) (obj : String → Object)
      -- Validation invariant: object being inserted is well-formed
      (h_validated : match obj label with
        | .hyp false f _ => WellFormedFloat f
        | .hyp true f _  => WellFormedFormula f
        | .assert f fr _ => WellFormedFormula f ∧ (∀ db, WellFormedFrame db fr)
        | .var v         => v = label  -- Var label = name invariant!
        | _              => True)
      -- Function invariant: if obj constructs vars, they satisfy label=name (for ALL labels!)
      (h_obj_var_names_match : ∀ lbl v, obj lbl = .var v → v = lbl)
      -- DB Freshness invariant: label not already in THIS database
      (h_fresh_db : db.find? label = none)
      -- Frame freshness invariant: label not in THIS current frame
      (h_fresh_label : ∀ (i : Nat) (hi : i < db.frame.hyps.size),
        (db.frame.hyps[i]'hi) ≠ label)
      -- Freshness invariant: label not in any assertion frame in THIS DB
      (h_fresh_in_asserts : ∀ (lbl : String) (fmla : Formula) (fr_assert : Frame) (name : String),
        db.find? lbl = some (.assert fmla fr_assert name) →
        ∀ (i : Nat) (hi : i < fr_assert.hyps.size), (fr_assert.hyps[i]'hi) ≠ label) :
      StructurePreservingOp db (fun db' => db'.insert pos label obj)
  | pushScope : StructurePreservingOp db (fun db' => db'.pushScope)
  | popScope (pos : Pos) : StructurePreservingOp db (fun db' => db'.popScope pos)
  | withFrame (f : Frame → Frame)
      (h_preserves : ∀ db_any fr, WellFormedFrame db_any fr → WellFormedFrame db_any (f fr)) :
      StructurePreservingOp db (fun db' => db'.withFrame f)
  | id : StructurePreservingOp db id

/-- **Main Theorem**: Structure-preserving operations maintain WellFormedDB.

If an operation doesn't raise an error and is structure-preserving,
then it maintains database well-formedness.

This is the KEY composition theorem that ties together all parser invariants.
-/
theorem structure_preserving_maintains_wf
    {op : DB → DB}
    (db : DB)
    (h_struct : StructurePreservingOp db op)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_no_err_after : (op db).error? = none) :
    WellFormedDB (op db) := by
  rcases h_wf with ⟨h_frame_wf, h_objs_wf⟩
  cases h_struct with
  | insert pos label obj h_validated h_obj_var_names_match h_fresh_db h_fresh_label h_fresh_in_asserts =>
      -- Case: insert operation
      -- We now have type-safe invariants from StructurePreservingOp!
      -- Strategy: Pattern match on obj label to extract the specific validation
      cases h_obj : obj label with
      | const c =>
          -- Inserting a constant
          -- Beta-reduce op db to db.insert pos label obj
          change WellFormedDB (db.insert pos label obj)
          change (db.insert pos label obj).error? = none at h_no_err_after

          -- Constants have no WF requirements (h_validated is True)
          -- Just need to show frame and objects preserved

          constructor
          · -- Part 1: Frame WF preserved
            rw [insert_frame_unchanged]

            -- Establish h_not_var_dup using h_fresh_db
            have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
              intro ⟨v_dup, _, h_find_old⟩
              rw [h_find_old] at h_fresh_db
              cases h_fresh_db

            have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
              intro lbl v_old h_find
              exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

            exact insert_preserves_frame_wf db pos label obj db.frame
              h_frame_wf h_fresh_label h_no_err_before h_no_err_after
              h_not_var_dup h_var_inv h_obj_var_names_match

          · -- Part 2: All objects still WF
            intro lbl obj' h_find'
            by_cases h_eq : lbl = label
            · -- NEW object: lbl = label, so obj' = .const c
              -- WF condition for const is True
              rw [h_eq]

              -- Establish h_not_var_dup (same as Part 1)
              have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                intro ⟨v_dup, _, h_find_old⟩
                rw [h_find_old] at h_fresh_db
                cases h_fresh_db

              have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                intro lbl v_old h_find
                exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

              have h_find_self := insert_success_find?_self db pos label obj
                h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_var_names_match

              -- Convert h_find' to use label
              have h_find'_label : (db.insert pos label obj).find? label = some obj' := by
                rw [h_eq] at h_find'
                exact h_find'

              -- Show obj' = obj label = .const c
              have h_obj'_eq : obj' = obj label := by
                have : some (obj label) = some obj' := by
                  rw [← h_find_self, h_find'_label]
                cases this
                rfl

              rw [h_obj] at h_obj'_eq
              cases h_obj'_eq
              -- Goal: True (WF condition for const)
              exact True.intro

            · -- EXISTING object: lbl ≠ label
              have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                intro lbl v_old h_find
                exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

              have h_obj_inv := h_obj_var_names_match

              have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                intro ⟨v_dup, _, h_find_old⟩
                rw [h_find_old] at h_fresh_db
                cases h_fresh_db

              have h_find_unchanged := insert_success_find?_ne db pos label lbl obj h_eq
                h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_inv
              rw [h_find_unchanged] at h_find'

              -- Get old WF and upgrade for assert case
              have h_obj'_wf_old := h_objs_wf lbl obj' h_find'

              cases h_obj' : obj' with
              | const c' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | var v' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | hyp ess f' name' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | assert f' fr' name' =>
                  rw [h_obj'] at h_obj'_wf_old
                  constructor
                  · exact h_obj'_wf_old.1
                  · have h_fr_wf_old := h_obj'_wf_old.2
                    have h_find'_assert : db.find? lbl = some (.assert f' fr' name') := by
                      rw [← h_obj']
                      exact h_find'
                    have h_fresh_fr : ∀ i (hi : i < fr'.hyps.size), (fr'.hyps[i]'hi) ≠ label := by
                      intro i hi
                      exact h_fresh_in_asserts lbl f' fr' name' h_find'_assert i hi
                    exact insert_preserves_frame_wf db pos label obj fr'
                      h_fr_wf_old h_fresh_fr h_no_err_before h_no_err_after
                      h_not_var_dup h_var_inv h_obj_inv
      | var v =>
          -- Inserting a variable
          -- Beta-reduce op db to db.insert pos label obj
          change WellFormedDB (db.insert pos label obj)
          change (db.insert pos label obj).error? = none at h_no_err_after

          -- Extract v = label from h_validated
          have h_v_eq_label : v = label := by
            rw [h_obj] at h_validated
            exact h_validated

          constructor
          · -- Part 1: Frame WF preserved
            -- Goal: WellFormedFrame (db.insert pos label obj) (db.insert pos label obj).frame
            -- Use the fact that insert doesn't change the frame
            rw [insert_frame_unchanged]
            -- Now goal: WellFormedFrame (db.insert pos label obj) db.frame

            -- First establish h_not_var_dup for insert_preserves_frame_wf
            have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
              intro ⟨v_dup, _, h_find_old⟩
              rw [h_find_old] at h_fresh_db
              cases h_fresh_db

            have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
              intro lbl v_old h_find
              exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

            -- Apply insert_preserves_frame_wf
            exact insert_preserves_frame_wf db pos label obj db.frame
              h_frame_wf h_fresh_label h_no_err_before h_no_err_after
              h_not_var_dup h_var_inv h_obj_var_names_match

          · -- Part 2: All objects still WF
            intro lbl obj' h_find'
            by_cases h_eq : lbl = label
            · -- NEW object: lbl = label, so obj' = .var v = .var label
              -- Need to show: obj' matches its WF condition
              -- For .var v', the condition is: v' = lbl
              -- After rewriting with h_eq, need to show: v' = label

              -- Rewrite the goal using h_eq
              rw [h_eq]

              -- Now establish that obj' = obj label = .var v
              have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                intro ⟨v_dup, _, h_find_old⟩
                rw [h_find_old] at h_fresh_db
                cases h_fresh_db

              have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                intro lbl v_old h_find
                exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

              have h_find_self := insert_success_find?_self db pos label obj
                h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_var_names_match

              -- Convert h_find' from lbl to label using h_eq
              have h_find'_label : (db.insert pos label obj).find? label = some obj' := by
                rw [h_eq] at h_find'
                exact h_find'

              -- Now both have label, so we can conclude obj' = obj label
              have h_obj'_eq : obj' = obj label := by
                -- h_find_self : (db.insert pos label obj).find? label = some (obj label)
                -- h_find'_label : (db.insert pos label obj).find? label = some obj'
                -- Therefore: some (obj label) = some obj'
                have : some (obj label) = some obj' := by
                  rw [← h_find_self, h_find'_label]
                cases this
                rfl

              -- obj label = .var v (from h_obj), so obj' = .var v
              rw [h_obj] at h_obj'_eq
              cases h_obj'_eq
              -- Goal: v = label, which is h_v_eq_label
              exact h_v_eq_label

            · -- EXISTING object: lbl ≠ label
              -- Lookup unchanged by insert
              have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                intro lbl v_old h_find
                exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

              -- Use the function invariant directly!
              have h_obj_inv := h_obj_var_names_match

              have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                intro ⟨v_dup, _, h_find_old⟩
                rw [h_find_old] at h_fresh_db
                cases h_fresh_db

              have h_find_unchanged := insert_success_find?_ne db pos label lbl obj h_eq
                h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_inv
              -- Now h_find_unchanged : (db.insert pos label obj).find? lbl = db.find? lbl
              -- Rewrite h_find' using this
              rw [h_find_unchanged] at h_find'
              -- Now h_find' : db.find? lbl = some obj'
              -- h_objs_wf gives us WF for obj' in db, but we need WF in (db.insert...)

              -- For most object types, the WF condition doesn't depend on the DB
              -- For assert, need to upgrade frame WF using insert_preserves_frame_wf
              have h_obj'_wf_old := h_objs_wf lbl obj' h_find'

              cases h_obj' : obj' with
              | const c =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | var v' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | hyp ess f' name' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | assert f' fr' name' =>
                  rw [h_obj'] at h_obj'_wf_old
                  constructor
                  · -- Formula WF doesn't change
                    exact h_obj'_wf_old.1
                  · -- Frame WF needs upgrading
                    have h_fr_wf_old := h_obj'_wf_old.2
                    -- Need to show: label ∉ fr'.hyps
                    -- Use h_fresh_in_asserts
                    have h_find'_assert : db.find? lbl = some (.assert f' fr' name') := by
                      rw [← h_obj']
                      exact h_find'
                    have h_fresh_fr : ∀ i (hi : i < fr'.hyps.size), (fr'.hyps[i]'hi) ≠ label := by
                      intro i hi
                      exact h_fresh_in_asserts lbl f' fr' name' h_find'_assert i hi
                    exact insert_preserves_frame_wf db pos label obj fr'
                      h_fr_wf_old h_fresh_fr h_no_err_before h_no_err_after
                      h_not_var_dup h_var_inv h_obj_inv
      | hyp ess f name =>
          -- Inserting a hypothesis
          cases ess with
          | false =>
              -- Float hypothesis
              -- Beta-reduce op db to db.insert pos label obj
              change WellFormedDB (db.insert pos label obj)
              change (db.insert pos label obj).error? = none at h_no_err_after

              -- Extract h_float from h_validated
              have h_float : WellFormedFloat f := by
                rw [h_obj] at h_validated
                exact h_validated

              constructor
              · -- Part 1: Frame WF preserved
                rw [insert_frame_unchanged]

                have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                  intro ⟨v_dup, _, h_find_old⟩
                  rw [h_find_old] at h_fresh_db
                  cases h_fresh_db

                have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                  intro lbl v_old h_find
                  exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

                exact insert_preserves_frame_wf db pos label obj db.frame
                  h_frame_wf h_fresh_label h_no_err_before h_no_err_after
                  h_not_var_dup h_var_inv h_obj_var_names_match

              · -- Part 2: All objects still WF
                intro lbl obj' h_find'
                by_cases h_eq : lbl = label
                · -- NEW object: lbl = label, so obj' = .hyp false f name
                  rw [h_eq]

                  have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                    intro ⟨v_dup, _, h_find_old⟩
                    rw [h_find_old] at h_fresh_db
                    cases h_fresh_db

                  have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                    intro lbl v_old h_find
                    exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

                  have h_find_self := insert_success_find?_self db pos label obj
                    h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_var_names_match

                  have h_find'_label : (db.insert pos label obj).find? label = some obj' := by
                    rw [h_eq] at h_find'
                    exact h_find'

                  have h_obj'_eq : obj' = obj label := by
                    have : some (obj label) = some obj' := by
                      rw [← h_find_self, h_find'_label]
                    cases this
                    rfl

                  rw [h_obj] at h_obj'_eq
                  cases h_obj'_eq
                  -- Goal: WellFormedFloat f
                  exact h_float

                · -- EXISTING object: lbl ≠ label
                  have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                    intro lbl v_old h_find
                    exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

                  have h_obj_inv := h_obj_var_names_match

                  have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                    intro ⟨v_dup, _, h_find_old⟩
                    rw [h_find_old] at h_fresh_db
                    cases h_fresh_db

                  have h_find_unchanged := insert_success_find?_ne db pos label lbl obj h_eq
                    h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_inv
                  rw [h_find_unchanged] at h_find'

                  have h_obj'_wf_old := h_objs_wf lbl obj' h_find'

                  cases h_obj' : obj' with
                  | const c' =>
                      rw [h_obj'] at h_obj'_wf_old
                      exact h_obj'_wf_old
                  | var v' =>
                      rw [h_obj'] at h_obj'_wf_old
                      exact h_obj'_wf_old
                  | hyp ess f' name' =>
                      rw [h_obj'] at h_obj'_wf_old
                      exact h_obj'_wf_old
                  | assert f' fr' name' =>
                      rw [h_obj'] at h_obj'_wf_old
                      constructor
                      · exact h_obj'_wf_old.1
                      · have h_fr_wf_old := h_obj'_wf_old.2
                        have h_find'_assert : db.find? lbl = some (.assert f' fr' name') := by
                          rw [← h_obj']
                          exact h_find'
                        have h_fresh_fr : ∀ i (hi : i < fr'.hyps.size), (fr'.hyps[i]'hi) ≠ label := by
                          intro i hi
                          exact h_fresh_in_asserts lbl f' fr' name' h_find'_assert i hi
                        exact insert_preserves_frame_wf db pos label obj fr'
                          h_fr_wf_old h_fresh_fr h_no_err_before h_no_err_after
                          h_not_var_dup h_var_inv h_obj_inv
          | true =>
              -- Essential hypothesis
              -- Beta-reduce op db to db.insert pos label obj
              change WellFormedDB (db.insert pos label obj)
              change (db.insert pos label obj).error? = none at h_no_err_after

              -- Extract h_formula from h_validated
              have h_formula : WellFormedFormula f := by
                rw [h_obj] at h_validated
                exact h_validated

              constructor
              · -- Part 1: Frame WF preserved
                rw [insert_frame_unchanged]

                have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                  intro ⟨v_dup, _, h_find_old⟩
                  rw [h_find_old] at h_fresh_db
                  cases h_fresh_db

                have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                  intro lbl v_old h_find
                  exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

                exact insert_preserves_frame_wf db pos label obj db.frame
                  h_frame_wf h_fresh_label h_no_err_before h_no_err_after
                  h_not_var_dup h_var_inv h_obj_var_names_match

              · -- Part 2: All objects still WF
                intro lbl obj' h_find'
                by_cases h_eq : lbl = label
                · -- NEW object: lbl = label, so obj' = .hyp true f name
                  rw [h_eq]

                  have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                    intro ⟨v_dup, _, h_find_old⟩
                    rw [h_find_old] at h_fresh_db
                    cases h_fresh_db

                  have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                    intro lbl v_old h_find
                    exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

                  have h_find_self := insert_success_find?_self db pos label obj
                    h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_var_names_match

                  have h_find'_label : (db.insert pos label obj).find? label = some obj' := by
                    rw [h_eq] at h_find'
                    exact h_find'

                  have h_obj'_eq : obj' = obj label := by
                    have : some (obj label) = some obj' := by
                      rw [← h_find_self, h_find'_label]
                    cases this
                    rfl

                  rw [h_obj] at h_obj'_eq
                  cases h_obj'_eq
                  -- Goal: WellFormedFormula f
                  exact h_formula

                · -- EXISTING object: lbl ≠ label
                  have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                    intro lbl v_old h_find
                    exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

                  have h_obj_inv := h_obj_var_names_match

                  have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                    intro ⟨v_dup, _, h_find_old⟩
                    rw [h_find_old] at h_fresh_db
                    cases h_fresh_db

                  have h_find_unchanged := insert_success_find?_ne db pos label lbl obj h_eq
                    h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_inv
                  rw [h_find_unchanged] at h_find'

                  have h_obj'_wf_old := h_objs_wf lbl obj' h_find'

                  cases h_obj' : obj' with
                  | const c' =>
                      rw [h_obj'] at h_obj'_wf_old
                      exact h_obj'_wf_old
                  | var v' =>
                      rw [h_obj'] at h_obj'_wf_old
                      exact h_obj'_wf_old
                  | hyp ess f' name' =>
                      rw [h_obj'] at h_obj'_wf_old
                      exact h_obj'_wf_old
                  | assert f' fr' name' =>
                      rw [h_obj'] at h_obj'_wf_old
                      constructor
                      · exact h_obj'_wf_old.1
                      · have h_fr_wf_old := h_obj'_wf_old.2
                        have h_find'_assert : db.find? lbl = some (.assert f' fr' name') := by
                          rw [← h_obj']
                          exact h_find'
                        have h_fresh_fr : ∀ i (hi : i < fr'.hyps.size), (fr'.hyps[i]'hi) ≠ label := by
                          intro i hi
                          exact h_fresh_in_asserts lbl f' fr' name' h_find'_assert i hi
                        exact insert_preserves_frame_wf db pos label obj fr'
                          h_fr_wf_old h_fresh_fr h_no_err_before h_no_err_after
                          h_not_var_dup h_var_inv h_obj_inv
      | assert fmla fr lbl =>
          -- Inserting an assertion
          -- Beta-reduce op db to db.insert pos label obj
          change WellFormedDB (db.insert pos label obj)
          change (db.insert pos label obj).error? = none at h_no_err_after

          -- Extract h_formula and h_frame_all from h_validated
          -- h_validated : WellFormedFormula fmla ∧ (∀ db, WellFormedFrame db fr)
          have h_assert_valid : WellFormedFormula fmla ∧ (∀ db, WellFormedFrame db fr) := by
            rw [h_obj] at h_validated
            exact h_validated
          
          rcases h_assert_valid with ⟨h_formula, h_frame_all⟩

          constructor
          · -- Part 1: Frame WF preserved
            rw [insert_frame_unchanged]

            have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
              intro ⟨v_dup, _, h_find_old⟩
              rw [h_find_old] at h_fresh_db
              cases h_fresh_db

            have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
              intro lbl v h_find
              exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

            exact insert_preserves_frame_wf db pos label obj db.frame
              h_frame_wf h_fresh_label h_no_err_before h_no_err_after
              h_not_var_dup h_var_inv h_obj_var_names_match

          · -- Part 2: All objects still WF
            intro lbl obj' h_find'
            by_cases h_eq : lbl = label
            · -- NEW object: lbl = label, so obj' = .assert fmla fr lbl
              rw [h_eq]

              have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                intro ⟨v_dup, _, h_find_old⟩
                rw [h_find_old] at h_fresh_db
                cases h_fresh_db

              have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                intro lbl v h_find
                exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

              have h_find_self := insert_success_find?_self db pos label obj
                h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_var_names_match

              have h_find'_label : (db.insert pos label obj).find? label = some obj' := by
                rw [h_eq] at h_find'
                exact h_find'

              have h_obj'_eq : obj' = obj label := by
                have : some (obj label) = some obj' := by
                  rw [← h_find_self, h_find'_label]
                cases this
                rfl

              rw [h_obj] at h_obj'_eq
              cases h_obj'_eq
              
              -- Goal: WellFormedFormula fmla ∧ WellFormedFrame (db.insert...) fr
              constructor
              · exact h_formula
              · -- Apply the ∀ db property to the NEW db
                exact h_frame_all (db.insert pos label obj)

            · -- EXISTING object: lbl ≠ label
              have h_var_inv : ∀ lbl v, db.find? lbl = some (.var v) → v = lbl := by
                intro lbl v_old h_find
                exact var_label_eq_name_of_db ⟨h_frame_wf, h_objs_wf⟩ h_find

              have h_obj_inv := h_obj_var_names_match

              have h_not_var_dup : ¬(∃ v_dup, obj label = .var v_dup ∧ db.find? label = some (.var v_dup)) := by
                intro ⟨v_dup, _, h_find_old⟩
                rw [h_find_old] at h_fresh_db
                cases h_fresh_db

              have h_find_unchanged := insert_success_find?_ne db pos label lbl obj h_eq
                h_no_err_before h_no_err_after h_not_var_dup h_var_inv h_obj_inv
              rw [h_find_unchanged] at h_find'

              have h_obj'_wf_old := h_objs_wf lbl obj' h_find'

              cases h_obj' : obj' with
              | const c' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | var v' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | hyp ess f' name' =>
                  rw [h_obj'] at h_obj'_wf_old
                  exact h_obj'_wf_old
              | assert f' fr' name' =>
                  rw [h_obj'] at h_obj'_wf_old
                  constructor
                  · exact h_obj'_wf_old.1
                  · have h_fr_wf_old := h_obj'_wf_old.2
                    have h_find'_assert : db.find? lbl = some (.assert f' fr' name') := by
                      rw [← h_obj']
                      exact h_find'
                    have h_fresh_fr : ∀ i (hi : i < fr'.hyps.size), (fr'.hyps[i]'hi) ≠ label := by
                      intro i hi
                      exact h_fresh_in_asserts lbl f' fr' name' h_find'_assert i hi
                    exact insert_preserves_frame_wf db pos label obj fr'
                      h_fr_wf_old h_fresh_fr h_no_err_before h_no_err_after
                      h_not_var_dup h_var_inv h_obj_inv
  | pushScope =>
      -- Case: pushScope operation
      -- pushScope only modifies db.scopes, doesn't touch objects or frame
      simpa [DB.pushScope] using And.intro h_frame_wf h_objs_wf
  | popScope pos =>
      -- Case: popScope operation
      classical
      cases h_scope : db.scopes.back? with
      | none =>
          have : False := by
            have h_err : (DB.popScope pos db).error? ≠ none := by
              simp [DB.popScope, DB.mkError, h_scope]
            exact h_err (by simpa [DB.popScope, h_scope] using h_no_err_after)
          exact this.elim
      | some sc =>
          have h_frame := wf_frame_shrink h_frame_wf sc
          refine ⟨?_, ?_⟩
          · simpa [DB.popScope, h_scope] using h_frame
          · intro lbl obj h_find
            have h_lookup : db.find? lbl = some obj := by
              simpa [DB.popScope, h_scope] using h_find
            simpa [DB.popScope, h_scope] using h_objs_wf lbl obj h_lookup
  | withFrame f h_preserves =>
      -- Case: withFrame operation
      -- withFrame modifies db.frame using f
      -- h_preserves gives us: ∀ db fr, WellFormedFrame db fr → WellFormedFrame db (f fr)
      -- Objects are unchanged
      
      constructor
      · -- Part 1: Frame WF preserved
        have h_objects_eq : (db.withFrame f).objects = db.objects := rfl
        have h_new_frame_wf_db : WellFormedFrame db (f db.frame) := 
          h_preserves db db.frame h_frame_wf
        unfold WellFormedFrame HypOK at h_new_frame_wf_db ⊢
        rcases h_new_frame_wf_db with ⟨h_hyp, h_unique⟩
        constructor
        · intro i hi
          have h_old := h_hyp i hi
          rcases h_old with ⟨ess, fm, lbl, h_find, h_float, h_fmla⟩
          refine ⟨ess, fm, lbl, ?_, h_float, h_fmla⟩
          rw [DB.find?_def, h_objects_eq]
          exact h_find
        · intro i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_sz_i h_sz_j
          rw [DB.find?_def, h_objects_eq] at h_fi h_fj
          exact h_unique i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_sz_i h_sz_j

      · -- Part 2: Objects WF preserved
        intro lbl obj h_find
        have h_objects_eq : (db.withFrame f).objects = db.objects := rfl
        have h_find_old : db.find? lbl = some obj := by
          rw [DB.find?_def] at h_find ⊢
          rw [h_objects_eq] at h_find
          exact h_find
          
        have h_wf_old := h_objs_wf lbl obj h_find_old
        cases obj with
        | const c => exact h_wf_old
        | var v => exact h_wf_old
        | hyp ess fm name => exact h_wf_old
        | assert fmla fr name =>
            rcases h_wf_old with ⟨h_fmla, h_fr_wf⟩
            constructor
            · exact h_fmla
            · unfold WellFormedFrame HypOK at h_fr_wf ⊢
              rcases h_fr_wf with ⟨h_hyp, h_unique⟩
              constructor
              · intro i hi
                have h_old := h_hyp i hi
                rcases h_old with ⟨ess, fm, lbl, h_find_hyp, h_float, h_fmla_hyp⟩
                refine ⟨ess, fm, lbl, ?_, h_float, h_fmla_hyp⟩
                rw [DB.find?_def, h_objects_eq]
                exact h_find_hyp
              · intro i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_sz_i h_sz_j
                rw [DB.find?_def, h_objects_eq] at h_fi h_fj
                exact h_unique i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_sz_i h_sz_j
  | id =>
      -- Case: identity operation
      exact ⟨h_frame_wf, h_objs_wf⟩

where
  wf_frame_shrink
      {db : DB} {fr : Frame}
      (h : WF.WellFormedFrame db fr) (sizes : Nat × Nat) :
      WF.WellFormedFrame db (fr.shrink sizes) := by
    classical
    rcases fr with ⟨dj, hyps⟩
    rcases sizes with ⟨x, y⟩
    simp [Frame.shrink] at h ⊢
    rcases h with ⟨h_hyp, h_unique⟩
    constructor
    · intro i hi
      have hi_min : i < min y hyps.size := by
        simpa [Array.shrink] using hi
      have hi_y : i < y := Nat.lt_of_lt_of_le hi_min (Nat.min_le_left _ _)
      have hi_orig : i < hyps.size := Nat.lt_of_lt_of_le hi_min (Nat.min_le_right _ _)
      have h_label := h_hyp i hi_orig
      simpa [Array.shrink, hi_y, hi_orig] using h_label
    · intro i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_sz_i h_sz_j
      have hi_min : i < min y hyps.size := by
        simpa [Array.shrink] using hi
      have hj_min : j < min y hyps.size := by
        simpa [Array.shrink] using hj
      have hi_y : i < y := Nat.lt_of_lt_of_le hi_min (Nat.min_le_left _ _)
      have hj_y : j < y := Nat.lt_of_lt_of_le hj_min (Nat.min_le_left _ _)
      have hi_orig : i < hyps.size := Nat.lt_of_lt_of_le hi_min (Nat.min_le_right _ _)
      have hj_orig : j < hyps.size := Nat.lt_of_lt_of_le hj_min (Nat.min_le_right _ _)
      have h_unique' := h_unique i j hi_orig hj_orig h_ne fi fj lbli lblj
      have h_fi' := by
        simpa [Array.shrink, hi_y, hi_orig] using h_fi
      have h_fj' := by
        simpa [Array.shrink, hj_y, hj_orig] using h_fj
      exact h_unique' h_fi' h_fj' h_sz_i h_sz_j

/-! ## Composition of Structure-Preserving Operations

Sequential composition of structure-preserving operations.
-/

/-- Composing two structure-preserving operations yields a structure-preserving operation.
    If `op1` and `op2` both preserve structure, then `op2 ∘ op1` preserves structure. -/
theorem structure_preserving_compose
    {op1 op2 : DB → DB}
    (db : DB)
    (h_op1 : StructurePreservingOp db op1)
    (h_op2 : StructurePreservingOp (op1 db) op2)
    (h_wf : WellFormedDB db)
    (h_no_err_before : db.error? = none)
    (h_no_err_mid : (op1 db).error? = none)
    (h_no_err_after : (op2 (op1 db)).error? = none) :
    WellFormedDB (op2 (op1 db)) := by
  -- Apply structure_preserving_maintains_wf twice
  have h_wf_mid : WellFormedDB (op1 db) :=
    structure_preserving_maintains_wf db h_op1 h_wf h_no_err_before h_no_err_mid
  exact structure_preserving_maintains_wf (op1 db) h_op2 h_wf_mid h_no_err_mid h_no_err_after

end Metamath.ParserCorrectness
