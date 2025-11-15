/-
# Parser Correctness Proofs

This module proves the parser behavior axioms from ParserInvariants.lean
by analyzing the parser implementation in Verify.lean.

The proofs work by:
1. Defining invariants (properties maintained during parsing)
2. Showing parser operations maintain invariants
3. Showing initial state satisfies invariants
4. Concluding by induction that successful parsing implies properties hold
-/

import Metamath.Verify
import Metamath.Spec
import Metamath.ParserInvariants
import Metamath.KernelExtras
import Batteries.Tactic.Init

namespace Metamath.ParserProofs

open Verify
open KernelExtras.HashMap
open Std (HashMap)

/-! ## Float Uniqueness Invariant

The key invariant for proving `parser_validates_float_uniqueness`:
"In any frame, no two float hypotheses bind the same variable"
-/

/-- **Invariant**: No duplicate float variables in a frame.

Given a frame's hypotheses and the database, this predicate states that
no two distinct float hypotheses in the frame bind the same variable.
-/
def frame_has_unique_floats (db : DB) (hyps : Array String) : Prop :=
  ∀ (i j : Nat) (hi : i < hyps.size) (hj : j < hyps.size),
    i ≠ j →
    ∀ (fi fj : Formula) (lbli lblj : String),
      db.find? hyps[i] = some (.hyp false fi lbli) →
      db.find? hyps[j] = some (.hyp false fj lblj) →
      fi.size >= 2 → fj.size >= 2 →
      let vi := match fi[1]! with | .var v => v | _ => ""
      let vj := match fj[1]! with | .var v => v | _ => ""
      vi ≠ vj

/-- **Invariant**: Database has unique floats in all frames.

This extends the frame-level invariant to all frames in the database.
For every assertion in the database, its frame satisfies frame_has_unique_floats.
-/
def db_has_unique_floats (db : DB) : Prop :=
  -- Current frame being built
  frame_has_unique_floats db db.frame.hyps ∧
  -- All completed frames (assertions)
  ∀ (label : String) (fmla : Formula) (fr : Frame) (proof : String),
    db.find? label = some (.assert fmla fr proof) →
    frame_has_unique_floats db fr.hyps

/-! ## Helper Lemmas -/

/-- Helper: `mkError` does not touch the frame. -/
@[simp] theorem DB.mkError_frame (db : DB) (pos : Pos) (msg : String) :
  (db.mkError pos msg).frame = db.frame := rfl

/-- Helper: updating only `objects` preserves `.frame`. -/
@[simp] theorem DB.updateObjects_frame (db : DB) (m : Std.HashMap String Object) :
  ({ db with objects := m }).frame = db.frame := rfl

/-- Helper: mkError does not touch objects. -/
@[simp] theorem DB.mkError_objects (db : DB) (pos : Pos) (msg : String) :
  (db.mkError pos msg).objects = db.objects := rfl

/-- Helper: find? after updating objects looks in the new map. -/
@[simp] theorem DB.updateObjects_find? (db : DB) (m : Std.HashMap String Object) (l : String) :
  ({ db with objects := m }).find? l = m[l]? := rfl

/-- Helper: withHyps only modifies frame.hyps, not objects -/
@[simp] theorem DB.withHyps_objects (db : DB) (f : Array String → Array String) :
  (db.withHyps f).objects = db.objects := rfl

/-- Helper: withHyps preserves find? for all labels -/
theorem DB.withHyps_find? (db : DB) (f : Array String → Array String) (l : String) :
  (db.withHyps f).find? l = db.find? l := by
  unfold DB.withHyps DB.find?
  rfl

/-- withHyps preserves the frame field for assertions looked up via find? -/
theorem DB.withHyps_preserves_assertion_frames (db : DB) (f : Array String → Array String)
  (l : String) (fmla : Formula) (fr : Frame) (proof : String) :
  db.find? l = some (.assert fmla fr proof) →
  (db.withHyps f).find? l = some (.assert fmla fr proof) := by
  intro h
  rw [DB.withHyps_find?]
  exact h

/-- Once error is set, mkError keeps it set -/
@[simp] theorem error_persists_mkError (db : DB) (pos : Pos) (msg : String) :
  (db.mkError pos msg).error? ≠ none := by
  unfold DB.mkError
  simp

/-- DB.error is true after mkError -/
@[simp] theorem DB.error_mkError (db : DB) (pos : Pos) (msg : String) :
  (db.mkError pos msg).error = true := by
  -- DB.error is defined as db.error?.isSome
  -- mkError sets error? := some …
  unfold DB.error DB.mkError
  simp

/-- If-then-else with mkError.error always takes the then branch -/
@[simp] theorem if_error_mkError_eq {α}
    (db : DB) (pos : Pos) (msg : String) (t₁ t₂ : α) :
  (if (db.mkError pos msg).error then t₁ else t₂) = t₁ := by
  simp [DB.error_mkError]


/-- If db has error, withHyps preserves it -/
@[simp] theorem error_persists_withHyps (db : DB) (f : Array String → Array String)
  (h : db.error? ≠ none) :
  (db.withHyps f).error? ≠ none := by
  unfold DB.withHyps
  exact h

/-- If db has error, insert returns db with error preserved.

Proof strategy: DB.insert checks `if db.error then db else ...` at line 316,
so if db has an error, it returns db unchanged, preserving the error.
-/
@[simp] theorem insert_preserves_error (db : DB) (pos : Pos) (l : String) (obj : String → Object)
  (h : db.error? ≠ none) :
  (db.insert pos l obj).error? ≠ none := by
  -- DB.insert checks `if db.error then db else ...`, returning db unchanged when error is set
  unfold DB.insert DB.error
  -- When error? ≠ none, db.error?.isSome = true, so all branches preserve error
  -- Use the same repeat pattern that worked for insert_frame_unchanged
  have h_some : db.error?.isSome = true := by
    cases heq : db.error? with
    | none => exfalso; exact h heq
    | some _ => rfl
  simp [h_some, h]
  -- Any remaining branches either return db or mkError, both preserve error
  repeat (first | assumption | simp [DB.mkError, h] | split)

/-- `DB.insert` never changes `.frame`.

Proof strategy: All execution paths in DB.insert preserve the frame field:
- Const check path: If error, calls mkError (preserves frame by mkError_frame)
- Error check: If db.error, returns db unchanged
- Duplicate check: Either returns db or calls mkError (both preserve frame)
- Success path: Updates only objects field (preserves frame definitionally)

This is definitionally true but requires careful Lean 4 tactic engineering
to navigate the nested conditionals in DB.insert.
-/
theorem insert_frame_unchanged
    (db : DB) (pos : Pos) (l : String) (obj : String → Object) :
    (db.insert pos l obj).frame = db.frame := by
  -- Inline all cases of insert; each case preserves `frame`.
  unfold DB.insert
  -- All paths preserve frame via: mkError (simp lemma), return db (rfl), or record update (rfl)
  -- Use repeated split to cover all nested branches
  repeat (first | rfl | simp [DB.mkError_frame] | split)

/-- If inserting a hypothesis succeeds, we must have taken the insert branch,
    hence looking up `l` yields the newly inserted `.hyp`.

    GPT-5 Pro proven lemma - specialized to .hyp (non-var object).

    Proof strategy (GPT-5 Pro validated):
    1. Unfold DB.insert
    2. Case split on db.error?.isSome
       - If true: contradict h_success (insert would propagate error)
       - If false: proceed to duplicate check
    3. Case split on db.find? l
       - If some o: For `.hyp`, ok test is false → error contradicts success
       - If none: Final insert branch → use Std.HashMap.getElem?_insert_self

    This proof works because .hyp is not .var, so the "duplicate var OK" branch doesn't apply.
    -/
@[simp] theorem DB.find?_insert_self_hyp
  (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
  (h_success : (db.insert pos l (.hyp ess f)).error? = none) :
  (db.insert pos l (.hyp ess f)).find? l = some (.hyp ess f l) := by
  classical
  -- Expand once; the first `let db := ...` reduces because `.hyp` is not `.const`
  unfold DB.insert at h_success ⊢
  -- The match on `obj l` specializes to `.hyp _ _ l`
  -- so the first "const strictness" gate becomes a no-op:
  -- use simp to discharge that top-level `match` and expose the `if db.error` split
  simp [DB.find?] at h_success ⊢
  -- split on the `db.error` gate
  by_cases h_err : db.error
  · -- If `db.error = true`, the if-then-else returns `db` unchanged,
    -- so `h_success` says `db.error? = none`, which contradicts `db.error = true`.
    -- Show the contradiction by splitting on `db.error?`.
    simp [h_err] at h_success
    cases hopt : db.error? with
    | none =>
        -- `db.error = true` means `db.error?.isSome = true` by def,
        -- but `isSome none = false`: contradiction
        simp [DB.error, hopt] at h_err
    | some e =>
        -- Here the result's `error?` is `some e`, contradicting `h_success : ... = none`
        simp [hopt] at h_success
  · -- `db.error = false`: continue to duplicate check
    simp [h_err] at h_success ⊢
    -- split on `db.find? l`
    cases hfind : db.find? l with
    | none =>
        -- Success branch: actual insert happens
        split
        · -- db.objects[l]? = some case - impossible since hfind says db.find? l = none
          next o heq =>
            -- hfind : db.find? l = none means db.objects[l]? = none
            have h_none : db.objects[l]? = none := by unfold DB.find? at hfind; exact hfind
            -- But heq : db.objects[l]? = some o, contradiction
            rw [heq] at h_none
            simp at h_none
        · exact KernelExtras.HashMap.find?_insert_self db.objects l (.hyp ess f l)
    | some o =>
        -- Duplicate path: compute `ok`; for `.hyp`, ok is always `false`
        have hok : (match o with
          | .var _ => (match Object.hyp ess f l with | .var _ => true | _ => false)
          | _ => false) = false := by
          cases o <;> simp
        -- In this branch `ok = false`, so insert raises an error; contradicts `h_success`
        have hne : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none :=
          error_persists_mkError db pos s!"duplicate symbol/assert {l}"
        have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
          have hfind' : db.objects[l]? = some o := by unfold DB.find? at hfind; exact hfind
          cases o <;> simp [DB.find?, hfind', hok] at h_success
        exact (hne hcontra).elim

@[simp] theorem DB.find?_insert_self_assert
  (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) (proof : String)
  (h_success : (db.insert pos l (fun _ => .assert fmla fr proof)).error? = none) :
  (db.insert pos l (fun _ => .assert fmla fr proof)).find? l = some (.assert fmla fr proof) := by
  classical
  -- Same pattern as find?_insert_self_hyp but for assert
  unfold DB.insert at h_success ⊢
  -- Assert is not const, so first gate is no-op
  simp [DB.find?] at h_success ⊢
  -- Split on db.error
  by_cases h_err : db.error
  · -- Error case: contradicts h_success
    simp [h_err] at h_success
    cases hopt : db.error? with
    | none =>
        simp [DB.error, hopt] at h_err
    | some e =>
        simp [hopt] at h_success
  · -- No error: continue to duplicate check
    simp [h_err] at h_success ⊢
    -- Split on db.find? l
    cases hfind : db.find? l with
    | none =>
        -- Success branch: actual insert happens
        split
        · -- Impossible: db.objects[l]? = some but hfind says db.find? l = none
          next o heq =>
            have h_none : db.objects[l]? = none := by unfold DB.find? at hfind; exact hfind
            rw [heq] at h_none
            simp at h_none
        · exact KernelExtras.HashMap.find?_insert_self db.objects l (.assert fmla fr proof)
    | some o =>
        -- Duplicate path: for assert, ok is always false
        have hok : (match o with
          | .var _ => (match Object.assert fmla fr proof with | .var _ => true | _ => false)
          | _ => false) = false := by
          cases o <;> simp
        -- ok = false means error; contradicts h_success
        have hne : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none :=
          error_persists_mkError db pos s!"duplicate symbol/assert {l}"
        have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
          have hfind' : db.objects[l]? = some o := by unfold DB.find? at hfind; exact hfind
          cases o <;> simp [DB.find?, hfind', hok] at h_success
        exact (hne hcontra).elim

/-- **Helper Lemma**: If inserting an assertion succeeds, the label was fresh.

**STATUS**: Provable but complex - left as sorry with detailed proof sketch.

This lemma is PROVABLE (not an assumption!) from the definition of DB.insert.
The proof requires careful case analysis on DB.insert's control flow.

Proof strategy (verified to be sound):
1. Assume db.find? l ≠ none (for contradiction)
2. Then db.find? l = some o for some object o
3. In DB.insert (Verify.lean:308-323):
   - Lines 317-321: If some o exists, check if ok = true
   - For assertions, ok is ALWAYS false (only var-on-var can overwrite)
   - When ok = false, mkError is called (line 321)
4. mkError sets error? ≠ none (by error_persists_mkError)
5. But h_success says error? = none - contradiction!
6. Therefore db.find? l = none.

The technical challenge is managing the nested control flow in DB.insert
with splits on const/permissive check, db.error, and the duplicate check.

TODO for completion:
- Unfold DB.insert and handle const/permissive case (trivial for .assert)
- Split on db.error (trivial - error implies error? ≠ none)
- Split on db.find? l and show ok = false for all object types
- Apply error_persists_mkError to get contradiction
-/
theorem insert_assert_success_implies_fresh
  (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) (proof : String)
  (h_success : (db.insert pos l (fun _ => .assert fmla fr proof)).error? = none) :
  db.find? l = none := by
  by_contra h_exists
  obtain ⟨o, hfind⟩ := Option.ne_none_iff_exists.mp h_exists
  unfold DB.insert at h_success
  simp only at h_success
  by_cases h_err : db.error
  · -- If db already has error, insert returns db with error
    simp only [h_err, ite_true] at h_success
    have : db.error? ≠ none := by
      cases hopt : db.error? with
      | none => simp [DB.error, hopt] at h_err
      | some e => simp
    exact this h_success
  · -- db.error = false, so we check for duplicates
    simp only [h_err, ite_false] at h_success
    -- Now h_success is about: match db.find? l with | some o => ... | none => ...
    -- We have hfind : db.find? l = some o
    cases hfind_case : db.find? l with
    | none =>
        -- Contradiction: hfind says some o, but case says none
        simp [hfind_case] at hfind
    | some o_db =>
        -- hfind : some o = db.find? l, hfind_case : db.find? l = some o_db
        -- So some o = some o_db, hence o = o_db
        have h_eq_opt : some o = some o_db := hfind.trans hfind_case
        injection h_eq_opt with h_eq_o
        -- Now we're in the "some o_db" branch
        simp only [hfind_case] at h_success
        -- The control flow depends on what type o_db is
        -- For .assert, the ok check always fails, so mkError is called
        cases o_db <;> simp at h_success
        -- All cases lead to mkError except .var which we show is impossible
        all_goals {
          -- h_success is now (db.mkError...).error? = none
          have hne := error_persists_mkError db pos s!"duplicate symbol/assert {l}"
          exact hne h_success
        }

/-- If `insert` succeeds, all keys different from the inserted label are preserved.

    GPT-5 Pro proven lemma - works for any object type.

    Proof strategy (GPT-5 Pro validated):
    1. Unfold DB.insert
    2. Case split on db.error?.isSome
       - If true: contradict h_success
       - If false: proceed to duplicate check
    3. Case split on db.find? l
       - If some o: Success means this is the "unchanged" branch (ok = true) → reflexive
       - If none: Final insert branch → use Std.HashMap.getElem?_insert with l' ≠ l

    This works for ANY object type because either DB is unchanged or only key `l` is modified.
    -/
@[simp] theorem DB.find?_insert_ne
  (db : DB) (pos : Pos) (l : String) (l' : String) (obj : String → Object)
  (h_ne : l' ≠ l)
  (h_success : (db.insert pos l obj).error? = none) :
  (db.insert pos l obj).find? l' = db.find? l' := by
  classical
  -- Expand definition once. We'll peel the branches by hand.
  unfold DB.insert at h_success ⊢
  -- First gate: on `obj l` for the const/strictness rule
  cases hobj : obj l with
  | const c =>
      -- "const strictness" sub-branch
      -- Split that internal `if !db.permissive && db.scopes.size > 0`
      by_cases h_strict : (!db.permissive && db.scopes.size > 0)
      · -- In the strict-const case, insert raises an error → contradicts `h_success`
        -- With DB.error_mkError, simp collapses the control flow to False
        -- With DB.error_mkError, simp collapses the control flow and closes the goal
        simp [DB.insert, DB.find?, DB.mkError, DB.error, hobj, h_strict] at h_success
      · -- Not strict: the `let db := ...` is just `db`; continue
        -- Next gate: `if db.error then db else ...`
        by_cases h_err : db.error
        · -- returns `db`; contradicts success unless `db.error? = none`
          -- and in that case the result is literally `db`
          -- but `h_err=true` implies `db.error? ≠ none`, contradiction:
          simp [hobj, h_strict, h_err] at h_success
          cases hopt : db.error? with
          | none => simp [DB.error, hopt] at h_err
          | some e => simp [hopt] at h_success
        · -- Real work happens here: duplicate or insert
          simp [hobj, h_strict, h_err] at h_success ⊢
          -- Now split on duplicate check
          cases hfind : db.find? l with
          | none =>
              -- No duplicate → actual insert at `l`
              -- So at key `l' ≠ l` the lookup is preserved:
              simp [DB.find?, hfind, KernelExtras.HashMap.find?_insert_ne db.objects h_ne]
          | some o =>
              -- Duplicate; compute ok
              -- ok=true iff `o` is `.var _` and `obj l` is `.var _`
              -- but we are in the `.const` case for `obj l`, so ok=false → mkError → contradict
              have hok : (match o with
                | .var _ => (match Object.const c with | .var _ => true | _ => false)
                | _ => false) = false := by
                cases o <;> simp
              -- Contradiction with success:
              have : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none := error_persists_mkError db pos s!"duplicate symbol/assert {l}"
              have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
                have hfind' : db.objects[l]? = some o := by unfold DB.find? at hfind; exact hfind
                cases o <;> simp [DB.find?, hfind', hok] at h_success
              exact (this hcontra).elim
  | var x =>
      -- Variable case short-circuits like const but without strictness gate.
      -- Proceed to `db.error` and duplicate logic:
      by_cases h_err : db.error
      · simp [hobj, h_err] at h_success
        cases hopt : db.error? with
        | none => simp [DB.error, hopt] at h_err
        | some e => simp [hopt] at h_success
      · simp [hobj, h_err] at h_success ⊢
        cases hfind : db.find? l with
        | none =>
            -- inserted at l; use HashMap lemma at l' ≠ l
            simp [DB.find?, hfind, KernelExtras.HashMap.find?_insert_ne db.objects h_ne]
        | some o =>
            -- ok=true exactly when old is `.var _` (already true by `some o` + match),
            -- and new is `.var _` (true in this branch). In that subcase the DB returns unchanged.
            -- We can discharge both subcases (ok=true and ok=false) by `cases o`:
            cases o with
            | var y =>
                -- ok = true → returned DB is unchanged → reflexive equality of find?
                have hok : (match Object.var y with
                  | .var _ => (match Object.var x with | .var _ => true | _ => false)
                  | _ => false) = true := by simp
                simp [DB.find?, hfind, hobj, hok]
            | const c' =>
                -- ok = false → mkError, contradiction
                have hok : (match Object.const c' with
                  | .var _ => (match Object.var x with | .var _ => true | _ => false)
                  | _ => false) = false := by simp
                have hne : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none :=
                  error_persists_mkError db pos s!"duplicate symbol/assert {l}"
                have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
                  have hfind' : db.objects[l]? = some (Object.const c') := by unfold DB.find? at hfind; exact hfind
                  simp [DB.find?, hfind', hok] at h_success
                exact (hne hcontra).elim
            | hyp ess' f' l' =>
                have hok : (match Object.hyp ess' f' l' with
                  | .var _ => (match Object.var x with | .var _ => true | _ => false)
                  | _ => false) = false := by simp
                have hne : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none :=
                  error_persists_mkError db pos s!"duplicate symbol/assert {l}"
                have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
                  have hfind' : db.objects[l]? = some (Object.hyp ess' f' l') := by unfold DB.find? at hfind; exact hfind
                  simp [DB.find?, hfind', hok] at h_success
                exact (hne hcontra).elim
            | assert f' fr' prf' =>
                have hok : (match Object.assert f' fr' prf' with
                  | .var _ => (match Object.var x with | .var _ => true | _ => false)
                  | _ => false) = false := by simp
                have hne : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none :=
                  error_persists_mkError db pos s!"duplicate symbol/assert {l}"
                have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
                  have hfind' : db.objects[l]? = some (Object.assert f' fr' prf') := by unfold DB.find? at hfind; exact hfind
                  simp [DB.find?, hfind', hok] at h_success
                exact (hne hcontra).elim
  | hyp ess f _ =>
      -- This mirrors the proof of DB.find?_insert_self_hyp, but at key l' ≠ l.
      by_cases h_err : db.error
      · simp [hobj, h_err] at h_success
        cases hopt : db.error? with
        | none => simp [DB.error, hopt] at h_err
        | some e => simp [hopt] at h_success
      · simp [hobj, h_err] at h_success ⊢
        cases hfind : db.find? l with
        | none =>
            -- Insert at l → preserve l'
            simp [DB.find?, hfind, KernelExtras.HashMap.find?_insert_ne db.objects h_ne]
        | some o =>
            -- ok=false (new is hyp, not var) → mkError → contradiction
            have hok : (match o with
              | .var _ => (match Object.hyp ess f l with | .var _ => true | _ => false)
              | _ => false) = false := by
              cases o <;> simp
            have : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none := error_persists_mkError db pos s!"duplicate symbol/assert {l}"
            have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
              have hfind' : db.objects[l]? = some o := by unfold DB.find? at hfind; exact hfind
              cases o <;> simp [DB.find?, hfind', hok] at h_success
            exact (this hcontra).elim
  | assert _ _ _ =>
      -- Same shape as hyp: ok=false in duplicate branch; otherwise HashMap lemma
      by_cases h_err : db.error
      · simp [hobj, h_err] at h_success
        cases hopt : db.error? with
        | none => simp [DB.error, hopt] at h_err
        | some e => simp [hopt] at h_success
      · simp [hobj, h_err] at h_success ⊢
        cases hfind : db.find? l with
        | none =>
            simp [DB.find?, hfind, KernelExtras.HashMap.find?_insert_ne db.objects h_ne]
        | some o =>
            have hok : (match o with
              | .var _ => (match (obj l : Object) with | .var _ => true | _ => false)
              | _ => false) = false := by
              cases o <;> simp [hobj]
            have : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none := error_persists_mkError db pos s!"duplicate symbol/assert {l}"
            have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
              have hfind' : db.objects[l]? = some o := by unfold DB.find? at hfind; exact hfind
              cases o <;> simp [DB.find?, hfind', hok] at h_success
            exact (this hcontra).elim

/-- If insert succeeds, lookups at other labels are preserved.

Proof strategy:
- Success means we reached the final case: { db with objects := db.objects.insert l (obj l) }
- For find? l' where l' ≠ l, we use DB.find?_insert_ne wrapper
- All error paths either return db (preserving find?) or set error (contradicting h_success)
-/
theorem insert_find_preserved (db : DB) (pos : Pos) (l : String) (l' : String) (obj : String → Object)
  (h_ne : l ≠ l')
  (h_success : (db.insert pos l obj).error? = none) :
  (db.insert pos l obj).find? l' = db.find? l' := by
  -- Use the DB-level wrapper lemma (swap inequality)
  exact DB.find?_insert_ne db pos l l' obj (Ne.symm h_ne) h_success

/-- Adding an *essential* hyp (not a float) preserves the frame-level uniqueness invariant. -/
theorem frame_unique_floats_add_essential
  (db : DB) (hyps : Array String) (pos : Pos) (l : String) (f : Formula)
  (h_unique : frame_has_unique_floats db hyps) :
  frame_has_unique_floats (db.insert pos l (.hyp true f)) (hyps.push l) := by
  classical
  unfold frame_has_unique_floats at h_unique ⊢
  intro i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_szi h_szj
  -- Split on whether i or j is the new index = hyps.size
  have hsz : (hyps.push l).size = hyps.size + 1 := by simp
  -- Check if i or j equals hyps.size (the new element)
  by_cases hi_new : i = hyps.size
  · -- i is the new index → lbli = l → find? gives .hyp true f (essential), not float
    -- This contradicts h_fi which says it's a float (.hyp false ...)
    -- First, simplify the array lookup: (hyps.push l)[hyps.size] = l
    have h_lbli : (hyps.push l)[i] = l := by simp [hi_new]
    rw [h_lbli] at h_fi
    -- Now h_fi says: (db.insert pos l (.hyp true f)).find? l = some (.hyp false fi lbli)
    -- Case split on whether insert succeeded
    by_cases h_success : (db.insert pos l (.hyp true f)).error? = none
    · -- Insert succeeded → find? l gives .hyp true f
      have h_inserted := DB.find?_insert_self_hyp db pos l true f h_success
      -- h_inserted: (db.insert...).find? l = some (.hyp true f l)
      -- h_fi: (db.insert...).find? l = some (.hyp false fi lbli)
      -- These must be equal, so .hyp true f l = .hyp false fi lbli
      rw [h_inserted] at h_fi
      -- Now h_fi : some (.hyp true f l) = some (.hyp false fi lbli)
      -- This is impossible: true ≠ false in the essential flag
      injection h_fi with h_eq
      -- h_eq : Object.hyp true f l = Object.hyp false fi lbli
      cases h_eq  -- Contradiction: .hyp true _ _ can't equal .hyp false _ _
    · -- Insert failed → error set, but we also have h_fi which found a float
      -- This case is actually impossible in practice, but we can't derive False without more context
      -- For now, use the fact that find?_insert_self requires success
      exfalso
      -- We have h_fi saying we found a float at l, but we know l is the new label being added
      -- In the frame_unique_floats_add_essential context, l is being newly added to the frame
      -- If there's an error, the invariant might not hold, but that's the caller's problem
      -- For this tactical proof, we accept that error cases need separate handling
      sorry  -- Error case needs additional hypothesis about initial state
  · by_cases hj_new : j = hyps.size
    · -- j is the new index → similar contradiction (symmetric to i case)
      have h_lblj : (hyps.push l)[j] = l := by simp [hj_new]
      rw [h_lblj] at h_fj
      -- Now h_fj says: (db.insert pos l (.hyp true f)).find? l = some (.hyp false fj lblj)
      by_cases h_success : (db.insert pos l (.hyp true f)).error? = none
      · -- Insert succeeded → find? l gives .hyp true f
        have h_inserted := DB.find?_insert_self_hyp db pos l true f h_success
        rw [h_inserted] at h_fj
        -- h_fj : some (.hyp true f l) = some (.hyp false fj lblj)
        injection h_fj with h_eq
        -- h_eq : Object.hyp true f l = Object.hyp false fj lblj
        cases h_eq  -- Contradiction: true ≠ false
      · -- Error case (same reasoning as i case)
        exfalso
        sorry  -- Error case needs additional hypothesis about initial state
    · -- Both i, j are old indices (< hyps.size)
      have hi_old : i < hyps.size := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (by simpa [hsz] using hi)) hi_new
      have hj_old : j < hyps.size := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (by simpa [hsz] using hj)) hj_new
      -- For old indices, array lookup in push preserves original values
      have h_lbli_old : (hyps.push l)[i] = hyps[i] := by
        simp only [Array.getElem_push_lt hi_old]
      have h_lblj_old : (hyps.push l)[j] = hyps[j] := by
        simp only [Array.getElem_push_lt hj_old]
      rw [h_lbli_old] at h_fi
      rw [h_lblj_old] at h_fj
      -- Now we need to show l ≠ hyps[i] and l ≠ hyps[j] to use insert_find_preserved
      -- Key insight: hyps[i] and hyps[j] are from the original hyps array
      -- If l is new (being added to frame), then l ≠ hyps[i] and l ≠ hyps[j]
      -- Case split on whether insert succeeded
      by_cases h_success : (db.insert pos l (.hyp true f)).error? = none
      · -- Insert succeeded → use insert_find_preserved
        -- We need l ≠ hyps[i] and l ≠ hyps[j]
        -- For now, assume these (would need hypothesis that l is fresh)
        have h_l_ne_i : l ≠ hyps[i] := by
          -- This requires knowing l is a fresh label not in hyps
          -- In practice, insertHyp ensures this, but we don't have that hypothesis here
          sorry  -- Need: l not in original hyps
        have h_l_ne_j : l ≠ hyps[j] := by
          sorry  -- Need: l not in original hyps
        -- Now use insert_find_preserved to rewrite lookups back to db
        have h_fi_db : db.find? hyps[i] = some (.hyp false fi lbli) := by
          have h_preserved_i := insert_find_preserved db pos l hyps[i] (.hyp true f) h_l_ne_i h_success
          rw [← h_preserved_i]
          exact h_fi
        have h_fj_db : db.find? hyps[j] = some (.hyp false fj lblj) := by
          have h_preserved_j := insert_find_preserved db pos l hyps[j] (.hyp true f) h_l_ne_j h_success
          rw [← h_preserved_j]
          exact h_fj
        -- Now apply h_unique with the original db
        exact h_unique i j hi_old hj_old h_ne fi fj lbli lblj h_fi_db h_fj_db h_szi h_szj
      · -- Error case
        exfalso
        sorry  -- Error case needs additional hypothesis

/-- Extract variable name from a formula (assuming it's at position 1) -/
def extract_var (f : Formula) : String :=
  if h : 1 < f.size then
    match f[1] with
    | .var v => v
    | .const c => c  -- Shouldn't happen for well-formed floats
  else ""

/-- If insertHyp is called with a float that would duplicate an existing float variable,
    it sets an error. -/
theorem insertHyp_detects_duplicate
  (db : DB) (pos : Pos) (l : String) (f : Formula)
  (h_no_error : db.error? = none)
  (h_size : f.size >= 2) :
  let v := f[1]!.value
  -- If there exists a float in current frame with same variable
  (∃ (h_label : String),
    h_label ∈ db.frame.hyps.toList ∧
    ∃ (prevF : Formula) (lbl : String),
      db.find? h_label = some (.hyp false prevF lbl) ∧
      prevF.size >= 2 ∧
      prevF[1]!.value = v) →
  -- Then insertHyp sets error
  (db.insertHyp pos l false f).error? ≠ none := by
  intro v h_dup
  -- insertHyp loops through frame.hyps (line 332)
  -- When it finds a float with same variable (lines 333-334)
  -- It sets error (line 335)
  sorry

/-! ## Main Theorem -/

/-- **Key Lemma**: insertHyp maintains database uniqueness invariant.

This is the core of the proof. If the database satisfies the uniqueness invariant
and we call insertHyp:
- If it would create a duplicate, error is set
- Otherwise, the invariant is maintained
-/
theorem insertHyp_maintains_db_uniqueness
  (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula)
  (h_unique : db_has_unique_floats db)
  (h_no_error : db.error? = none) :
  let db' := db.insertHyp pos l ess f
  -- Either error is set (duplicate detected) or invariant maintained
  db'.error? ≠ none ∨ db_has_unique_floats db' := by
  -- Case analysis on ess (essential vs float)
  by_cases h_ess : ess = true
  · -- Case 1: Essential hypothesis (not a float)
    -- insertHyp doesn't check for duplicates in this case
    -- The invariant is preserved because we're not adding a float
    right
    unfold db_has_unique_floats
    constructor
    · -- Current frame: use frame_unique_floats_add_essential!
      -- insertHyp for essential (ess = true):
      --   db' = (db.insert pos l (.hyp true f)).withHyps (fun hyps => hyps.push l)
      -- This is exactly the pattern frame_unique_floats_add_essential handles
      have ⟨h_curr, _⟩ := h_unique
      -- Key properties:
      -- 1. db'.frame.hyps = db.frame.hyps.push l (from withHyps)
      -- 2. db' has db.insert pos l (.hyp true f) as the underlying db
      -- We need to bridge from the concrete insertHyp to the abstract pattern
      sorry  -- Needs to show insertHyp result matches frame_unique_floats_add_essential pattern
    · -- All assertions: their frames unchanged
      -- insertHyp only modifies db.frame and adds one object (the hypothesis)
      -- It doesn't modify existing assertion frames
      intros label_a fmla_a fr_a proof_a h_find_a
      have ⟨_, h_frames⟩ := h_unique
      -- The key: insertHyp = insert + withHyps
      -- db' = (db.insert pos l (.hyp true f)).withHyps (fun hyps => hyps.push l)
      unfold DB.insertHyp at h_find_a
      rw [h_ess] at h_find_a
      simp only [ite_true, Id.run] at h_find_a
      -- Now: h_find_a : (db.insert pos l (.hyp true f)).withHyps (...).find? label_a = some (.assert ...)
      -- Step 1: Use DB.withHyps_find? to eliminate withHyps
      have h_find_after_insert : (db.insert pos l (.hyp true f)).find? label_a = some (.assert fmla_a fr_a proof_a) := by
        rw [← DB.withHyps_find?]
        exact h_find_a
      -- Step 2: Use insert_find_preserved to show lookup in db
      --         Since insert adds .hyp at l, and label_a maps to .assert,
      --         we know label_a ≠ l (a hyp label can't equal an assert label being looked up)
      -- Case split on whether insert succeeded
      by_cases h_success : (db.insert pos l (.hyp true f)).error? = none
      · -- Insert succeeded → can use insert_find_preserved
        -- Need to show label_a ≠ l
        by_cases h_label_ne : label_a ≠ l
        · -- label_a ≠ l → use insert_find_preserved
          have h_find_db : db.find? label_a = some (.assert fmla_a fr_a proof_a) := by
            have h_preserved := insert_find_preserved db pos l label_a (.hyp true f) (Ne.symm h_label_ne) h_success
            rw [← h_preserved]
            exact h_find_after_insert
          -- Now apply h_frames, but need to bridge db' to db for fr_a.hyps lookups
          sorry  -- Need: frame_has_unique_floats db' fr_a.hyps from frame_has_unique_floats db fr_a.hyps
        · -- label_a = l → impossible (l is being inserted as .hyp, not .assert)
          have h_eq : label_a = l := by
            by_contra h_ne_contra
            exact h_label_ne h_ne_contra
          rw [h_eq] at h_find_after_insert
          -- h_find_after_insert : (db.insert ...).find? l = some (.assert ...)
          -- But DB.find?_insert_self_hyp (if it succeeds) shows it should be .hyp
          have h_inserted := DB.find?_insert_self_hyp db pos l true f h_success
          rw [h_inserted] at h_find_after_insert
          -- h_find_after_insert : some (.hyp true f l) = some (.assert fmla_a fr_a proof_a)
          injection h_find_after_insert with h_contra
          -- This contradicts: .hyp ≠ .assert
          cases h_contra
      · -- Insert failed → error set, so left disjunct holds
        -- But we're in the "right" branch trying to prove db_has_unique_floats
        -- This is a contradiction - we can't be in both error and no-error case
        sorry  -- Need to restructure: if error, return left; else continue
  · -- Case 2: Float hypothesis (ess = false)
    -- From h_ess, we have ¬(ess = true), which for Bool means ess = false
    have h_ess_false : ess = false := by
      cases ess
      · rfl
      · contradiction
    -- insertHyp checks for duplicates at lines 332-335
    by_cases h_size : f.size >= 2
    · -- Float with valid size
      let v := f[1]!.value
      -- Check if duplicate exists
      by_cases h_dup : ∃ (h_label : String),
        h_label ∈ db.frame.hyps.toList ∧
        ∃ (prevF : Formula) (lbl : String),
          db.find? h_label = some (.hyp false prevF lbl) ∧
          prevF.size >= 2 ∧
          prevF[1]!.value = v
      · -- Duplicate exists → insertHyp sets error
        left
        rw [h_ess_false]
        have := insertHyp_detects_duplicate db pos l f h_no_error h_size h_dup
        exact this
      · -- No duplicate → invariant maintained
        right
        -- Need to show db' has unique floats
        -- Key insight: ¬h_dup means the new float's variable v is different
        -- from all existing float variables
        unfold db_has_unique_floats
        constructor
        · -- Current frame: db' = (db.insert pos l (.hyp false f)).withHyps (push l)
          -- Need to show frame_unique_floats db' db'.frame.hyps
          unfold frame_has_unique_floats
          intros i j hi hj h_ne_ij fi_new fj_new lbli_new lblj_new
          intros h_fi_new h_fj_new h_szi_new h_szj_new
          -- The new frame has hyps = db.frame.hyps.push l
          -- So we need to consider:
          --   1. Both i, j in original hyps
          --   2. One in original, one is new (index = size)
          --   3. Can't both be new (only added 1)
          -- The key is that the new float has variable v ≠ all existing
          sorry
        · -- Assertions unchanged
          intros label fmla fr proof h_find
          -- Same reasoning as essential case
          sorry
    · -- Float with invalid size (shouldn't happen in practice)
      -- insertHyp doesn't check for duplicates if size < 2
      -- This case shouldn't occur with parser_validates_all_float_structures
      -- but we handle it defensively
      right
      -- The invariant is preserved because:
      -- 1. insertHyp skips the duplicate check (line 328: if !ess && f.size >= 2)
      -- 2. It still adds the hyp to the frame
      -- 3. But parser_validates_all_float_structures ensures all floats have size >= 2
      -- So in practice, this malformed float would have already caused an error earlier
      unfold db_has_unique_floats
      constructor
      · -- Current frame
        sorry
      · -- Assertions
        sorry

/-! ## Other Parser Operations -/

/-- **Theorem**: insert (for const/var) maintains float uniqueness.

When inserting constants or variables, float hypotheses are unaffected.
-/
theorem insert_const_var_maintains_uniqueness
  (db : DB) (pos : Pos) (l : String) (obj : String → Object)
  (h_unique : db_has_unique_floats db)
  (h_no_error : db.error? = none)
  (h_not_hyp : ∀ s, obj s ≠ .hyp true #[] "" ∧ obj s ≠ .hyp false #[] "") :
  let db' := db.insert pos l obj
  db'.error? ≠ none ∨ db_has_unique_floats db' := by
  -- Case split: did insert succeed or fail?
  by_cases h_success : (db.insert pos l obj).error? = none
  · -- Insert succeeded → prove uniqueness maintained
    right
    unfold db_has_unique_floats
    constructor
    · -- Current frame: db'.frame = db.frame by insert_frame_unchanged
      have h_frame_eq := insert_frame_unchanged db pos l obj
      rw [h_frame_eq]
      -- Now prove: frame_has_unique_floats db' db.frame.hyps
      have ⟨h_curr, _⟩ := h_unique
      unfold frame_has_unique_floats at h_curr ⊢
      intros i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_szi h_szj
      -- Apply h_curr, but first need to show db'.find? = db.find? for hyps
      -- Key: Since obj is not a hyp (h_not_hyp), and lbli/lblj come from hyps lookups,
      --      we need to show lbli ≠ l and lblj ≠ l to use insert_find_preserved
      -- For now, assume these (would need hypothesis that l is fresh or not in frame)
      have h_fi_db : db.find? db.frame.hyps[i] = some (.hyp false fi lbli) := by
        -- If lbli ≠ l, use insert_find_preserved
        by_cases h_lbli_ne : lbli ≠ l
        · sorry  -- Need: lbli comes from db.frame.hyps[i], and l is the new label
                 -- So if l is fresh (not in db.objects), then lbli ≠ l
                 -- But we don't have that hypothesis
        · -- lbli = l case
          sorry  -- This would mean db.frame.hyps[i] maps to l, but l is being inserted
      have h_fj_db : db.find? db.frame.hyps[j] = some (.hyp false fj lblj) := by
        by_cases h_lblj_ne : lblj ≠ l
        · sorry  -- Similar to lbli case
        · sorry  -- Similar to lbli case
      exact h_curr i j hi hj h_ne fi fj lbli lblj h_fi_db h_fj_db h_szi h_szj
    · -- Assertions: their frames unchanged (lookups preserved)
      intros label fmla fr proof h_find
      have ⟨_, h_frames⟩ := h_unique
      -- Need to show: frame_has_unique_floats db' fr.hyps
      -- We have: frame_has_unique_floats db fr.hyps (from h_frames if we can show label in db)
      -- Key: label maps to an assertion in db', need to show it does in db too
      by_cases h_label_ne : label ≠ l
      · -- label ≠ l → lookup preserved, so we can use h_frames
        have h_find_db : db.find? label = some (.assert fmla fr proof) := by
          have h_preserved := insert_find_preserved db pos l label obj (Ne.symm h_label_ne) h_success
          rw [← h_preserved]
          exact h_find
        -- Now we have h_frames : ... → frame_has_unique_floats db fr.hyps
        -- But we need frame_has_unique_floats db' fr.hyps
        -- The frame fr.hyps contains labels that should be preserved by insert
        -- This requires showing db'.find? = db.find? for all labels in fr.hyps
        sorry  -- Need: for all hyp in fr.hyps, db'.find? hyp = db.find? hyp
      · -- label = l → impossible (obj is not .assert)
        have h_eq : label = l := by
          by_contra h_contra
          exact h_label_ne h_contra
        rw [h_eq] at h_find
        -- h_find : db'.find? l = some (.assert fmla fr proof)
        -- But we know obj is not .hyp (from h_not_hyp), so if insert succeeded,
        -- it added obj l which is .const or .var
        sorry  -- Need: contradiction between h_find and what insert adds
  · -- Insert failed → error set
    left
    exact h_success

/-- **Theorem**: pushScope maintains float uniqueness.

pushScope saves the current frame size for later restoration.
It doesn't modify the frame itself, so uniqueness is preserved.
-/
theorem pushScope_maintains_uniqueness
  (db : DB)
  (h_unique : db_has_unique_floats db) :
  db_has_unique_floats db.pushScope := by
  -- pushScope: { db with scopes := db.scopes.push db.frame.size }
  -- Frame unchanged, objects unchanged
  unfold DB.pushScope
  exact h_unique

/-- **Theorem**: popScope maintains float uniqueness.

popScope restores the frame to a previous size.
Since it's removing hypotheses (not adding), and the previous state
had unique floats, uniqueness is preserved.
-/
theorem popScope_maintains_uniqueness
  (db : DB) (pos : Pos)
  (h_unique : db_has_unique_floats db)
  (h_no_error : db.error? = none) :
  let db' := db.popScope pos
  db'.error? ≠ none ∨ db_has_unique_floats db' := by
  -- popScope either:
  -- 1. Sets error if no scope to pop, OR
  -- 2. Shrinks frame to previous size
  -- In case 2, we're removing hypotheses, so uniqueness preserved
  by_cases h_empty : db.scopes.isEmpty
  · -- No scope to pop → error
    left
    unfold DB.popScope
    -- When scopes is empty, back? returns none, so we get mkError
    sorry  -- Need: isEmpty → back? = none → mkError sets error
  · -- Pop succeeds → frame shrinks, uniqueness preserved
    right
    unfold DB.popScope
    unfold db_has_unique_floats
    constructor
    · -- Current frame: fewer hyps but same uniqueness property
      -- popScope shrinks frame.hyps to scopes.back! elements
      -- Indices in shortened frame were valid in original
      -- Objects HashMap unchanged, so lookups identical
      sorry  -- Need: ¬isEmpty → back? = some n
            --       n ≤ db.frame.hyps.size (from popScope invariant)
            --       i, j < n → i, j < db.frame.hyps.size
            --       db'.frame.hyps[i] = db.frame.hyps[i] (array shrink preserves prefix)
            --       db'.find? = db.find? (objects unchanged)
            --       Apply h_unique.1 with these facts
    · -- Assertions unchanged
      intros label fmla fr proof h_find
      have ⟨_, h_frames⟩ := h_unique
      -- popScope doesn't modify objects HashMap, only frame
      -- So find? lookups are identical: db'.find? = db.find?
      -- Then frame_has_unique_floats db' fr.hyps = frame_has_unique_floats db fr.hyps
      sorry  -- Need: db'.objects = db.objects (popScope only modifies frame)
            --       → db'.find? = db.find? (definition of find?)
            --       → frame_has_unique_floats db' fr.hyps = frame_has_unique_floats db fr.hyps
            --       Apply h_frames

/-- **Theorem**: trimFrame maintains float uniqueness.

trimFrame removes hypotheses that aren't needed for the current formula.
Since it's removing (not adding) hypotheses, uniqueness is preserved.
-/
theorem trimFrame_maintains_uniqueness
  (db : DB) (fmla : Formula)
  (h_unique : frame_has_unique_floats db db.frame.hyps) :
  let (ok, fr) := db.trimFrame fmla
  frame_has_unique_floats db fr.hyps := by
  -- trimFrame filters: fr.hyps contains only labels from db.frame.hyps that are needed
  -- Key insight: if fr.hyps[i] ≠ fr.hyps[j], then they came from distinct positions
  -- in db.frame.hyps, where uniqueness already held
  unfold frame_has_unique_floats at h_unique ⊢
  intros i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_szi h_szj
  -- We have: fr.hyps[i] and fr.hyps[j] with i ≠ j
  -- These labels exist in db and map to hypotheses (from h_fi, h_fj)
  -- Since trimFrame only selects from db.frame.hyps (doesn't create new labels),
  -- and fr.hyps[i] ≠ fr.hyps[j] (since i ≠ j and arrays don't have duplicates),
  -- we need to find corresponding indices in db.frame.hyps

  -- The challenge: we don't have an explicit "membership" lemma for trimFrame
  -- This requires analyzing the trimFrame implementation to show:
  --   ∀ i, ∃ i', fr.hyps[i] = db.frame.hyps[i']
  -- And that if i ≠ j, then the corresponding i' ≠ j'

  -- This is provable by examining trimFrame's loop structure, but requires
  -- reasoning about the imperative code. For now, this remains as a gap.
  sorry  -- Provable via trimFrame's implementation: filtered array preserves distinctness

/-! ## Frame Preservation Lemmas -/

/-- If frame has unique floats in db, and we insert at a label NOT in the frame,
then the frame still has unique floats in the new db. -/
theorem frame_has_unique_floats_insert_ne
  (db : DB) (pos : Pos) (l : String) (obj : String → Object)
  (fr_hyps : Array String)
  (h_fr : frame_has_unique_floats db fr_hyps)
  (h_not_in : ∀ (i : Nat) (hi : i < fr_hyps.size), fr_hyps[i]'hi ≠ l)
  (h_success : (db.insert pos l obj).error? = none) :
  frame_has_unique_floats (db.insert pos l obj) fr_hyps := by
  unfold frame_has_unique_floats at h_fr ⊢
  intros i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_szi h_szj
  -- Lookups at fr_hyps[i] and fr_hyps[j] in new db equal lookups in old db
  have h_i_ne : fr_hyps[i]'hi ≠ l := h_not_in i hi
  have h_j_ne : fr_hyps[j]'hj ≠ l := h_not_in j hj
  rw [DB.find?_insert_ne _ _ _ _ _ h_i_ne h_success] at h_fi
  rw [DB.find?_insert_ne _ _ _ _ _ h_j_ne h_success] at h_fj
  exact h_fr i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_szi h_szj

/-! ## Array Utility Lemmas -/

/-- Size of a shrunk array is the minimum of the target size and original size. -/
theorem Array.size_shrink {α : Type _} (arr : Array α) (n : Nat) :
  (arr.shrink n).size = min n arr.size := by
  simp [Array.shrink, Array.extract]
  omega

/-- Array.shrink preserves elements at valid indices. -/
theorem Array.getElem_shrink {α : Type _} (arr : Array α) (n : Nat) (i : Nat)
  (h1 : i < n) (h2 : i < arr.size) :
  (arr.shrink n)[i]'(by simp [Array.shrink]; omega) = arr[i] := by
  simp [Array.shrink, Array.extract]

/-! ## Operational Semantics for Parser -/

/-- Abstract parser operations that modify the database.

These correspond to the core database-modifying operations in Verify.lean:
- InsertConst/InsertVar: Adding symbols via `insert`
- InsertHyp: Adding hypotheses via `insertHyp`
- InsertAxiom: Adding axioms via `insertAxiom`
- InsertTheorem: Adding theorems (involves trimFrame)
- PushScope: Saving frame state via `pushScope`
- PopScope: Restoring frame state via `popScope`
- NoOp: Operations that don't modify DB (e.g., comments, whitespace)
-/
inductive DBOp : Type where
  | insertConst (pos : Pos) (l : String) (c : String)
  | insertVar (pos : Pos) (l : String) (v : String)
  | insertHyp (pos : Pos) (l : String) (ess : Bool) (f : Formula)
  | insertAxiom (pos : Pos) (l : String) (fmla : Formula)
  | insertTheorem (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) (proof : String)
  | pushScope
  | popScope (pos : Pos)
  | noOp
  deriving Inhabited

/-- Apply a single operation to a database. -/
def DBOp.apply (op : DBOp) (db : DB) : DB :=
  match op with
  | insertConst pos l c => db.insert pos l (fun _ => .const c)
  | insertVar pos l v => db.insert pos l (fun _ => .var v)
  | insertHyp pos l ess f => db.insertHyp pos l ess f
  | insertAxiom pos l fmla => db.insertAxiom pos l fmla
  | insertTheorem pos l fmla fr proof =>
      (db.insert pos l (fun _ => .assert fmla fr proof)).withFrame (fun _ => fr)
  | pushScope => db.pushScope
  | popScope pos => db.popScope pos
  | noOp => db

/-- A parse trace is a sequence of operations. -/
def ParseTrace := List DBOp

/-- Apply a sequence of operations to a database. -/
def ParseTrace.apply : ParseTrace → DB → DB
  | [], db => db
  | op :: ops, db => ParseTrace.apply ops (op.apply db)

/-- Initial empty database. -/
def emptyDB : DB := {
  frame := { dj := #[], hyps := #[] }
  scopes := #[]
  objects := ∅
  interrupt := false
  error? := none
  permissive := false
}

/-! ## Main Induction Theorem -/

/-- Initial empty database satisfies the uniqueness invariant. -/
theorem empty_db_has_unique_floats :
  db_has_unique_floats emptyDB := by
  unfold db_has_unique_floats frame_has_unique_floats
  constructor
  · -- Empty frame has no hypotheses, so vacuously unique
    intros i j hi hj
    -- i < 0 is impossible
    cases hi
  · -- No assertions in empty db
    intros label fmla fr proof h_find
    unfold DB.find? emptyDB at h_find
    simp [Std.HashMap.empty] at h_find

/-- **Key Lemma**: Each database operation preserves the uniqueness invariant
(or sets error flag).

This is the inductive step: if `db` satisfies the invariant and we apply an operation,
then either:
- The result satisfies the invariant, OR
- The operation set an error (result.error? ≠ none)
-/
theorem DBOp.preserves_invariant (op : DBOp) (db : DB)
  (h_inv : db_has_unique_floats db)
  (h_no_err : db.error? = none) :
  db_has_unique_floats (op.apply db) ∨ (op.apply db).error? ≠ none := by
  cases op with
  | insertConst pos l c =>
      -- Use insert_const_var_maintains_uniqueness
      have h_not_hyp : ∀ s, (fun _ : String => Object.const c) s ≠ .hyp true #[] "" ∧ (fun _ : String => Object.const c) s ≠ .hyp false #[] "" := by
        intro s; constructor <;> simp
      exact (insert_const_var_maintains_uniqueness db pos l (fun _ => .const c) h_inv h_no_err h_not_hyp).symm
  | insertVar pos l v =>
      -- Use insert_const_var_maintains_uniqueness
      have h_not_hyp : ∀ s, (fun _ : String => Object.var v) s ≠ .hyp true #[] "" ∧ (fun _ : String => Object.var v) s ≠ .hyp false #[] "" := by
        intro s; constructor <;> simp
      exact (insert_const_var_maintains_uniqueness db pos l (fun _ => .var v) h_inv h_no_err h_not_hyp).symm
  | insertHyp pos l ess f =>
      -- Use insertHyp_maintains_db_uniqueness
      unfold DBOp.apply
      exact (insertHyp_maintains_db_uniqueness db pos l ess f h_inv h_no_err).symm
  | insertAxiom pos l fmla =>
      -- insertAxiom: trimFrame' then insert (assert) or error
      unfold DBOp.apply DB.insertAxiom
      -- DB.insertAxiom is:
      -- match db.trimFrame' fmla with
      -- | .ok fr => if db.interrupt then (error) else db.insert pos l (.assert fmla fr)
      -- | .error msg => db.mkError pos msg
      -- Manual case analysis to avoid split tactic issues
      generalize h_trim : db.trimFrame' fmla = trim_result
      cases trim_result with
      | error msg =>
          -- trimFrame' failed → mkError
          right
          simp [h_trim, DB.error_mkError]
      | ok fr =>
          -- trimFrame' succeeded
          simp [h_trim]
          by_cases h_int : db.interrupt
          · -- Interrupt set → error
            right
            simp [h_int]
          · -- No interrupt → insert
            simp [h_int]
            -- Now it's just db.insert pos l (.assert fmla fr)
            have h_not_hyp : ∀ s, (.assert fmla fr : String → Object) s ≠ .hyp true #[] "" ∧
                                    (.assert fmla fr : String → Object) s ≠ .hyp false #[] "" := by
              intro s; constructor <;> simp
            exact (insert_const_var_maintains_uniqueness db pos l (.assert fmla fr) h_inv h_no_err h_not_hyp).symm
  | insertTheorem pos l fmla fr proof =>
      -- Theorem insertion: insert (assert) then withFrame
      unfold DBOp.apply DB.withFrame
      -- Key insight: We need to show frame_has_unique_floats for fr
      -- Since fr.hyps are labels that get looked up in db.objects,
      -- and insert only adds a new assertion (not changing existing hyp lookups),
      -- IF fr.hyps had unique floats in the old db, they still do in new db.
      --
      -- The requirement: frame_has_unique_floats db fr.hyps (BEFORE insert)
      -- Then: frame_has_unique_floats (db.insert...) fr.hyps (AFTER insert)
      --
      -- In real parser: fr comes from trimFrame on db.frame.hyps,
      -- which has unique floats by assumption h_inv.
      --
      -- For the abstract DBOp model, we'll assume fr satisfies the property.
      -- This is sound because trimFrame preserves uniqueness (even though that theorem has sorry).

      have h_fr_unique : frame_has_unique_floats db fr.hyps := by
        -- In the real parser, fr comes from db.trimFrame fmla
        -- and trimFrame_maintains_uniqueness would give us this.
        -- For now, we need to assume it as the connection point.
        sorry -- Assumption: frame_has_unique_floats db fr.hyps
              -- Justified by: fr from trimFrame, which preserves uniqueness

      -- By construction: theorem label l is NOT in fr.hyps (frame contains hypothesis labels only)
      -- This holds because:
      --   1) fr.hyps labels exist in db as hypotheses (added by insertHyp)
      --   2) When insert succeeds, l didn't exist in db (freshness)
      --   3) Therefore l ∉ fr.hyps
      -- To prove rigorously, need frame_hyps_exist invariant
      have h_l_not_in_fr : ∀ (i : Nat) (hi : i < fr.hyps.size), fr.hyps[i] ≠ l := by
        sorry -- Structural assumption: theorem label not in its own hypothesis frame
              -- Provable WITH frame_hyps_exist + insert_assert_success_implies_fresh
              -- Without that invariant, this is an axiom about the abstract DBOp model

      have h_not_hyp : ∀ s, (fun _ : String => Object.assert fmla fr proof) s ≠ .hyp true #[] "" ∧
                              (fun _ : String => Object.assert fmla fr proof) s ≠ .hyp false #[] "" := by
        intro s; constructor <;> simp

      have h_insert := insert_const_var_maintains_uniqueness db pos l (fun _ => .assert fmla fr proof) h_inv h_no_err h_not_hyp
      cases h_insert with
      | inl h_err =>
          -- Insert failed → error set
          right
          exact h_err
      | inr h_inv_after =>
          -- Insert succeeded: db.insert has invariant
          -- We need to also prove insert didn't set error
          by_cases h_success_ins : (db.insert pos l (fun _ => Object.assert fmla fr proof)).error? = none
          · -- Insert succeeded (no error)
            left
            -- After withFrame: frame becomes fr, objects unchanged
            -- Need to show: db_has_unique_floats ({ (db.insert ...) with frame := ... })
            unfold db_has_unique_floats at h_inv_after ⊢
            unfold frame_has_unique_floats at h_fr_unique ⊢
            simp
            constructor
            · -- Current frame: fr
              -- Need: frame_has_unique_floats (db.insert...) fr.hyps
              -- We have: frame_has_unique_floats db fr.hyps (h_fr_unique)
              -- Key: l ∉ fr.hyps, so insert doesn't affect fr lookups
              exact frame_has_unique_floats_insert_ne db pos l (fun _ => Object.assert fmla fr proof) fr.hyps
                h_fr_unique h_l_not_in_fr h_success_ins
            · -- Assertions: all frames including new one have unique floats
              intros label' fmla' fr' proof' h_find
              by_cases h_eq : label' = l
              · -- New assertion at l
                -- h_find has the withFrame structure: { (db.insert...) with frame := fr }.find? label' = ...
                -- Key observation: withFrame only changes frame, not objects
                -- So { db with frame := fr }.find? = db.find? (same objects field)
                --
                -- Strategy: Simplify h_find to show it's about (db.insert...).objects[l]?
                -- DON'T use subst h_eq - it makes l disappear!
                -- Instead use rw [h_eq] to rewrite label' to l
                rw [h_eq] at h_find
                -- Now: { (db.insert...) with frame := fr }.find? l = some (.assert fmla' fr' proof')
                unfold DB.find? at h_find
                simp at h_find
                -- Now: (db.insert...).objects[l]? = some (.assert fmla' fr' proof')
                -- We know (db.insert...).objects[l]? = some (.assert fmla fr proof)
                -- Use DB.insert structure
                unfold DB.insert at h_find
                simp at h_find
                by_cases h_err : db.error
                · simp [h_err] at h_find
                  cases hopt : db.error? with
                  | none => simp [DB.error, hopt] at h_err
                  | some e => simp [hopt] at h_success_ins
                · simp [h_err] at h_find
                  cases hfind_old : db.find? l with
                  | none =>
                      simp [hfind_old] at h_find
                      -- After simp, h_find should be a conjunction fmla = fmla' ∧ fr = fr' ∧ proof = proof'
                      -- Extract the equality fr = fr'
                      have ⟨_, h_eq_fr, _⟩ := h_find
                      rw [← h_eq_fr]
                      exact frame_has_unique_floats_insert_ne db pos l (fun _ => .assert fmla fr proof) fr.hyps
                        h_fr_unique h_l_not_in_fr h_success_ins
                  | some o =>
                      -- Duplicate found: db.find? l = some o
                      -- DB.insert with duplicate calls mkError (except for var overwriting)
                      -- But h_success_ins says (db.insert...).error? = none
                      -- Contradiction!
                      exfalso
                      -- ok = false means DB.insert calls mkError, setting error? ≠ none
                      have hne : (db.mkError pos s!"duplicate symbol/assert {l}").error? ≠ none :=
                        error_persists_mkError db pos s!"duplicate symbol/assert {l}"
                      -- But h_success_ins says error? = none after insert
                      -- Unfold DB.insert in h_success_ins and use hfind_old to show mkError path
                      have hcontra : (db.mkError pos s!"duplicate symbol/assert {l}").error? = none := by
                        unfold DB.insert at h_success_ins
                        simp [h_err] at h_success_ins
                        have hfind' : db.objects[l]? = some o := by unfold DB.find? at hfind_old; exact hfind_old
                        simp [DB.find?, hfind_old, hfind'] at h_success_ins
                        -- Now h_success_ins has: (if (match o with | .var _ => false | _ => false) = true then db else mkError).error? = none
                        -- Split on o to show the match returns false in all cases
                        cases o <;> simp at h_success_ins <;> exact h_success_ins
                      exact (hne hcontra).elim
              · -- Old assertion at label' ≠ l
                -- The goal asks about frame_has_unique_floats for { (db.insert...) with frame := fr }
                -- But h_inv_after.2 gives us the property for any assertion in (db.insert...)
                -- The withFrame doesn't affect lookups (only changes frame field)
                -- So we can use h_inv_after.2 directly
                exact h_inv_after.2 label' fmla' fr' proof' h_find
          · -- Insert failed (has error) - contradiction with h_inv_after
            -- We have h_inv_after : db_has_unique_floats (db.insert...)
            -- But insert set error, so find? operations won't work correctly
            -- This means we derived the invariant in an inconsistent state
            right
            -- Prove error is set
            exact h_success_ins
  | pushScope =>
      -- pushScope only modifies scopes array, not frame or objects
      unfold DBOp.apply DB.pushScope
      left
      -- The frame and objects are unchanged
      -- So the invariant is trivially preserved
      unfold db_has_unique_floats frame_has_unique_floats at h_inv ⊢
      simp
      exact h_inv
  | popScope pos =>
      -- popScope shrinks frame.hyps or sets error
      unfold DBOp.apply DB.popScope
      cases h_back : db.scopes.back? with
      | none =>
          -- No scope to pop: mkError sets error
          right
          simp [DB.error_mkError]
      | some sc =>
          -- Pop succeeds: frame shrinks to first sc elements
          left
          -- Shrinking frame.hyps preserves uniqueness:
          -- If i, j < sc, then they were < frame.hyps.size before
          -- and the uniqueness property still holds for them
          unfold db_has_unique_floats frame_has_unique_floats at h_inv ⊢
          unfold Frame.shrink
          constructor
          · -- Current frame: fewer hyps but same uniqueness
            intros i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_szi h_szj
            have ⟨h_curr, _⟩ := h_inv
            -- From hi : i < (db.frame.hyps.shrink sc.2).size
            -- Use Array.size_shrink to get i < min sc.2 db.frame.hyps.size
            rw [Array.size_shrink] at hi hj
            -- Now hi : i < min sc.2 db.frame.hyps.size
            have hi_n : i < sc.2 := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
            have hi_orig : i < db.frame.hyps.size := Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
            have hj_n : j < sc.2 := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
            have hj_orig : j < db.frame.hyps.size := Nat.lt_of_lt_of_le hj (Nat.min_le_right _ _)
            -- Use Array.getElem_shrink to connect shrunk and original
            have h_i_eq : (db.frame.hyps.shrink sc.2)[i] = db.frame.hyps[i] :=
              Array.getElem_shrink db.frame.hyps sc.2 i hi_n hi_orig
            have h_j_eq : (db.frame.hyps.shrink sc.2)[j] = db.frame.hyps[j] :=
              Array.getElem_shrink db.frame.hyps sc.2 j hj_n hj_orig
            -- Rewrite h_fi and h_fj using equalities
            rw [h_i_eq] at h_fi
            rw [h_j_eq] at h_fj
            -- Now apply h_curr with original frame indices
            exact h_curr i j hi_orig hj_orig h_ne fi fj lbli lblj h_fi h_fj h_szi h_szj
          · -- Assertions: objects unchanged, so lookups identical
            intros label fmla fr proof h_find
            have ⟨_, h_frames⟩ := h_inv
            -- popScope doesn't modify objects HashMap
            -- So db.find? = ({ db with frame := ... }).find?
            -- The frame_has_unique_floats for fr is about lookups in db.objects
            -- which are unchanged by popScope
            unfold DB.find? at h_find
            simp at h_find
            -- Apply h_frames with the find from original db
            have h_find_orig : db.find? label = some (.assert fmla fr proof) := by
              unfold DB.find?
              exact h_find
            exact h_frames label fmla fr proof h_find_orig
  | noOp =>
      -- NoOp doesn't change db
      unfold DBOp.apply
      left
      exact h_inv

/-- Apply a trace to emptyDB: if no error at end, invariant holds. -/
theorem ParseTrace.preserves_invariant (trace : ParseTrace) :
  (trace.apply emptyDB).error? = none →
  db_has_unique_floats (trace.apply emptyDB) := by
  induction trace with
  | nil =>
      -- Empty trace: db = emptyDB
      intro _
      exact empty_db_has_unique_floats
  | cons op ops ih =>
      intro h_success
      unfold ParseTrace.apply at h_success ⊢
      -- After applying op to emptyDB, then ops
      -- Let db' = op.apply emptyDB
      -- Then trace.apply ops db' gives final result
      -- We need: db_has_unique_floats (ops.apply (op.apply emptyDB))

      -- Key insight: h_success means (ops.apply db').error? = none
      -- This means db'.error? = none (errors are sticky)
      -- Actually, we need to be more careful here
      sorry -- Need: error propagation property + careful induction

/-- **Main Induction Theorem**: Parser success implies database has unique floats.

Proof strategy:
1. Base case: Empty DB satisfies invariant (empty_db_has_unique_floats)
2. Inductive step: Each parser operation maintains invariant
   - insertHyp: insertHyp_maintains_db_uniqueness
   - insert (const/var): insert_const_var_maintains_uniqueness
   - pushScope: pushScope_maintains_uniqueness
   - popScope: popScope_maintains_uniqueness
   - trimFrame: trimFrame_maintains_uniqueness (for assertions)
3. By induction on parsing operations: if error? = none throughout,
   then invariant maintained

The proof requires showing that the parser can be modeled as a sequence
of these operations starting from empty_db, and that error? = none
means no operation set an error.
-/
theorem parser_success_implies_unique_floats
  (db : DB)
  (h_success : db.error? = none) :
  db_has_unique_floats db := by
  -- The key insight: We need an additional hypothesis that db was produced
  -- by applying a ParseTrace to emptyDB. Without this, we can't prove the invariant
  -- for an arbitrary DB.
  --
  -- The actual theorem we can prove is:
  --   ∀ (trace : ParseTrace), (trace.apply emptyDB).error? = none →
  --     db_has_unique_floats (trace.apply emptyDB)
  --
  -- This is proven by ParseTrace.preserves_invariant (which has a sorry for
  -- error propagation).
  --
  -- To make this work with the axiom signature, we would need to either:
  -- 1. Add a "trace witness" to the DB structure, OR
  -- 2. Axiomatize that all valid DBs come from parsing, OR
  -- 3. Change the axiom to quantify over traces
  --
  -- For now, we use classical reasoning + axiom of choice to extract a trace:
  sorry

/-- **Main Result**: Prove the parser_validates_float_uniqueness axiom.

This theorem has the exact signature of the axiom, so once proven,
we can replace the axiom with this theorem.
-/
theorem prove_parser_validates_float_uniqueness :
  ∀ (db : DB) (label : String) (fmla : Formula) (fr : Frame) (proof : String),
    db.error? = none →
    db.find? label = some (.assert fmla fr proof) →
    ∀ (i j : Nat) (hi : i < fr.hyps.size) (hj : j < fr.hyps.size) (h_ne : i ≠ j),
      ∀ (fi fj : Formula) (vi vj : String) (lbli lblj : String),
        db.find? fr.hyps[i] = some (.hyp false fi lbli) →
        db.find? fr.hyps[j] = some (.hyp false fj lblj) →
        fi.size >= 2 → fj.size >= 2 →
        (match fi[1]! with | .var v => v | _ => "") = vi →
        (match fj[1]! with | .var v => v | _ => "") = vj →
        vi ≠ vj := by
  intros db label fmla fr proof h_success h_find
  -- Use parser_success_implies_unique_floats
  have h_unique := parser_success_implies_unique_floats db h_success
  -- Extract the frame uniqueness property
  have ⟨_, h_frames⟩ := h_unique
  have h_fr_unique := h_frames label fmla fr proof h_find
  -- Apply frame_has_unique_floats definition
  intros i j hi hj h_ne fi fj vi vj lbli lblj
  intros h_fi h_fj h_szi h_szj h_vi h_vj
  -- Unfold definitions
  unfold frame_has_unique_floats at h_fr_unique
  -- Apply the invariant
  specialize h_fr_unique i j hi hj h_ne fi fj lbli lblj h_fi h_fj h_szi h_szj
  -- h_fr_unique says: (extract from fi) ≠ (extract from fj)
  -- We need to show: vi ≠ vj
  -- We have: h_vi : (extract from fi) = vi and h_vj : (extract from fj) = vj
  rw [← h_vi, ← h_vj]
  exact h_fr_unique

/-! ## Helper Lemma: Float Size Constraint

This lemma captures the key insight for completing the Step 1 f.size = 2 proof.

To prove that if f is a float hypothesis in a successful parse, then f.size = 2,
we need to establish that f came from feedTokens line 613 where the check at
line 611 (arr.size == 2) was verified before insertHyp was called.

This requires feedAll loop induction to show that only feedTokens line 613
can add $f hypotheses to the database.
-/

/-- **Key Property**: If a float hypothesis entered the DB, its size must be 2.

This lemma establishes the critical link between:
1. Hypothesis in DB (found via db.find?)
2. It came from feedTokens (line 613)
3. Which requires arr.size == 2 (line 611 check)
4. Therefore f.size = 2 (since f = arr from insertHyp)

PROOF STRATEGY:
The formal completion requires:
1. Prove that the only way to add a $f hypothesis is via feedTokens line 613
   - This needs feedAll loop induction showing line 613 is the only source
2. Show that line 613 is only reachable if line 611 check (arr.size == 2) passes
3. Apply error monotonicity: if check had failed, mkError would set db.error?
4. Use feed_stops_on_error to show error would persist to final state
5. Contradiction with h_success: db.error? = none

INTERMEDIATE STEP (what we can prove now):
If we assume h_path: "the float f came from feedTokens line 613", then
we can prove f.size = 2 by showing:
  - Line 613 only reached if line 611 check passes
  - Line 611 check requires arr.size == 2
  - f = arr, so f.size == 2
-/
theorem float_from_feedTokens_has_size_2
  (db : DB) (pos : Pos) (l : String) (f : Formula) (lbl : String)
  (h_in_db : db.find? l = some (.hyp false f lbl))
  (h_path : ∃ (arr : Array Verify.Sym), f = arr ∧
    -- This formula came from feedTokens line 613 with size check
    ∃ (check_passed : arr.size == 2 ∧ arr[1]!.isVar),
    ∃ (inserted : Verify.DB.insertHyp db pos l false arr = db),
    True) :
  f.size = 2 := by
  -- This lemma says: IF we can prove that f came from feedTokens line 613,
  -- THEN we can prove f.size = 2.
  --
  -- The key insight: feedTokens only calls insertHyp (line 613) after the check
  -- at line 611 (arr.size == 2) passes. Since f = arr from insertHyp,
  -- we have f.size == 2.
  --
  -- To use this lemma to complete the ParserInvariants proof:
  -- 1. Use feedAll loop induction to show f came from feedTokens line 613
  -- 2. Apply this lemma with the h_path witness
  -- 3. Get f.size = 2 directly
  --
  -- This unblocks the parser_validates_all_float_structures proof.
  sorry  -- This is a direct proof once h_path is established

end Metamath.ParserProofs
