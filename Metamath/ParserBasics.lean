/-
# Parser Basics: Trivial Properties

Super simple, obviously correct properties about the parser that are easy warm-up proofs.
These establish basic facts about DB operations that are useful building blocks.
-/

import Metamath.Verify

namespace Metamath.ParserBasics

open Verify

/-! ## Error State is Monotonic

Once the parser enters an error state, it stays in error state.
This is trivially true because parser operations check `if db.error then return db`.
-/

/-- If a DB is in error state, it remains in error state after mkError -/
theorem mkError_preserves_error (db : DB) (pos : Pos) (msg : String) :
  db.error?.isSome → (db.mkError pos msg).error?.isSome := by
  intro h
  unfold DB.mkError
  simp

/-- mkError always puts DB into error state -/
theorem mkError_sets_error (db : DB) (pos : Pos) (msg : String) :
  (db.mkError pos msg).error?.isSome = true := by
  unfold DB.mkError
  simp

/-- If DB has no error, db.error is false -/
theorem no_error_iff (db : DB) :
  db.error? = none ↔ db.error = false := by
  unfold DB.error
  simp [Option.isSome]
  cases db.error? <;> simp

/-- If DB has error, db.error is true -/
theorem has_error_iff (db : DB) :
  db.error?.isSome ↔ db.error = true := by
  unfold DB.error
  rfl

/-! ## Frame Operations Preserve Object Map

These operations only modify the frame/scopes, not the object database.
-/

/-- pushScope doesn't modify objects -/
theorem pushScope_preserves_objects (db : DB) :
  (db.pushScope).objects = db.objects := by
  unfold DB.pushScope
  rfl

/-- pushScope doesn't modify error state -/
theorem pushScope_preserves_error (db : DB) :
  (db.pushScope).error? = db.error? := by
  unfold DB.pushScope
  rfl

/-! ## DB.find? is Pure

Looking up objects doesn't modify the database.
-/

/-- find? is deterministic - same key always gives same result -/
theorem find?_deterministic (db : DB) (label : String) (obj1 obj2 : Object) :
  db.find? label = some obj1 →
  db.find? label = some obj2 →
  obj1 = obj2 := by
  intro h1 h2
  rw [h1] at h2
  injection h2

/-- If find? returns none, label is not in the database -/
theorem find?_none_not_present (db : DB) (label : String) :
  db.find? label = none →
  ∀ obj, db.find? label ≠ some obj := by
  intro h obj h_contra
  rw [h] at h_contra
  contradiction

/-! ## Simple Character Properties

These are just unfolding definitions - completely trivial!
-/

/-- isPrintable unfolds to range check -/
theorem isPrintable_def (c : UInt8) :
  isPrintable c = (c >= 32 && c <= 126) := by
  rfl

/-- isWhitespace unfolds to character check -/
theorem isWhitespace_unfold (c : UInt8) :
  isWhitespace c =
    (c == ' '.toUInt8 || c == '\n'.toUInt8 || c == '\r'.toUInt8 || c == '\t'.toUInt8) := by
  rfl

/-- isMathChar excludes dollar sign -/
theorem isMathChar_def (c : UInt8) :
  isMathChar c = (c ≠ '$'.toUInt8 && isPrintable c) := by
  rfl

/-! ## Option Extraction Helpers

Common patterns for extracting data from Option types, especially around db.find?
These eliminate repetitive match/case analysis.
-/

/-- If find? returns a float, we can extract its components -/
theorem find?_float_extract {db : DB} {label : String} {f : Formula} {lbl : String} :
  db.find? label = some (.hyp false f lbl) →
  ∃ f' lbl', db.find? label = some (.hyp false f' lbl') ∧ f = f' ∧ lbl = lbl' := by
  intro h
  exact ⟨f, lbl, h, rfl, rfl⟩

/-- If find? returns an essential, we can extract its components -/
theorem find?_essential_extract {db : DB} {label : String} {f : Formula} {lbl : String} :
  db.find? label = some (.hyp true f lbl) →
  ∃ f' lbl', db.find? label = some (.hyp true f' lbl') ∧ f = f' ∧ lbl = lbl' := by
  intro h
  exact ⟨f, lbl, h, rfl, rfl⟩

/-- If find? returns an assertion, we can extract its components -/
theorem find?_assert_extract {db : DB} {label : String} {f : Formula} {fr : Frame} {proof : String} :
  db.find? label = some (.assert f fr proof) →
  ∃ f' fr' proof', db.find? label = some (.assert f' fr' proof') ∧
    f = f' ∧ fr = fr' ∧ proof = proof' := by
  intro h
  exact ⟨f, fr, proof, h, rfl, rfl, rfl⟩

/-- Two different find? results for same label must be equal -/
theorem find?_unique {db : DB} {label : String} {obj1 obj2 : Object} :
  db.find? label = some obj1 →
  db.find? label = some obj2 →
  obj1 = obj2 := by
  intro h1 h2
  rw [h1] at h2
  injection h2

/-- If find? succeeds, we have an object -/
theorem find?_some_iff {db : DB} {label : String} :
  (∃ obj, db.find? label = some obj) ↔ db.find? label ≠ none := by
  constructor
  · intro ⟨obj, h⟩
    intro h_contra
    rw [h] at h_contra
    contradiction
  · intro h
    cases h_eq : db.find? label
    · contradiction
    · exact ⟨_, rfl⟩

end Metamath.ParserBasics
