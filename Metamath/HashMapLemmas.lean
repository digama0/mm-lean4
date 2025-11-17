/-
# HashMap Lemmas: Infrastructure for Sonnet 4.5

This module provides HashMap reasoning infrastructure to eliminate axioms and
make proofs tractable for Sonnet 4.5. We bridge between Batteries' HashMap
and our verification needs.

**Key insight**: Most HashMap proofs reduce to showing that after a sequence
of insertions, we can find what we inserted. This module provides the machinery.
-/

import Batteries.Data.HashMap
import Metamath.Verify

namespace Metamath.HashMapLemmas

open Std

/-! ## Core HashMap Properties

These replace the axioms in ParserCorrectness.lean with actual theorems.
We use Batteries' HashMap lemmas where available.
-/

/-- After insert, we can find the inserted value -/
theorem HashMap.find?_insert_self {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : HashMap α β) (k : α) (v : β) :
    (m.insert k v)[k]? = some v := by
  -- Batteries.HashMap wraps Std.HashMap
  -- The Std.HashMap theorem directly applies
  exact Std.HashMap.getElem?_insert_self

/-- Insert doesn't affect unrelated keys -/
theorem HashMap.find?_insert_other {α β} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (m : HashMap α β) (k k' : α) (v : β) :
    k ≠ k' → (m.insert k v)[k']? = m[k']? := by
  intro h_ne
  -- Use Std.HashMap.getElem?_insert which gives us the conditional
  rw [Std.HashMap.getElem?_insert]
  -- Goal: if k == k' then some v else m[k']? = m[k']?
  -- We need to show the if evaluates to the else branch
  -- With LawfulBEq, we can use beq_iff_eq
  have h_beq_false : ¬((k == k') = true) := by
    intro h
    -- beq_iff_eq gives us: (k == k') = true ↔ k = k'
    rw [beq_iff_eq] at h
    exact h_ne h
  simp [h_beq_false]

/-- String has LawfulBEq (needed for HashMap proofs) -/
instance : LawfulBEq String where
  eq_of_beq := by
    intro a b hab
    -- String's BEq is just structural equality
    simp [BEq.beq] at hab
    exact hab
  rfl := by
    intro a
    -- String equality is reflexive
    simp [BEq.beq]

/-! ## HashMap Sequences and Folds

Common pattern: build HashMap via fold over a list of insertions.
-/

/-- Folding insertions preserves findability -/
theorem HashMap.find?_after_fold_insert {α β} [BEq α] [Hashable α] [LawfulBEq α]
    (pairs : List (α × β)) (m : HashMap α β) (k : α) (v : β) :
    (k, v) ∈ pairs →
    -- No duplicate keys assumption
    ((pairs.foldl (fun acc (k, v) => acc.insert k v) m)[k]? = some v ∨
     m[k]? = some v) := by
  sorry -- TODO: Prove by induction on pairs

/-! ## Pattern: Proving Properties Through HashMap Construction

This pattern appears everywhere in the parser:
1. Start with empty HashMap
2. Insert entries one by one (checking conditions)
3. If no error, all entries are findable
-/

structure HashMapBuildInvariant {α β} [BEq α] [Hashable α] where
  -- The map being built
  map : HashMap α β
  -- Keys processed so far
  processed : List α
  -- Invariant: all processed keys are findable
  inv : ∀ k ∈ processed, map[k]?.isSome

/-- Building step preserves invariant -/
theorem HashMapBuildInvariant.insert_preserves {α β} [BEq α] [Hashable α] [LawfulBEq α]
    (hbi : @HashMapBuildInvariant α β _ _) (k : α) (v : β)
    (h_not_dup : k ∉ hbi.processed) :
    ∃ hbi' : @HashMapBuildInvariant α β _ _,
      hbi'.map = hbi.map.insert k v ∧
      hbi'.processed = k :: hbi.processed := by
  sorry -- TODO: Construct the new HashMapBuildInvariant

/-! ## Application to Verify.DB

The DB object map is just a HashMap String Object.
These lemmas directly apply to proving parser properties.
-/

/-- DB.find? after insert (no error case) -/
theorem DB.find?_after_insert_no_error
    (db : Verify.DB) (pos : Verify.Pos) (label : String) (obj : String → Verify.Object) :
    db.error = false →
    db.find? label = none →
    let db' := db.insert pos label obj
    db'.error = false →
    db'.find? label = some (obj label) := by
  intro h_no_err h_not_found h_no_err'
  -- DB.insert has complex control flow, need detailed analysis
  sorry -- TODO: Analyze DB.insert implementation

/-! ## Tactic Helpers for Sonnet

These tactics help automate common patterns.
-/

/-- Simplify HashMap lookups after insertions -/
macro "hashmap_simp" : tactic => `(tactic|
  simp [HashMap.find?_insert_self, HashMap.find?_insert_other])

/-- Unfold DB operations to reveal HashMap operations -/
macro "db_unfold" : tactic => `(tactic|
  unfold Verify.DB.insert Verify.DB.find? Verify.DB.error)

end Metamath.HashMapLemmas