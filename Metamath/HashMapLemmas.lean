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
import Metamath.ParserInvariants

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

/-- Helper: fold over insertions doesn't affect keys not in the list -/
theorem HashMap.fold_insert_preserves_other {α β} [BEq α] [Hashable α] [LawfulBEq α]
    (pairs : List (α × β)) (m : HashMap α β) (k : α)
    (h_not_in : ∀ v, (k, v) ∉ pairs) :
    (pairs.foldl (fun acc (kv : α × β) => acc.insert kv.1 kv.2) m)[k]? = m[k]? := by
  induction pairs generalizing m with
  | nil => rfl
  | cons hd tl IH =>
    simp only [List.foldl_cons]
    cases hd with
    | mk k' v' =>
      have h_ne : k ≠ k' := by
        intro h_eq
        subst h_eq
        have := h_not_in v'
        simp at this
      rw [IH]
      · rw [Std.HashMap.getElem?_insert]
        -- Goal: (if (k' == k) = true then some v' else m[k]?) = m[k]?
        -- We have h_ne : k ≠ k', so k' ≠ k
        have h_ne' : k' ≠ k := fun h => h_ne h.symm
        simp only [beq_iff_eq, h_ne', ↓reduceIte]
      · intro v h_v
        exact h_not_in v (List.mem_cons_of_mem _ h_v)

/-- Folding insertions preserves findability when keys are unique.
    Without uniqueness, the last insertion of a key wins. -/
theorem HashMap.find?_after_fold_insert {α β} [BEq α] [Hashable α] [LawfulBEq α]
    (pairs : List (α × β)) (m : HashMap α β) (k : α) (v : β)
    (h_unique : ∀ v', (k, v') ∈ pairs → v' = v) :
    (k, v) ∈ pairs →
    (pairs.foldl (fun acc (kv : α × β) => acc.insert kv.1 kv.2) m)[k]? = some v := by
  intro h_mem
  induction pairs generalizing m with
  | nil => simp at h_mem
  | cons hd tl IH =>
    simp only [List.foldl_cons]
    cases hd with
    | mk k' v' =>
      -- Check if (k,v) is the head or in the tail
      rcases List.mem_cons.mp h_mem with h_eq | h_in_tl
      · -- (k, v) is the head element
        simp only [Prod.mk.injEq] at h_eq
        obtain ⟨rfl, rfl⟩ := h_eq
        -- Need to show k persists through the fold
        -- Since keys are unique, if k appears in tl it must be with value v
        by_cases h_k_in_tl : ∃ v'', (k, v'') ∈ tl
        · -- k appears in tl with some value v''
          obtain ⟨v'', h_v''⟩ := h_k_in_tl
          -- By uniqueness, v'' = v
          have h_v_eq : v'' = v := h_unique v'' (List.mem_cons_of_mem _ h_v'')
          subst h_v_eq
          -- Apply IH
          apply IH
          · intro v''' h_v'''
            exact h_unique v''' (List.mem_cons_of_mem _ h_v''')
          · exact h_v''
        · -- k doesn't appear in tl
          -- Convert ¬∃ to ∀¬
          have h_not_in : ∀ v'', (k, v'') ∉ tl := by
            intro v'' h_v''
            exact h_k_in_tl ⟨v'', h_v''⟩
          -- Use helper lemma
          rw [HashMap.fold_insert_preserves_other tl (m.insert k v) k h_not_in]
          exact Std.HashMap.getElem?_insert_self
      · -- (k, v) is in the tail, apply IH
        apply IH
        · intro v' h_v'
          exact h_unique v' (List.mem_cons_of_mem _ h_v')
        · exact h_in_tl

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
  -- Construct the new invariant
  refine ⟨⟨hbi.map.insert k v, k :: hbi.processed, ?_⟩, rfl, rfl⟩
  -- Prove the invariant
  intro k' h_mem
  simp only [List.mem_cons] at h_mem
  rcases h_mem with rfl | h_in_old
  · -- k' = k: the newly inserted key
    simp only [Std.HashMap.getElem?_insert_self, Option.isSome_some]
  · -- k' in old processed list
    -- k' was findable in hbi.map, still findable after insert
    have h_old := hbi.inv k' h_in_old
    simp only [Option.isSome_iff_exists] at h_old ⊢
    obtain ⟨val, h_val⟩ := h_old
    -- After insert, either k' == k (contradiction) or k' persists
    by_cases h_eq : k' = k
    · subst h_eq; exact absurd h_in_old h_not_dup
    · rw [Std.HashMap.getElem?_insert]
      have h_ne : ¬(k == k') := by
        simp only [beq_iff_eq]
        exact fun h => h_eq h.symm
      simp [h_ne]
      exact ⟨val, h_val⟩

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
  -- DB.insert is complex with const check and duplicate check
  -- Since we're given db.find? label = none and db'.error = false,
  -- the insert must have succeeded by adding to objects
  -- This requires detailed unfolding of DB.insert which is complex
  -- For now, leave as sorry pending more investigation
  sorry

/-! ## Tactic Helpers for Sonnet

These tactics help automate common patterns.
-/

/-- Simplify HashMap lookups after insertions -/
macro "hashmap_simp" : tactic => `(tactic|
  simp [HashMap.find?_insert_self, HashMap.find?_insert_other])

/-- Unfold DB operations to reveal HashMap operations -/
macro "db_unfold" : tactic => `(tactic|
  unfold Verify.DB.insert Verify.DB.find? Verify.DB.error)

/-! ## Float Structure Lemmas

The parser checks (Verify.lean:611-612) that floats satisfy:
- `arr.size == 2` - Floats have exactly 2 elements
- `arr[1]!.isVar` - Second element is a variable (not constant)

These lemmas extract these facts from ParserInvariants theorems - NO AXIOMS!
-/

/-- If an object in the database is a float hypothesis (and parsing succeeded),
its formula has size ≥ 2. Proven from parser checks at Verify.lean:611. -/
theorem float_has_size_ge_2 (db : Verify.DB) (label : String) (f : Verify.Formula) (lbl : String)
    (h_success : db.error? = none)
    (h_find : db.find? label = some (.hyp false f lbl)) :
    f.size ≥ 2 := by
  have h_eq := ParserInvariants.parser_enforces_float_size db h_success label f lbl h_find
  omega

/-- If an object in the database is a float hypothesis (and parsing succeeded),
f[1] is a variable. Proven from parser checks at Verify.lean:611. -/
theorem float_has_var_at_1 (db : Verify.DB) (label : String) (f : Verify.Formula) (lbl : String)
    (h_success : db.error? = none)
    (h_find : db.find? label = some (.hyp false f lbl)) :
    ∃ v : String, f[1]! = .var v := by
  have h_struct := ParserInvariants.parser_enforces_float_structure db h_success label f lbl h_find
  obtain ⟨c, v, h_size, h_const, h_var⟩ := h_struct
  exact ⟨v, h_var⟩

/-- Helper: Extract variable name from f[1] when it's a var. -/
theorem float_var_value_eq (f : Verify.Formula) (v : String) :
  f[1]! = .var v →
  f[1]!.value = (match f[1]! with | .var w => w | _ => "") := by
  intro h
  rw [h]
  simp [Verify.Sym.value]

/-! ## checkHyp Persistence Lemmas

The key insight (Mario Carneiro style): checkHyp ONLY modifies the HashMap via insert
at line 386 of Verify.lean. It NEVER removes entries. Therefore:
- Inserted values persist through the recursion
- Unchanged values remain unchanged

**PROOF STRATEGY**:
1. Strong induction on fuel = hyps.size - i
2. Base case (i ≥ hyps.size): checkHyp returns σ unchanged, use HashMap.getElem?_insert_self
3. Recursive case: unfold with checkHyp_step lemmas
   - Float case: recurses with (σ.insert k' v'), apply IH
     * Key persists because HashMap.insert never removes keys
     * Use that (σ.insert k v).insert k' v' preserves both k and k'
   - Essential case: recurses with σ unchanged, apply IH directly
4. The Std.HashMap theorems give us the base facts we need!

This is Mario's style: mirror the implementation exactly, use library lemmas.
-/

/-- **Persistence Lemma 2** (proven first!): Existing keys persist through checkHyp.

If checkHyp succeeds with σ_in, and k was already in σ_in with value v,
then σ_out contains k ↦ v.

PROOF INSIGHT: Same as above - checkHyp only inserts, preserving existing entries.
This is easier to prove first because the IH applies directly!

**Key assumption**: We need uniqueness (no two floats bind the same variable) AND
that σ_in only contains keys from floats at indices < i. This rules out the edge
case where we try to insert at index i for a variable that's already bound. -/
theorem checkHyp_preserves_keys
    {db : Verify.DB} {hyps : Array String} {stack : Array Verify.Formula}
    {off : {off : Nat // off + hyps.size = stack.size}}
    {i : Nat} {σ_in σ_out : Std.HashMap String Verify.Formula}
    {k : String} {v : Verify.Formula}
    (h_success : db.error? = none)
    (h_unique : ∀ (i j : Nat) (hi : i < hyps.size) (hj : j < hyps.size),
        i ≠ j →
        ∀ (fi fj : Verify.Formula) (lbli lblj : String),
          db.find? hyps[i] = some (.hyp false fi lbli) →
          db.find? hyps[j] = some (.hyp false fj lblj) →
          fi.size ≥ 2 → fj.size ≥ 2 →
          let vi := match fi[1]! with | .var v => v | _ => ""
          let vj := match fj[1]! with | .var v => v | _ => ""
          vi ≠ vj)
    (h_keys_from_before_i : ∀ (key : String) (val : Verify.Formula),
        σ_in[key]? = some val →
        ∃ (j : Nat) (hj : j < i) (hj_bound : j < hyps.size) (f : Verify.Formula) (lbl : String),
          db.find? (hyps[j]'hj_bound) = some (.hyp false f lbl) ∧
          f.size ≥ 2 ∧
          (match f[1]! with | .var v => v | _ => "") = key)
    (h_in : σ_in[k]? = some v)
    (h_ok : db.checkHyp hyps stack off i σ_in = Except.ok σ_out) :
    σ_out[k]? = some v := by
  -- Induction on hyps.size - i
  generalize h_fuel : hyps.size - i = fuel
  revert i σ_in σ_out h_unique h_keys_from_before_i h_in h_ok h_fuel
  induction fuel with
  | zero =>
      intro i σ_in σ_out h_unique h_keys_from_before_i h_in h_ok h_fuel
      have h_ge : ¬(i < hyps.size) := by omega
      rw [Verify.DB.checkHyp_base _ _ _ _ _ _ h_ge] at h_ok
      injection h_ok with h_eq
      rw [← h_eq]
      exact h_in
  | succ fuel' IH =>
      intro i σ_in σ_out h_unique h_keys_from_before_i h_in h_ok h_fuel
      have hi_lt : i < hyps.size := by omega
      cases h_find : db.find? hyps[i] with
      | none =>
        -- WF: checkHyp reaches unreachable! when db.find? = none
        -- Contradiction: unreachable! cannot equal Except.ok
        unfold Verify.DB.checkHyp at h_ok
        simp only [hi_lt, dif_pos] at h_ok
        rw [h_find] at h_ok
        simp at h_ok
      | some obj =>
        cases obj with
        | const _ =>
          -- WF: checkHyp reaches unreachable! for const objects
          unfold Verify.DB.checkHyp at h_ok
          simp only [hi_lt, dif_pos] at h_ok
          rw [h_find] at h_ok
          simp at h_ok
        | var _ =>
          -- WF: checkHyp reaches unreachable! for var objects
          unfold Verify.DB.checkHyp at h_ok
          simp only [hi_lt, dif_pos] at h_ok
          rw [h_find] at h_ok
          simp at h_ok
        | assert _ _ _ =>
          -- WF: checkHyp reaches unreachable! for assert objects
          unfold Verify.DB.checkHyp at h_ok
          simp only [hi_lt, dif_pos] at h_ok
          rw [h_find] at h_ok
          simp at h_ok
        | hyp ess f lbl =>
          cases ess
          · -- Float: recurses with σ_in.insert k' v'
            have h_step := Verify.DB.checkHyp_step_hyp_false db hyps stack off i σ_in f lbl hi_lt h_find
            rw [h_step] at h_ok
            split at h_ok
            · -- Typecode passed
              -- Need: (σ_in.insert k' v')[k]? = some v
              -- We have: σ_in[k]? = some v
              -- Use HashMap.getElem?_insert: if k ≠ k' then preserved!
              have h_in' : (σ_in.insert f[1]!.value (stack[off.1 + i]!))[k]? = some v := by
                rw [Std.HashMap.getElem?_insert]
                split
                · -- k == f[1]!.value = true, so k = f[1]!.value
                  -- This case is IMPOSSIBLE by uniqueness!
                  -- k ∈ σ_in means k came from some float at index j < i
                  -- But f[1]!.value is the variable bound at index i
                  -- Uniqueness says no two floats bind the same variable
                  rename_i h_eq
                  -- h_eq comes from split, could be (k == f[1]!.value) = true
                  -- Use LawfulBEq for String to convert to equality
                  have h_k_eq : k = f[1]!.value := by
                    rw [beq_iff_eq] at h_eq
                    exact h_eq.symm
                  have ⟨j, hj, hj_bound, f_j, lbl_j, h_find_j, h_size_j, h_var_j⟩ := h_keys_from_before_i k v h_in
                  -- Now apply uniqueness: i ≠ j, both are floats for same variable
                  have h_i_ne_j : i ≠ j := Nat.ne_of_gt hj
                  -- Apply uniqueness: different indices with floats for same variable → contradiction
                  have h_i_bound : i < hyps.size := hi_lt
                  -- This case is impossible - derive contradiction from uniqueness
                  -- f.size ≥ 2 and f_j.size ≥ 2 from parser checks
                  have h_f_size : f.size ≥ 2 := float_has_size_ge_2 db hyps[i] f lbl h_success h_find
                  have h_vars_ne : (match f[1]! with | .var v => v | _ => "") ≠
                                    (match f_j[1]! with | .var v => v | _ => "") := by
                    exact h_unique i j h_i_bound hj_bound h_i_ne_j f f_j lbl lbl_j h_find h_find_j h_f_size h_size_j
                  -- h_var_j : (match f_j[1]! with | .var v => v | _ => "") = k
                  -- h_k_eq : k = f[1]!.value
                  -- h_vars_ne : (match f[1]! with | .var v => v | _ => "") ≠ (match f_j[1]! with | .var v => v | _ => "")
                  -- Need to show: f[1]!.value = (match f[1]! with | .var v => v | _ => "")
                  have h_f1_var : f[1]!.value = (match f[1]! with | .var v => v | _ => "") := by
                    have ⟨v_f, hv_f⟩ := float_has_var_at_1 db hyps[i] f lbl h_success h_find
                    exact float_var_value_eq f v_f hv_f
                  -- Now: k = f[1]!.value = (match f[1]! with ...)
                  --      k = (match f_j[1]! with ...)
                  -- So: (match f[1]! with ...) = (match f_j[1]! with ...), contradicting h_vars_ne
                  have : (match f[1]! with | .var v => v | _ => "") =
                         (match f_j[1]! with | .var v => v | _ => "") := by
                    calc (match f[1]! with | .var v => v | _ => "")
                        = f[1]!.value := h_f1_var.symm
                      _ = k := h_k_eq.symm
                      _ = (match f_j[1]! with | .var v => v | _ => "") := h_var_j.symm
                  exact absurd this h_vars_ne
                · -- k ≠ f[1]!.value, so insertion doesn't affect k
                  exact h_in
              have h_fuel' : hyps.size - (i+1) = fuel' := by omega
              -- Need to show the keys assumption holds for the recursive call
              have h_keys' : ∀ (key : String) (val : Verify.Formula),
                  (σ_in.insert f[1]!.value (stack[off.1 + i]!))[key]? = some val →
                  ∃ (j : Nat) (_ : j < i+1) (hj_bound : j < hyps.size) (f_j : Verify.Formula) (lbl : String),
                    db.find? (hyps[j]'hj_bound) = some (.hyp false f_j lbl) ∧
                    f_j.size ≥ 2 ∧
                    (match f_j[1]! with | .var v_j => v_j | _ => "") = key := by
                intro key val h_key_in
                -- Key is either in σ_in or is the newly inserted key
                rw [Std.HashMap.getElem?_insert] at h_key_in
                split at h_key_in
                · -- Case: key == f[1]!.value (newly inserted)
                  rename_i h_key_eq
                  -- key came from float at index i
                  have h_key_is : key = f[1]!.value := by
                    rw [beq_iff_eq] at h_key_eq
                    exact h_key_eq.symm
                  have h_f_size : f.size ≥ 2 := float_has_size_ge_2 db hyps[i] f lbl h_success h_find
                  have h_f1_var : (match f[1]! with | .var v => v | _ => "") = f[1]!.value := by
                    have ⟨v_f, hv_f⟩ := float_has_var_at_1 db hyps[i] f lbl h_success h_find
                    exact (float_var_value_eq f v_f hv_f).symm
                  -- Need to show: (match f[1]! with | .var v_j => v_j | _ => "") = key
                  have : (match f[1]! with | .var v => v | _ => "") = key := by
                    rw [h_f1_var, ← h_key_is]
                  exact ⟨i, Nat.lt_succ_self i, hi_lt, f, lbl, h_find, h_f_size, this⟩
                · -- Case: key ≠ f[1]!.value (was already in σ_in)
                  have ⟨j, hj, hj_bound, f_j, lbl_j, h_find_j, h_size_j, h_var_j⟩ :=
                    h_keys_from_before_i key val h_key_in
                  exact ⟨j, Nat.lt_trans hj (Nat.lt_succ_self i), hj_bound, f_j, lbl_j, h_find_j, h_size_j, h_var_j⟩
              apply IH
              exact h_unique
              exact h_keys'
              exact h_in'
              exact h_ok
              exact h_fuel'
            · simp at h_ok
          · -- Essential: recurses with σ_in unchanged
            have h_step := Verify.DB.checkHyp_step_hyp_true db hyps stack off i σ_in f lbl hi_lt h_find
            rw [h_step] at h_ok
            split at h_ok
            · generalize h_eq : f.subst σ_in = subst_result at h_ok
              cases subst_result with
              | error e => simp at h_ok
              | ok s =>
                  simp at h_ok
                  split at h_ok
                  · -- σ_in unchanged, apply IH directly
                    have h_fuel' : hyps.size - (i+1) = fuel' := by omega
                    -- Keys assumption unchanged since σ_in unchanged
                    have h_keys' : ∀ (key : String) (val : Verify.Formula),
                        σ_in[key]? = some val →
                        ∃ (j : Nat) (_ : j < i+1) (hj_bound : j < hyps.size) (f_j : Verify.Formula) (lbl_j : String),
                          db.find? (hyps[j]'hj_bound) = some (.hyp false f_j lbl_j) ∧
                          f_j.size ≥ 2 ∧
                          (match f_j[1]! with | .var v_j => v_j | _ => "") = key := by
                      intro key val h_key
                      have ⟨j, hj, hj_bound, f_j, lbl_j, h_find_j, h_size_j, h_var_j⟩ := h_keys_from_before_i key val h_key
                      exact ⟨j, Nat.lt_trans hj (Nat.lt_succ_self i), hj_bound, f_j, lbl_j, h_find_j, h_size_j, h_var_j⟩
                    apply IH
                    exact h_unique
                    exact h_keys'
                    exact h_in
                    exact h_ok
                    exact h_fuel'
                  · simp at h_ok
            · simp at h_ok

/-- **Persistence Lemma 1**: Inserted values persist through checkHyp.

Derived as a corollary of checkHyp_preserves_keys. Requires uniqueness and
keys invariant assumptions. -/
theorem checkHyp_insert_persists
    {db : Verify.DB} {hyps : Array String} {stack : Array Verify.Formula}
    {off : {off : Nat // off + hyps.size = stack.size}}
    {i : Nat} {σ_in σ_out : Std.HashMap String Verify.Formula}
    {k : String} {v : Verify.Formula}
    (h_success : db.error? = none)
    (h_unique : ∀ (i j : Nat) (hi : i < hyps.size) (hj : j < hyps.size),
        i ≠ j →
        ∀ (fi fj : Verify.Formula) (lbli lblj : String),
          db.find? hyps[i] = some (.hyp false fi lbli) →
          db.find? hyps[j] = some (.hyp false fj lblj) →
          fi.size ≥ 2 → fj.size ≥ 2 →
          let vi := match fi[1]! with | .var v => v | _ => ""
          let vj := match fj[1]! with | .var v => v | _ => ""
          vi ≠ vj)
    (h_keys_from_before_i : ∀ (key : String) (val : Verify.Formula),
        (σ_in.insert k v)[key]? = some val →
        ∃ (j : Nat) (hj : j < i) (hj_bound : j < hyps.size) (f : Verify.Formula) (lbl : String),
          db.find? (hyps[j]'hj_bound) = some (.hyp false f lbl) ∧
          f.size ≥ 2 ∧
          (match f[1]! with | .var v => v | _ => "") = key)
    (h_ok : db.checkHyp hyps stack off i (σ_in.insert k v) = Except.ok σ_out) :
    σ_out[k]? = some v := by
  -- The inserted key is in (σ_in.insert k v)
  have h_in : (σ_in.insert k v)[k]? = some v := Std.HashMap.getElem?_insert_self
  -- Apply checkHyp_preserves_keys!
  exact checkHyp_preserves_keys h_success h_unique h_keys_from_before_i h_in h_ok

/-- Helper: substStep preserves equality when HashMap lookups agree -/
theorem Formula.substStep_preserved
    {σ_in σ_out : Std.HashMap String Verify.Formula}
    (h_preserve : ∀ (v : String), (σ_in[v]? : Option Verify.Formula) = σ_out[v]?)
    (acc : Verify.Formula) (s : Verify.Sym) :
    Verify.Formula.substStep σ_in acc s = Verify.Formula.substStep σ_out acc s := by
  unfold Verify.Formula.substStep
  cases s with
  | const c => rfl
  | var v =>
    simp only
    rw [h_preserve v]

/-- **Corollary**: Formula.subst is preserved if the HashMap is preserved.

Since Formula.subst only reads from the HashMap, if all variables in f
map to the same values in σ_in and σ_out, then substitution gives the same result. -/
theorem subst_preserved_by_keys
    {f : Verify.Formula} {σ_in σ_out : Std.HashMap String Verify.Formula}
    (h_preserve : ∀ (v : String), (σ_in[v]? : Option Verify.Formula) = σ_out[v]?) :
    f.subst σ_in = f.subst σ_out := by
  unfold Verify.Formula.subst
  -- f.foldlM (substStep σ_in) #[] = f.foldlM (substStep σ_out) #[]
  -- Since substStep is equal for all inputs (by substStep_preserved),
  -- the foldlM results should be equal
  congr 1
  funext acc s
  exact Formula.substStep_preserved h_preserve acc s

end Metamath.HashMapLemmas