/-
Helper lemmas for Metamath kernel verification.

This module contains kernel-specific helpers and re-exports array/list
infrastructure from Metamath.ArrayListExt.

After Batteries 4.24.0 upgrade (November 2025):
- Array/List infrastructure centralized in ArrayListExt.lean
- KernelExtras focuses on kernel-specific helpers
-/

import Metamath.Spec
import Metamath.Verify
import Metamath.ArrayListExt
import Std.Data.HashMap.Lemmas
import Batteries.Data.List.Lemmas
import Batteries.Data.Array.Lemmas

-- Re-export array/list infrastructure for backward compatibility
export List (dropLastN dropLastN_eq_take take_eq_dropLastN)
export List (mapM_length_option foldl_and_eq_true foldl_all₂ mapM_some_of_mem getElem!_idxOf)
export KernelExtras.List (mapM_get_some list_mapM_append list_mapM_dropLastN_of_mapM_some filterMap_after_mapM_eq)
export Array (getElem!_toList toList_get getElem!_mem_toList getElem!_of_getElem?_eq_some)
export Array (toList_extract_take toList_extract_dropLastN shrink_toList window_toList_map)

/-! ## Except monad peeling helpers (for stepAssert bind chain navigation) -/

namespace Except

@[simp] theorem bind_ok_iff {ε α β}
  {x : Except ε α} {f : α → Except ε β} {y : β} :
  x.bind f = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x <;> simp [Except.bind]

/-- Repeatedly apply `Except.bind_ok_iff` to walk to the final `pure`. -/
theorem ok_of_chain {ε α} :
  (∀ {β} (x : Except ε β) {f : β → Except ε α} {y},
     x.bind f = .ok y → ∃ b, x = .ok b ∧ f b = .ok y) := by
  intro β x f y h; exact (Except.bind_ok_iff).1 h

end Except

namespace KernelExtras

/-- Pair pattern eta-reduction for λ-normalization.

This eliminates eta-expansion issues between different lambda representations:
- `(fun p : α × β => f p.1 p.2)` (projection form)
- `(fun (a, b) => f a b)` (pattern matching form)

Used throughout checkHyp proofs for allM/match alignment.
-/
@[simp] theorem pair_eta₂ {α β γ} (f : α → β → γ) :
  (fun p : α × β => f p.1 p.2) = (fun (a, b) => f a b) := rfl

/-! ## Arithmetic helpers for offset calculations -/

theorem off_def_of_sum_eq {off k n : Nat} (h : off + k = n) : off = n - k := by
  have := congrArg (fun t => t - k) h
  simp [Nat.add_sub_cancel] at this
  exact this

theorem off_le_size {off k n : Nat} (h : off + k = n) : off ≤ n := by
  omega

/-! ## Array fold lemmas -/

/-- Array.foldlM equals List.foldlM on the underlying list.

This theorem unlocks Phase-7 induction by converting array folds to list folds,
enabling standard list induction patterns.

**Proof strategy:** Array.foldlM is defined in terms of iteration over the
array's range, which corresponds to folding over the list representation.
-/
theorem Array.foldlM_toList_eq
  {α β ε} (f : β → α → Except ε β) (a : Array α) (b : β) :
  a.foldlM f b = (a.toList.foldlM f b) := by
  rw [← Array.foldlM_toList]

/-! ## Fold Induction Lemmas (GPT-5 Pro contribution)

These lemmas provide reusable fold-induction patterns for proving that
properties are preserved across foldlM operations.
-/

variable {α β ε : Type}

/-- List-level: if `P` holds at the start and each `f`-step preserves `P`,
    then `foldlM f xs init` returns a state again satisfying `P`.

This is the workhorse for Phase 7 fold proofs. -/
theorem list_foldlM_preserves
    (P : β → Prop) (f : β → α → Except ε β)
    (xs : List α) (init res : β)
    (h0 : P init)
    (hstep : ∀ b a b', f b a = Except.ok b' → P b → P b')
    (hfold : xs.foldlM f init = Except.ok res) :
    P res := by
  revert init h0
  induction xs with
  | nil =>
      intro init h0 hfold
      -- nil case: foldlM returns init immediately (pure init = Except.ok res)
      simp only [List.foldlM] at hfold
      cases hfold
      exact h0
  | cons a xs ih =>
      intro init h0 hfold
      -- cons case: one step then recurse
      simp only [List.foldlM] at hfold
      cases hfa : f init a with
      | error e =>
          -- impossible: the fold returned ok
          rw [hfa] at hfold
          contradiction
      | ok init' =>
          -- one step preserves P, then recurse
          rw [hfa] at hfold
          have hP' : P init' := hstep init a init' hfa h0
          apply ih
          · exact hP'
          · exact hfold

/-- Array-level wrapper: use the `toList` bridge to reuse the list proof.

This is the main theorem used in Phase 7's `fold_maintains_provable`. -/
theorem array_foldlM_preserves
    (P : β → Prop) (f : β → α → Except ε β)
    (arr : Array α) (init res : β)
    (h0 : P init)
    (hstep : ∀ b a b', f b a = Except.ok b' → P b → P b')
    (hfold : arr.foldlM f init = Except.ok res) :
    P res := by
  -- bridge to list using the axiom
  have h_list : arr.toList.foldlM f init = Except.ok res := by
    have := Array.foldlM_toList_eq f arr init
    rw [←this]
    exact hfold
  exact list_foldlM_preserves P f arr.toList init res h0 hstep h_list

/-! ## Array fold head preservation

Micro-lemmas for substitution: Show that folding with Array.push preserves
the head element at index 0, which is critical for substitution correctness.
-/

-- Array.getElem!_push_lt is defined in ArrayListExt.lean
-- It establishes that Array.push preserves access to earlier indices

/-- Foldl with push preserves the head element.
    Key micro-lemma for substitution: When folding a list using Array.push,
    the element at index 0 is never modified since we only append to the end.

    **Precondition**: Requires a.size > 0 (array is non-empty).
    This holds in practice since formulas are well-formed and contain at least
    one symbol (guaranteed by WellFormedFormula).

    This is used in Formula.substStep to show that when substituting a variable,
    the constant at position 0 is preserved even after appending expansion symbols. -/
theorem foldl_from_pos1_preserves_head {a : Metamath.Verify.Formula} (suffix : List Metamath.Verify.Sym)
    (h_nonempty : 0 < a.size) :
    (suffix.foldl (fun acc x => acc.push x) a)[0]! = a[0]! := by
  -- List.foldl with Array.push only appends, so position 0 is never touched
  induction suffix generalizing a with
  | nil =>
    -- No processing: result equals input
    rfl
  | cons x xs ih =>
    -- After one push, head is still at position 0
    simp only [List.foldl_cons]
    -- Goal is now: (List.foldl (fun acc y => acc.push y) (a.push x) xs)[0]! = a[0]!
    -- We need to apply IH with (a.push x) as the new accumulator
    -- But first show that (a.push x)[0]! = a[0]!
    have h_head : (a.push x)[0]! = a[0]! := by
      -- Array.push appends at the end, so index 0 is unchanged
      apply Array.getElem!_push_lt h_nonempty
    -- Now show (a.push x) is also non-empty for the inductive hypothesis
    have h_push_nonempty : 0 < (a.push x).size := by
      simp [Array.size_push]
    -- Now the IH gives us:
    -- (List.foldl (fun acc y => acc.push y) (a.push x) xs)[0]! = (a.push x)[0]!
    have ih_applied : (List.foldl (fun acc y => acc.push y) (a.push x) xs)[0]! = (a.push x)[0]! :=
      @ih (a.push x) h_push_nonempty
    rw [← h_head]
    exact ih_applied

/-! ## HashMap Lemmas

Standard HashMap insertion and lookup properties.
These replace the axiomatized versions in KernelClean.lean.
-/

namespace HashMap

variable {α : Type _} [BEq α] [Hashable α]

/-- Looking up the key just inserted returns that value.

Standard HashMap property: insert followed by lookup of the same key
returns the inserted value.

We rely on `Std.HashMap.getElem?_insert_self`, which is proven for any
`EquivBEq`/`LawfulHashable` key type.
-/
@[simp] theorem find?_insert_self (m : Std.HashMap α β) (k : α) (v : β)
    [EquivBEq α] [LawfulHashable α] [LawfulBEq α] :
    (m.insert k v)[k]? = some v := by
  simpa using (Std.HashMap.getElem?_insert_self (m := m) (k := k) (v := v))

/-- Looking up a different key is unchanged by insert.

Standard HashMap property: inserting at key k doesn't affect
lookups at other keys k'.

**Proof strategy**: Use the general `getElem?_insert` lemma and the fact
that `k == k'` would imply `k = k'` for lawful `BEq`, contradicting `h`.
-/
@[simp] theorem find?_insert_ne (m : Std.HashMap α β)
    {k k' : α} (h : k' ≠ k) (v : β)
    [EquivBEq α] [LawfulHashable α] [LawfulBEq α] :
    (m.insert k v)[k']? = m[k']? := by
  classical
  have hbranch := Std.HashMap.getElem?_insert (m := m) (k := k) (a := k') (v := v)
  cases hbeq : (k == k') <;> try simp [Std.HashMap.getElem?_insert, hbeq] at hbranch
  · -- beq returns false, so lookup is unchanged
    simpa [Std.HashMap.getElem?_insert, hbeq] using hbranch
  · -- beq returns true, contradicting key inequality
    have hk' : k = k' := LawfulBEq.eq_of_beq (a := k) (b := k') (by simpa [hbeq])
    exact (h hk'.symm).elim

end HashMap

end KernelExtras
