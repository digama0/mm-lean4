/-
Array and List infrastructure lemmas for Metamath verification.

This module centralizes array/list bridge theorems and infrastructure axioms.
These are standard library properties that should eventually be proven or
migrated to Batteries.

After Lean 4.24.0 + Batteries v4.24.0 upgrade (November 2025):
- Several axioms were eliminated using Batteries-provided lemmas
- Remaining axioms have documented proof strategies in AXIOMS.md
-/

import Batteries.Data.List.Lemmas
import Batteries.Data.Array.Lemmas

/-! ## List helpers -/

namespace List

/-- Drop the last n elements from a list.
    Equivalent to taking the first (length - n) elements.
    Note: The builtin List.dropLast (no argument) drops exactly 1 element.
    This version `dropLastN` takes n : Nat and drops the last n elements.
-/
def dropLastN (xs : List α) (n : Nat) : List α :=
  xs.take (xs.length - n)

/-- dropLastN n is equivalent to take (length - n). -/
@[simp] theorem dropLastN_eq_take (xs : List α) (n : Nat) :
  xs.dropLastN n = xs.take (xs.length - n) := rfl

/-- take n is equivalent to dropLastN (length - n). -/
theorem take_eq_dropLastN (xs : List α) (n : Nat) (h : n ≤ xs.length) :
  xs.take n = xs.dropLastN (xs.length - n) := by
  rw [dropLastN_eq_take]
  congr 1
  omega

/-! ### List.mapM axioms

These are fundamental Option.mapM properties. Proofs encounter mapM.loop
expansion issues - the monadic bind structure doesn't simplify cleanly.

See AXIOMS.md for documented proof strategies.
-/

/-- If mapM succeeds, the result has the same length as the input.

This is a fundamental property of Option.mapM: it either fails (returns none)
or produces exactly one output element for each input element.

Proven using a helper lemma about mapM.loop that tracks the accumulator.
-/
private theorem mapM_loop_length {α β} (f : α → Option β) :
  ∀ (xs : List α) (acc : List β) (ys : List β),
    List.mapM.loop f xs acc = some ys →
    ys.length = acc.length + xs.length := by
  intro xs
  induction xs with
  | nil =>
    intro acc ys h
    simp [List.mapM.loop] at h
    cases h
    simp
  | cons a xs' ih =>
    intro acc ys h
    simp [List.mapM.loop] at h
    cases hfa : f a with
    | none =>
      simp [hfa] at h
    | some b =>
      simp [hfa] at h
      have := ih (b :: acc) ys h
      simp at this ⊢
      omega

theorem mapM_length_option {α β : Type _} (f : α → Option β) :
  ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length := by
  intro xs ys h
  unfold List.mapM at h
  have := mapM_loop_length f xs [] ys h
  simp at this
  exact this

/-- Helper: folding && with false always gives false. -/
private theorem foldl_and_false {α} (xs : List α) (p : α → Bool) :
    xs.foldl (fun b x => b && p x) false = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.foldl, ih]

/-- Folding && over a list returns true iff all elements satisfy the predicate.

Standard fold property: folding && starting from true returns true iff every
element contributes true (since true && true = true, true && false = false).
-/
@[simp] theorem foldl_and_eq_true {α} {p : α → Bool} (xs : List α) :
    xs.foldl (fun b x => b && p x) true = true ↔
    ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    rw [List.foldl]
    constructor
    · intro h y hy
      cases hy with
      | head =>
        cases hpx : p x
        · simp [hpx, foldl_and_false] at h
        · rfl
      | tail _ hmem =>
        cases hpx : p x
        · simp [hpx, foldl_and_false] at h
        · simp [hpx] at h
          exact ih.mp h y hmem
    · intro h
      have hx : p x = true := h x (List.mem_cons_self ..)
      simp [hx]
      apply ih.mpr
      intro y hy
      exact h y (List.mem_cons_of_mem x hy)

/-- Nested fold starting with false accumulator always returns false. -/
private theorem foldl_nested_false {α β} (xs : List α) (ys : List β) (p : α → β → Bool) :
    xs.foldl (fun b x => ys.foldl (fun b' y => b' && p x y) b) false = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.foldl, foldl_and_false, ih]

/-- Nested fold with && returns true iff predicate holds for all pairs.

Extension of foldl_and_eq_true to two lists. The nested fold checks p x y
for every pair (x,y) where x ∈ xs and y ∈ ys, returning true iff all checks pass.
-/
theorem foldl_all₂ {α β} (xs : List α) (ys : List β) (p : α → β → Bool) :
  (xs.foldl (fun b x => ys.foldl (fun b' y => b' && p x y) b) true = true)
  ↔ (∀ x ∈ xs, ∀ y ∈ ys, p x y = true) := by
  induction xs with
  | nil =>
    simp [List.foldl]
  | cons x xs ih =>
    rw [List.foldl]
    constructor
    · -- Forward direction: fold succeeds → all pairs satisfy p
      intro h z hz w hw
      -- First extract that inner fold must be true
      have h_inner : ys.foldl (fun b' y => b' && p x y) true = true := by
        match h_eq : ys.foldl (fun b' y => b' && p x y) true with
        | true => rfl
        | false =>
          -- Contradiction: h_eq = false implies outer fold = false
          rw [h_eq, foldl_nested_false] at h
          nomatch h
      cases hz with
      | head =>
        -- z = x: use h_inner
        exact (foldl_and_eq_true ys).mp h_inner w hw
      | tail _ hmem =>
        -- z ∈ xs: rewrite h using h_inner, then apply IH
        rw [h_inner] at h
        exact ih.mp h z hmem w hw
    · -- Backward direction: all pairs satisfy p → fold succeeds
      intro h
      -- First show inner fold = true
      have h_inner : ys.foldl (fun b' y => b' && p x y) true = true := by
        apply (foldl_and_eq_true ys).mpr
        intro w hw
        exact h x (List.mem_cons_self ..) w hw
      -- Rewrite goal using h_inner
      rw [h_inner]
      -- Now use IH
      apply ih.mpr
      intro z hz w hw
      exact h z (List.mem_cons_of_mem x hz) w hw

/-- If mapM succeeds on a list, then f succeeds on each element.

Fundamental Option.mapM property: the monadic bind only succeeds if f succeeds
on every element. If mapM returns some ys, then every input element must have
successfully converted.

Proven using a helper lemma about mapM.loop that handles membership.
-/
private theorem mapM_loop_some_of_mem {α β} (f : α → Option β) :
  ∀ (xs : List α) (acc : List β) (ys : List β) (x : α),
    List.mapM.loop f xs acc = some ys →
    x ∈ xs →
    ∃ b, f x = some b := by
  intro xs
  induction xs with
  | nil =>
    intro acc ys x h hmem
    cases hmem
  | cons a xs' ih =>
    intro acc ys x h hmem
    simp [List.mapM.loop] at h
    cases hfa : f a with
    | none =>
      simp [hfa] at h
    | some b =>
      simp [hfa] at h
      cases hmem with
      | head =>
        -- x = a, so f x = f a = some b
        exact ⟨b, hfa⟩
      | tail _ hmem' =>
        -- x ∈ xs', use IH
        exact ih (b :: acc) ys x h hmem'

theorem mapM_some_of_mem {α β} (f : α → Option β) {xs : List α} {ys : List β} {x : α}
    (h : xs.mapM f = some ys) (hx : x ∈ xs) : ∃ b, f x = some b := by
  unfold List.mapM at h
  exact mapM_loop_some_of_mem f xs [] ys x h hx

/-- If an element is in a list (with BEq), then indexing by idxOf retrieves that element.

Requires `LawfulBEq α` to bridge between boolean equality `==` (used by `idxOf`)
and propositional equality `=` (used in the membership hypothesis).

The proof uses:
1. `List.idxOf_lt_length_iff`: converts membership to valid index
2. `List.findIdx_getElem`: shows the predicate holds at the found index
3. `LawfulBEq.eq_of_beq`: upgrades boolean to propositional equality
4. `getElem!_pos`: converts panic-safe indexing to bounded indexing
-/
theorem getElem!_idxOf
  {α : Type _} [BEq α] [LawfulBEq α] [Inhabited α]
  {xs : List α} {x : α} (hx : x ∈ xs) :
  xs[xs.idxOf x]! = x := by
  -- 1) Bound: idxOf x is a valid index when x ∈ xs
  have hi : xs.idxOf x < xs.length :=
    List.idxOf_lt_length_iff.mpr hx

  -- 2) At the found index, the BEq-predicate holds
  --    Note: idxOf x is defined via findIdx (· == x)
  have hbeq : (xs.get ⟨xs.idxOf x, hi⟩ == x) = true := by
    show (xs.get ⟨xs.findIdx (· == x), hi⟩ == x) = true
    exact @List.findIdx_getElem _ (· == x) xs hi

  -- 3) Upgrade BEq to propositional equality
  have hget : xs.get ⟨xs.idxOf x, hi⟩ = x :=
    LawfulBEq.eq_of_beq hbeq

  -- 4) Bridge xs[i]! to xs.get
  --    xs[i]! is defined as: getElem! xs i = if h : i < xs.length then xs[i] else default
  --    Since we have hi : xs.idxOf x < xs.length, the if-then-else evaluates to xs[i]
  --    Then xs[i] is definitionally equal to xs.get ⟨i, hi⟩
  show xs[xs.idxOf x]! = x
  unfold getElem! instGetElem?NatLtLength
  simp [hi]
  -- Now goal is: xs[idxOf x xs] = x
  -- and hget says: xs.get ⟨idxOf x xs, hi⟩ = x
  -- xs[i] is definitionally xs.get ⟨i, proof⟩
  exact hget

/-! ### forIn bridges (for loop equivalence proofs)

Note: Lean 4.24.0 stdlib provides all the lemmas needed for proving that
imperative `for...in` loops equal functional recursion. We use those directly.

**Available stdlib lemmas:**

From Init/Data/List/Monadic.lean:
- `List.forIn_yield_eq_foldl`: forIn (yield-only) equals foldl for Lists
- `List.idRun_forIn_yield_eq_foldl`: Id.run version

From Init/Data/Array/Lemmas.lean:
- `Array.forIn_toList`: forIn over Array equals forIn over toList
- `Array.forIn_yield_eq_foldlM`: Array forIn (yield-only) equals foldlM

**Proof pattern for loop = recursion equivalence:**
1. Use `Array.forIn_toList` to convert Array iteration to List iteration
2. Use `List.forIn_yield_eq_foldl` to show forIn = foldl
3. Prove recursive function = foldl by induction
4. Conclude both sides equal by transitivity
-/

/-! ### Additional forIn bridges for floatCheckLoop proof -/

namespace ArrayListExt

/-! ### ForIn to foldl bridge for DBCaseAnalysis

**Kevin Buzzard's Discovery (2025-11-17):**

The Lean 4 standard library already has `List.idRun_forIn_yield_eq_foldl` which proves
that yield-only forIn loops in the Id monad equal foldl! The type signature is:

```lean
List.idRun_forIn_yield_eq_foldl {α β} (l : List α) (f : α → β → Id β) (init : β) :
  (forIn l init fun a b => ForInStep.yield <$> f a b).run =
    foldl (fun b a => (f a b).run) init l
```

Our use case is slightly different: we have `fun a s => pure (ForInStep.yield (step s a))`
instead of `fun a b => ForInStep.yield <$> f a b`. These are equivalent when `f = pure ∘ step`,
but the proof requires funext + simp to connect them.

For now, we use a sorry with full documentation. The alternative approaches:
1. **Rewrite our code** to match stdlib's expected form (changes DBCaseAnalysis)
2. **Prove the adapter** lemma (requires careful funext reasoning)
3. **Accept the sorry** as "uses stdlib under the hood" (pragmatic choice)

Kevin's lesson: *Always check what the stdlib provides before rolling your own!*
-/

namespace Array

/-- In `Id`, array forIn with yield-only body equals List foldl.

**Note**: The Lean stdlib has `List.idRun_forIn_yield_eq_foldl` which almost proves this.
We use a documented sorry here rather than complicate the DBCaseAnalysis code. -/
theorem idRun_forIn_yield_eq_foldl
    {α β} (arr : Array α) (init : β) (step : β → α → β) :
    Id.run (forIn arr init (fun a s => pure (ForInStep.yield (step s a)))) =
      (arr.toList).foldl step init := by
  -- Apply stdlib List.idRun_forIn_yield_eq_foldl by first unfolding to List.forIn
  -- Array.forIn reduces to List.forIn on toList
  rw [←Array.forIn_toList]

  -- Show that our forIn body matches the stdlib pattern
  have h : (fun a s => pure (ForInStep.yield (step s a))) =
           (fun a s => (ForInStep.yield <$> pure (step s a) : Id (ForInStep β))) := by
    funext a s
    rfl
  simp only [h]

  -- Apply List.idRun_forIn_yield_eq_foldl with f = fun a b => pure (step b a)
  rw [List.idRun_forIn_yield_eq_foldl arr.toList (fun a b => pure (step b a)) init]

  -- Simplify: (pure (step b a)).run = step b a in Id monad
  -- In Id, pure is identity, so this completes the proof
  simp [Id.run]
  congr 1

end Array

end ArrayListExt

end List

/-! ### Namespaced List.mapM axioms

These live in a separate namespace to avoid clutter in the List namespace.
They represent more specialized mapM properties.
-/

namespace KernelExtras.List

/-- Head of `drop`: the element at index `i` is exactly the head of `xs.drop i`. -/
private theorem drop_eq_head_tail'
  {α} (xs : List α) (i : Nat) (h : i < xs.length) :
  xs.drop i = xs.get ⟨i, h⟩ :: xs.drop (i+1) := by
  revert xs
  induction i with
  | zero =>
      intro xs h
      cases xs with
      | nil => cases h
      | cons x xs => rfl
  | succ i ih =>
      intro xs h
      cases xs with
      | nil => cases h
      | cons hd tl =>
        have : i < tl.length := Nat.lt_of_succ_lt_succ h
        simpa using ih tl this

/-- Option `bind` deconstruction: a convenience fact. -/
@[simp] private theorem Option.bind_eq_some {α β} {x : Option α} {f : α → Option β} {y : β} :
  x.bind f = some y ↔ ∃ a, x = some a ∧ f a = some y := by
  cases x <;> simp

/-- Helper lemma for mapM_get_some that handles the cons case after case splits.
Extracted to avoid Lean 4.24.0 parser bug with deeply nested case splits.
Uses term mode to completely avoid the tactic parser.

COMPLETED: All 4 list indexing lemmas have been filled in using `subst` and explicit
dependent type handling. The proof is now complete.
-/
private theorem mapM_get_some_cons_helper {α β} (f : α → Option β)
    (x : α) (xs : List α)
    (ih : ∀ (ys : List β),
      List.mapM f xs = some ys → ∀ (i : Fin xs.length) (h_len : i.val < ys.length),
      ∃ b, f xs[i] = some b ∧ ys[i.val]'h_len = b)
    (b : β) (hfx : f x = some b)
    (ys' : List β) (htail : List.mapM f xs = some ys')
    (ys : List β) (hcons : b :: ys' = ys)
    (i : Fin (x :: xs).length) (hlen : i.val < ys.length) :
    ∃ b, f (x :: xs)[i] = some b ∧ ys[i.val]'hlen = b :=
  if h : i.val = 0 then
    -- i.val = 0, so (x::xs)[i] = x and ys[0] = b
    have i_eq : i = ⟨0, by simp⟩ := Fin.ext h
    ⟨b, by
      -- f((x::xs)[i]) = f(x) = some b
      subst i_eq
      simp [hfx],
     by
      -- ys[0] = b
      subst i_eq hcons
      rfl⟩
  else
    have h_pos : 0 < i.val := Nat.pos_of_ne_zero h
    have ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h_pos
    have hn : i.val = k + 1 := by omega
    have n_lt : k < xs.length := by have := i.isLt; simp [hn] at this ⊢; exact this
    have n_lt_ys' : k < ys'.length := by
      have : i.val < ys.length := hlen
      rw [hn, ← hcons] at this
      simp at this
      exact this
    let ⟨b', hf', hy'⟩ := ih ys' htail ⟨k, n_lt⟩ n_lt_ys'
    -- i.val = k+1, so (x::xs)[i] = xs[k] and ys[i.val] = ys'[k]
    ⟨b', by
      -- f((x::xs)[i]) = f(xs[k]) = some b'
      have i_succ : i.val = k + 1 := hn
      have h1 : (x :: xs)[i] = (x :: xs)[i.val]'i.isLt := rfl
      have h2 : (x :: xs)[i.val]'i.isLt = xs[k]'n_lt := by simp [i_succ]
      rw [h1, h2]
      exact hf',
     by
      -- ys[i.val] = ys'[k] = b'
      subst hcons
      have : i.val = k + 1 := hn
      simp [this, hy']⟩

/-- If mapM succeeds, then indexing the result corresponds to mapping the input.

For any valid index i, if xs.mapM f = some ys, then ys[i] is the result of
applying f to xs[i].

COMPLETED: The "unknown tactic" error was caused by Lean 4.24.0 parser bug
with deeply nested case splits. Fixed by:
1. Extracting final case analysis into `mapM_get_some_cons_helper`
2. Using term-mode `if-then-else` instead of tactic-mode case splits
3. Avoiding any `by_cases`, `cases`, or `match` in deeply nested tactic contexts
4. Using `subst` and explicit dependent type handling for index equality proofs

This proof is now fully complete. The only remaining `sorry` in this file is in
`getElem!_idxOf` which requires LawfulBEq lemmas about `List.findIdx.go`.
-/
theorem mapM_get_some {α β} (f : α → Option β)
    (xs : List α) (ys : List β)
    (h : xs.mapM f = some ys)
    (i : Fin xs.length) (h_len : i.val < ys.length) :
  ∃ b, f xs[i] = some b ∧ ys[i.val]'h_len = b := by
  revert i h_len ys
  induction xs with
  | nil =>
    intro ys h i hlen
    exact Fin.elim0 i
  | cons x xs ih =>
    intro ys h i hlen
    rw [List.mapM_cons] at h
    cases hfx : f x with
    | none =>
      simp [hfx] at h
    | some b =>
      simp [hfx] at h
      cases htail : xs.mapM f with
      | none =>
        simp [htail] at h
      | some ys' =>
        simp [htail] at h
        exact mapM_get_some_cons_helper f x xs ih b hfx ys' htail ys h i hlen

/-- MapM preserves append structure.

If mapM succeeds on xs ++ ys, it's equivalent to mapping xs and ys separately
and concatenating the results.

Provided directly by Batteries 4.24.0 as List.mapM_append for LawfulMonad.
Option is a LawfulMonad, so this is just a direct application.
-/
abbrev list_mapM_append {α β} (f : α → Option β) (xs ys : List α) :=
  @List.mapM_append Option α β _ _ (f := f) (l₁ := xs) (l₂ := ys)

/-- MapM preserves dropLastN operation.

If mapM succeeds on xs, then mapM on xs.dropLastN n also succeeds and produces
ys.dropLastN n.

Proven by decomposing xs using take/drop, applying mapM_append, and showing
that the first part corresponds to dropLastN.
-/
theorem list_mapM_dropLastN_of_mapM_some {α β} (f : α → Option β)
    {xs : List α} {ys : List β} (h : xs.mapM f = some ys) (k : Nat) :
    (xs.dropLastN k).mapM f = some (ys.dropLastN k) := by
  unfold List.dropLastN
  have hlen := @List.mapM_length_option α β f xs ys h
  rw [hlen]
  -- Strategy: rewrite xs as xs.take n ++ xs.drop n
  let n := xs.length - k
  have split_xs : xs = xs.take n ++ xs.drop n := (List.take_append_drop n xs).symm
  rw [split_xs] at h
  -- Now use mapM_append to decompose h
  rw [List.mapM_append] at h
  -- h now says: (xs.take n).mapM f >>= ... = some ys
  -- We need to extract that (xs.take n).mapM f = some (ys.take n)
  simp [pure] at h
  -- h : bind (xs.take n).mapM f (...) = some ys
  cases hxs_take : (xs.take n).mapM f with
  | none =>
    simp [hxs_take] at h
  | some ys₁ =>
    simp [hxs_take] at h
    cases hxs_drop : (xs.drop n).mapM f with
    | none =>
      simp [hxs_drop] at h
    | some ys₂ =>
      simp [hxs_drop] at h
      -- h : some (ys₁ ++ ys₂) = some ys
      cases h
      -- ys = ys₁ ++ ys₂
      -- Need to show ys₁ = ys.take n
      have hlen₁ := @List.mapM_length_option α β f (xs.take n) ys₁ hxs_take
      have hlen₂ := @List.mapM_length_option α β f (xs.drop n) ys₂ hxs_drop
      -- ys₁.length = (xs.take n).length
      simp at hlen₁ hlen₂
      -- Show that ys₁.length = xs.length - k (which is n)
      have n_le : n ≤ xs.length := Nat.sub_le xs.length k
      have hlen₁' : ys₁.length = n := by
        rw [hlen₁]
        exact Nat.min_eq_left n_le
      -- Now show (ys₁ ++ ys₂).take (xs.length - k) = ys₁
      have take_eq : (ys₁ ++ ys₂).take ys₁.length = ys₁ := by
        induction ys₁ with
        | nil => rfl
        | cons y ys₁' ih => simp
      -- Combine: hlen₁' : ys₁.length = n = xs.length - k
      congr 1
      symm
      show List.take (xs.length - k) (ys₁ ++ ys₂) = ys₁
      calc List.take (xs.length - k) (ys₁ ++ ys₂)
          _ = List.take n (ys₁ ++ ys₂) := by rfl
          _ = List.take ys₁.length (ys₁ ++ ys₂) := by rw [← hlen₁']
          _ = ys₁ := take_eq

/-- FilterMap after mapM can be fused.

If mapM succeeds and produces ys, then filtering ys with g is equivalent
to filtering xs with the composed operation (f then g).

Proven using a helper lemma about mapM.loop that tracks the accumulator.
The key insight: mapM.loop accumulates results in reverse, so we track
filterMap through this reverse accumulation.
-/
private theorem mapM_loop_filterMap_eq {α β γ} (f : α → Option β) (p : β → Option γ) :
  ∀ (xs : List α) (acc : List β) (ys : List β),
    List.mapM.loop f xs acc = some ys →
    ys.filterMap p = acc.reverse.filterMap p ++ xs.filterMap (fun a => Option.bind (f a) p) := by
  intro xs
  induction xs with
  | nil =>
    intro acc ys h
    simp [List.mapM.loop] at h
    cases h
    simp
  | cons a xs' ih =>
    intro acc ys h
    simp [List.mapM.loop] at h
    cases hfa : f a with
    | none =>
      rw [hfa] at h
      simp at h
    | some b =>
      rw [hfa] at h
      simp at h
      have ih_result := ih (b :: acc) ys h
      rw [ih_result]
      rw [List.reverse_cons]
      rw [List.filterMap_append]
      rw [List.filterMap]
      cases hpb : p b with
      | none =>
        simp [List.filterMap]
        simp [hfa, Option.bind, hpb]
      | some c =>
        simp [List.filterMap]
        simp [hfa, Option.bind, hpb]

theorem filterMap_after_mapM_eq {α β γ}
    (f : α → Option β) (p : β → Option γ)
    {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) :
  xs.filterMap (fun a => Option.bind (f a) p) = ys.filterMap p := by
  unfold List.mapM at h
  have helper := mapM_loop_filterMap_eq f p xs [] ys h
  simp at helper
  exact helper.symm

end KernelExtras.List

/-! ## Array helpers -/

namespace Array

/-- Array.toList preserves getElem! access (panic-safe version).

If i < a.size, then a[i]! in the original array equals a.toList[i]! in the list.

Uses Batteries 4.24's `getElem!_pos` lemma which says c[i]! = c[i] when i is valid.
-/
theorem getElem!_toList {α} [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
  a[i]! = a.toList[i]! := by
  simp [getElem!_pos, h]

/-- Array.toList preserves indexed get access.

For any valid index i, a.toList.get gives the same element as a[i].
This is definitional equality.
-/
theorem toList_get {α} (a : Array α) (i : Nat) (h : i < a.size) :
  ∀ (h_len : i < a.toList.length), a.toList.get ⟨i, h_len⟩ = a[i] := by
  intro h_len
  rfl

/-- Elements accessed via getElem! are members of toList.

If i < a.size, then a[i]! is a member of a.toList.

Proven using getElem!_pos to convert to bounded access, then standard membership.
-/
theorem getElem!_mem_toList {α} [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
  a[i]! ∈ a.toList := by
  simp [getElem!_pos, h]

/-- Correspondence between get? and getElem!.

If a[i]? returns some x, then a[i]! equals x.
-/
theorem getElem!_of_getElem?_eq_some {α} [Inhabited α] (a : Array α) (i : Nat) (x : α)
  (h : a[i]? = some x) : a[i]! = x := by
  -- getElem? returns some x iff i < size and a[i] = x
  have ⟨hi, heq⟩ : ∃ h : i < a.size, a[i] = x := by
    simp [getElem?_def] at h
    exact h
  -- Directly use the bounds witness and equality
  simp [getElem!, Array.get!Internal, hi]
  exact heq

end Array

/-! ## Array push lemmas: getElem! preservation

These lemmas establish that Array.push preserves access to earlier indices.
This is foundational for list folding invariants.

Strategy: Use push_eq_append_singleton to reduce to Array.append, then apply
Array.getElem_append_left (from Batteries) which states that indexing into the
prefix of an append returns the prefix's element.
-/

namespace Array

/-- Array.getElem! at index i < arr.size is unchanged after push.

When pushing x to the end of array a, accessing index i (which is valid in the
original array) gives the same element. This is because push appends to the end,
and earlier indices remain unchanged.

**Batteries provides**: Array.getElem_push_lt (bounded getElem version)
  From ParserProofs.lean line 589:
    have h : (hyps.push l)[i] = hyps[i] := by simp only [Array.getElem_push_lt hi_old]

**We need to prove**: The unsafe getElem! version.
  The connection is via the definition: getElem! i = if h : i < size then getElem i ⟨h⟩ else default

**Proof strategy**:
1. Unfold getElem! on both sides
2. Show i < (a.push x).size using Array.size_push
3. Both sides now reduce to bounded getElem via the if-condition
4. Apply Array.getElem_push_lt to the bounded getElem
-/
theorem getElem!_push_lt {α : Type u} [Inhabited α] {a : Array α} {i : Nat} {x : α}
    (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  -- Use getElem!_pos to convert both sides from ! to bounded indexing
  have h_push : i < (a.push x).size := by
    simp only [Array.size_push]
    omega
  -- Proof by transitivity
  have step1 : (a.push x)[i]! = (a.push x)[i]'h_push := getElem!_pos ..
  have step2 : (a.push x)[i]'h_push = a[i]'h := Array.getElem_push_lt ..
  have step3 : a[i]'h = a[i]! := (getElem!_pos ..).symm
  exact step1.trans (step2.trans step3)

end Array

/-! ## Array extraction and window operations

These axioms bridge Array's extraction/window operations with List operations.
Many may be provable using Batteries 4.24.0 lemmas.
-/

namespace Array

-- NOTE: As of Batteries 4.24.0, Array.toList_push is provided by the library.
-- We no longer need a local definition. Import Batteries.Data.Array.Lemmas to use it.

/-- Extracting the first n elements and converting to list equals taking n elements.

Batteries 4.24.0 provides Array.toList_extract. This is a specialized version
for the common case of extract 0 n (take pattern).
-/
@[simp] theorem toList_extract_take {α} (a : Array α) (n : Nat) :
  (a.extract 0 n).toList = a.toList.take n := by
  rw [Array.toList_extract]
  simp [List.extract]

/-- Extracting a prefix while dropping the last k elements.

This operation is common in stack manipulation (pop k elements).
-/
theorem toList_extract_dropLastN {α} (a : Array α) (k : Nat) (h : k ≤ a.size) :
  (a.extract 0 (a.size - k)).toList = a.toList.dropLastN k := by
  -- Use toList_extract_take: (a.extract 0 n).toList = a.toList.take n
  rw [toList_extract_take]
  -- Now goal is: a.toList.take (a.size - k) = a.toList.dropLastN k
  -- Use dropLastN definition: dropLastN k = take (length - k)
  rw [List.dropLastN_eq_take]
  -- Goal: a.toList.take (a.size - k) = a.toList.take (a.toList.length - k)
  -- These are equal because a.size = a.toList.length (definitional)
  rfl

/-- Shrinking an array to size n equals taking the first n elements.

As of Batteries 4.24.0, Array.toList_shrink is provided directly.
We can use it without a local proof.
-/
@[simp] theorem shrink_toList {α} (a : Array α) (n : Nat) :
  (a.shrink n).toList = a.toList.take n :=
  Array.toList_shrink  -- Direct reference to Batteries theorem

/-- Mapping over a window of an array equals dropping, taking, and mapping.

Window operation: extract a slice [off, off+len) and map a function over it.
This is equivalent to dropping off elements, taking len elements, then mapping.
-/
theorem window_toList_map {α β} (a : Array α) (off len : Nat)
    (f : α → β) (h : off + len ≤ a.size) :
  (a.extract off (off + len)).toList.map f =
  ((a.toList.drop off).take len).map f := by
  -- Use toList_extract to convert extract to List.extract
  rw [Array.toList_extract]
  -- List.extract is defined as drop then take
  simp [List.extract]

end Array
