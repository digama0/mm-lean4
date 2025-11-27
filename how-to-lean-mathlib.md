# how-to-lean.md

*Lean 4 proof patterns for mathlib‑first projects (with batteries notes)* 

---

## 0. Scope and philosophy

This guide merges three earlier docs into a single “how to Lean” playbook:

* Batteries‑style core proof patterns (no mathlib needed)
* LeanHammer (ATP) integration
* Finset/combinatorics and graph‑theory patterns (mathlib‑heavy)

Assumptions:

* Lean 4
* **mathlib is available** and the default choice
* Some projects also use a **batteries‑only kernel**; where relevant this is called out explicitly, but the patterns are the same.

Use this as:

* A **pattern index** when you’re stuck
* A **coding style guide** for proofs
* A **high‑signal context** for LLM agents working on your Lean projects

---

## 1. Pattern index (“what do I use when…?”)

When your goal involves… jump to:

* **Complex if / match / control flow**
  → §4 (If/Bool/Match) and §4.4 (Success condition extraction) and §4.5 (Control flow with match+if)
* **Boolean conditions and ADT predicates (`isVar`, etc.)**
  → §4.2 (Bool ↔ Prop for ADTs)
* **Equality vs `==`, HashMaps, keys**
  → §5 (BEq & HashMap)
* **Arrays / indices / `arr[i]!` vs `arr[i]`**
  → §6 (Arrays & dependent rewrites)
* **Loops, `for`, `do`, `Id.run`**
  → §7 (Loops & `Id.run`)
* **Finsets, cardinalities, partitions, graph combinatorics**
  → §8 (Finsets & combinatorics)
* **Hammer / external ATP**
  → §9 (LeanHammer)
* **Batteries‑only environment**
  → §10 (Batteries notes; but most patterns above still apply)
* **General “I’m stuck”**
  → §2.2 (When stuck checklist) and §11 (Tiny proof idioms)

---

## 2. Core tactics and workflow

### 2.1 Essential tactics (cheat table)

These are the workhorses you’ll use constantly. 

| Tactic                       | Typical use case                                                    |
| ---------------------------- | ------------------------------------------------------------------- |
| `unfold`                     | Expose definitions and record projections before reasoning          |
| `simp only [..]`             | Local, controlled simplification; avoids global blow‑ups            |
| `simp [..]`                  | Heavy simplification when you *want* everything normalized          |
| `if_pos h` / `if_neg h`      | Reduce `if` branches when you know `cond = true/false`              |
| `rw [thm]` / `rw [thm] at h` | Rewrite equalities in goal / hypotheses                             |
| `intro` / `intros`           | Introduce ∀‑bound vars or implications                              |
| `constructor`                | Build conjunctions / structure values / constructors                |
| `cases` / `match`            | Case split on inductives, `Option`, `Sum`, etc.                     |
| `by_cases h : cond`          | Split on a decidable boolean or Prop                                |
| `have` / `let`               | Introduce intermediate lemmas/definitions                           |
| `obtain ⟨x, hx⟩ := h`        | Unpack existentials while keeping witnesses in scope                |
| `subst h`                    | Replace a variable using `h : x = y` (handles dependent types well) |
| `exact` / `refine`           | Finish goal with an existing term / partially specified shape       |

---

### 2.2 “When stuck” checklist

Before you flail:

1. **Unfold what you actually care about**

   * Projections like `db.error`, `DB.find?`, `DB.insertAxiom`, `trimFrame`, `Finset.erase`, etc.
   * Example:

     ```lean
     unfold DB.error at h ⊢
     ```

2. **Make implicit control flow explicit**

   * `match` / `if` stuck? Do `cases` / `by_cases` **before** big `simp` calls.

3. **Look for the right pattern section**

   * Booleans / `if`: §4.1–4.3
   * Arrays / indices: §6
   * HashMap / `==`: §5
   * Loops: §7
   * Finsets/cardinality: §8

4. **Use `simp only` instead of `simp` if structure matters**

5. **Check typeclass requirements**

   * Need `LawfulBEq` vs `EquivBEq`, `LawfulHashable`, etc. (§5)

6. **Turn ugly control‑flow theorem into a “success conditions” lemma (§4.4)**

---

## 3. Verification testing (proof‑aligned tests)

Formal proofs are great, but **test the invariants you care about** using executable tests. Inspired by verified SAT solvers like CreuSAT. 

### 3.1 Pattern: executable tests for formal properties

Write the theorem you ultimately want:

```lean
theorem insertHyp_maintains_wf
    (db : DB) (pos : Pos) (l : String) (ess : Bool) (arr : Formula)
    (h_wf : WellFormedDB db)
    (h_no_err : db.error? = none)
    : WellFormedDB (db.insertHyp pos l ess arr) := by
  sorry
```

Now mirror a **concrete instance** of this as an IO test:

```lean
def test_insertHyp_float_structure : IO Unit := do
  let db := mkTestDB
  let pos : Pos := ⟨1, 1⟩
  let arr : Formula := #[.const "wff", .var "x"]
  let db' := db.insertHyp pos "fx" false arr

  match db'.find? "fx" with
  | some (.hyp false f _) =>
      if f.size = 2 ∧ !f[0]!.isVar ∧ f[1]!.isVar then
        IO.println "✓ insertHyp float has correct structure"
      else
        throw <| IO.userError "float should have structure (const, var)"
  | _ => throw <| IO.userError "insertHyp should add float"
```

Run via `lake build` and the resulting binary; tests give **fast sanity checks** long before the formal proof is finished.

**Use tests to:**

* Check `error?` flags, sizes, presence/shape of objects
* Catch regressions when refactoring
* Validate that your intended invariant is even realistic

---

## 4. Reasoning about `if`, booleans, matches and control flow

### 4.1 If–then–else reduction

Pattern: **when you know the condition**, make the `if` go away. 

```lean
have h_cond : condition = true := ...
unfold DB.error at h_cond ⊢
simp only [if_pos h_cond]
-- goal reduced to the "then" branch
```

Key tools:

* `if_pos h : cond = true → (if cond then a else b) = a`
* `if_neg h : cond = false → (if cond then a else b) = b`
* Always `unfold` to expose the `if` before using `if_pos`/`if_neg`.
* Prefer `simp only [...]` to avoid over‑simplifying.

---

### 4.2 Bool → Prop for ADT predicates (`isVar`, etc.)

Goal: turn boolean checks into **existential witnesses**.

Example: we know the first symbol is a const because `!isVar` holds. 

```lean
-- Want: ∃ c, arr[0]! = Sym.const c

have ⟨c, h_c⟩ : ∃ c, arr[0]! = Sym.const c := by
  cases h_arr0 : arr[0]! with
  | const c =>
      exact ⟨c, rfl⟩
  | var _ =>
      -- impossible: we have !isVar = true
      simp only [h_arr0, Sym.isVar] at h_first
      simp at h_first
```

Pattern:

1. `cases h_arr0 : arr[i]!` on the ADT (e.g. `const` vs `var`)
2. In unwanted constructors, use your boolean hypothesis (like `!arr[i]!.isVar = true`) and `simp` twice:

   * once to substitute the constructor into `isVar`
   * once to simplify the resulting Boolean equality into contradiction.

Use this whenever you have:

* A boolean predicate like `isVar`, `isConst`, `isAdj` on an ADT
* A spec that wants propositional witnesses (`∃ v, ...`)

---

### 4.3 Case analysis patterns

General shape for aligned `match` in spec and implementation: 

```lean
theorem classify_correct (obj : Object) :
    match classify obj with
    | .error   => result.error = true
    | .success => result.ok := by
  unfold classify process
  match obj with
  | .const c =>
      by_cases h : condition
      · simp [h]  -- error branch
      · simp [h]  -- success branch
  | .var v =>
      ...
```

**Crucial trick**: when a hypothesis hides a `match`, **case on the discriminant first**:

```lean
-- h_match : (match obj with | .const _ => complex_expr | _ => false) = false

cases h_obj : obj with
| const c =>
    simp only [h_obj] at h_match
| var v =>
    simp only [h_obj] at h_match
```

For existentials:

```lean
have h_exists : ∃ o, db.find? label = some o := ...
obtain ⟨o, h_some⟩ := h_exists  -- keeps o in scope
cases o with
| const c => simp [h_some]
| var v   => simp [h_some]
```

Always:

* Use `obtain ⟨x, hx⟩ := ...` instead of anonymous `⟨x, hx⟩` patterns that might scope badly.
* Do `cases` before heavy `simp`.

---

### 4.4 Success condition extraction (⭐)

When you have a hypothesis like:

```lean
h_success : (db.insertAxiom pos l arr).error? = none
```

…don’t fight the full definition inline. Extract **clean conditions** in a dedicated lemma. 

```lean
theorem insertAxiom_success_conditions
    (db : DB) (pos : Pos) (l : String) (arr : Formula)
    (h_success : (db.insertAxiom pos l arr).error? = none) :
    ∃ (fr : Frame),
      db.trimFrame' arr = .ok fr ∧
      db.interrupt = false ∧
      (db.insert pos l (.assert arr fr)).error? = none := by
  unfold DB.insertAxiom at h_success
  generalize h_trim : db.trimFrame' arr = result at h_success
  cases result with
  | error msg =>
      simp at h_success  -- contradiction: mkError can't give error? = none
  | ok fr =>
      refine ⟨fr, ?_⟩
      constructor
      · -- trim succeeded
        rwa [← h_trim]
      ·
        by_cases h_int : db.interrupt
        · simp [h_int] at h_success   -- impossible
        · constructor
          · -- db.interrupt = false
            have := h_int
            simp [Bool.not_eq_true] at this
            exact this
          · -- insert succeeded
            simpa [h_int] using h_success
```

Then your invariants (e.g. well‑formedness) just use:

```lean
obtain ⟨fr, h_trim, h_no_int, h_insert_ok⟩ :=
  insertAxiom_success_conditions db pos l arr h_success
```

**Use this pattern for any** “big function with error flags” where you often assume “no error”.

---

### 4.5 Control flow with match + if

Combine §4.3 and §4.4:

* Put **all the gnarly control flow** (`match`, `if`, `mkError`, flags) into 1–2 “success conditions” lemmas.
* Keep the main invariants talking only about:

  * Which branch was taken (`trimFrame' = .ok fr`)
  * Simple booleans (`interrupt = false`)
  * Downstream calls succeeding (`insert ... .error? = none`)

---

## 5. Equality, `BEq`, HashMaps, and `LawfulBEq`

### 5.1 `EquivBEq` vs `LawfulBEq`

Typeclass hierarchy: 

* `EquivBEq α` – ensures `==` is an equivalence (refl/symm/trans)
* `LawfulBEq α` – stronger: has `beq_iff_eq : (a == b) = true ↔ a = b`

Use:

* `EquivBEq` when you only need equivalence properties.
* `LawfulBEq` when you need to move between `==` and `=`.

Useful lemmas:

* `Bool.eq_false_iff : b = false ↔ b ≠ true`
* `Bool.eq_true_iff : b = true ↔ b ≠ false`

Pattern: from `k ≠ k'` to `(k == k') = false`:

```lean
theorem beq_of_ne_false [BEq α] [LawfulBEq α]
    (k k' : α) (h_ne : k ≠ k') :
    (k == k') = false := by
  have : ¬((k == k') = true) := by
    intro h
    rw [beq_iff_eq] at h
    exact h_ne h
  simp [this]
```

---

### 5.2 HashMap proofs (Std and Batteries)

In batteries, `HashMap` is a wrapper for `Std.HashMap`: 

```lean
structure HashMap (α : Type u) (β : Type v) where
  inner : Std.HashMap α β
```

Core lemmas (from `Std.HashMap`):

```lean
-- after inserting key k with value v, lookup k
theorem getElem?_insert_self [EquivBEq α] [LawfulHashable α] :
  (m.insert k v)[k]? = some v

-- inserting maybe affects other keys:
theorem getElem?_insert [EquivBEq α] [LawfulHashable α] :
  (m.insert k v)[a]? = if k == a then some v else m[a]?
```

Pattern: inserting a **different key** doesn’t change other lookups (needs `LawfulBEq`):

```lean
theorem find?_insert_other
    [LawfulBEq α] [LawfulHashable α]
    (m : HashMap α β) (k k' : α) (v : β) :
    k ≠ k' → (m.insert k v)[k']? = m[k']? := by
  intro h_ne
  rw [Std.HashMap.getElem?_insert]
  have : ¬((k == k') = true) := by
    intro h
    rw [beq_iff_eq] at h
    exact h_ne h
  simp [this]
```

HashMap inside records:

```lean
structure DB where
  objects : HashMap String Object
  error?  : Option Error
```

Record updates compose nicely with `simp`:

```lean
theorem example (db : DB) (label : String) (obj : Object) :
    { db with objects := db.objects.insert label obj }.objects[label]? = some obj := by
  simp  -- uses getElem?_insert_self through .objects
```

Plan:

1. `unfold DB.find?` wrappers to reveal `.objects[label]?`.
2. Use `simp` to push through record updates and apply HashMap lemmas.

---

## 6. Arrays, indices, and dependent rewrites

### 6.1 `arr[i]!` vs `arr[i]` (Array indexing equivalence)

Lean has two styles: 

* `arr[i]` / `arr[i]'h` – dependent indexing (requires proof `h : i < arr.size`)
* `arr[i]!` – partial indexing with `[Inhabited α]`

They’re **not** definitionally equal, but we have:

```lean
theorem getElem!_pos {α} [Inhabited α]
    (arr : Array α) (i : Nat) (h : i < arr.size) :
  arr[i]! = arr[i]
```

Example:

```lean
-- Given
hi     : i < db.frame.hyps.size
h_find : db.find? db.frame.hyps[i] = some obj

-- Bridge to `!` form:
have h_bang : db.frame.hyps[i]! = db.frame.hyps[i] := by
  simp [getElem!_pos, hi]

have h_find' : db.find? db.frame.hyps[i]! = some obj := by
  rw [h_bang]
  exact h_find
```

Same pattern holds for `List` via its own `getElem!_pos` variant.

---

### 6.2 Dependent type rewrites and `subst`

Typical error:

> “motive is not type correct”

…when rewriting arrays that appear inside dependent indices. Root cause: proof terms like `h : i < arr.size` are embedded in the type of `arr[i]'h`, so changing `arr` without changing `h` breaks typing. 

Preferred fix: **`subst` whole equalities**, especially for records:

```lean
-- h_db_eq : db_after_check = db

have h_db_eq := h_loop_eq_db h_ess h_size
subst h_db_eq
-- all occurrences of db_after_check, including in bounds proofs,
-- are replaced consistently by db
```

Other strategies:

* Abstract indices in helper lemmas:

  ```lean
  lemma helper_with_indices
      (arr : Array α) (i j : Nat)
      (hi : i < arr.size) (hj : j < arr.size) :
      some_property arr[i] arr[j] := by
    ...
  ```

  Then call `helper_with_indices` instead of rewriting inside `arr[i]'hi`.

* Use definitional equalities (`rfl`) where possible instead of arithmetic equalities that require rewriting.

---

## 7. Loops, `Id.run`, and for‑in

### 7.1 For‑in loops as `foldl`

Goal: show imperative loops (with `for` and mutable state) equal a **pure fold**. 

For lists:

```lean
theorem List.idRun_forIn_yield_eq_foldl
    {α β} (xs : List α) (init : β) (step : β → α → β) :
    Id.run (xs.forIn init (fun a s =>
      pure (ForInStep.yield (step s a)))) =
      xs.foldl step init := by
  induction xs generalizing init with
  | nil => simp
  | cons a xs ih => simpa using ih (step init a)
```

For arrays:

```lean
theorem Array.idRun_forIn_toList {α β}
    (arr : Array α) (init : β)
    (body : α → β → Id (ForInStep β)) :
    Id.run (arr.forIn init body) =
      Id.run ((arr.toList).forIn init body) := by
  simp [Array.forIn_toList]

theorem Array.idRun_forIn_yield_eq_foldl
    {α β} (arr : Array α) (init : β) (step : β → α → β) :
    Id.run (arr.forIn init (fun a s =>
      pure (ForInStep.yield (step s a)))) =
      (arr.toList).foldl step init := by
  rw [Array.idRun_forIn_toList]
  exact List.idRun_forIn_yield_eq_foldl (arr.toList) init step
```

### 7.2 Example: factoring a loop via a step function

Define a pure step:

```lean
def floatStep (pos : Pos) (v : String) (db : DB) (h : String) : DB :=
  match db.find? h with
  | some (.hyp false prevF _) =>
      if prevF.size ≥ 2 ∧ prevF[1]!.value == v then
        db.mkError pos s!"variable {v} already has $f hypothesis"
      else db
  | _ => db
```

The recursive specification:

```lean
theorem floatCheckLoopAux_eq_foldl
    (db : DB) (pos : Pos) (v : String) (hyps : List String) :
    floatCheckLoopAux db pos v hyps =
      hyps.foldl (floatStep pos v) db := by
  induction hyps generalizing db with
  | nil => rfl
  | cons h t ih =>
      simp [floatCheckLoopAux, List.foldl, floatStep]
      cases db.find? h <;> simp [ih]
```

For the imperative `for` version, you show it also equals the same `foldl` using the `Array.idRun_forIn_yield_eq_foldl` lemma and pointwise equality of bodies (via `funext`).

---

### 7.3 Loop reasoning: three strategies

1. **External I/O‑style correctness theorem**

   Work only with `(input, output)` relation:

   ```lean
   theorem trimFrame_produces_subsequence
       (db : DB) (fmla : Formula)
       (fr : Frame)
       (h : db.trimFrame fmla = (ok, fr)) :
       IsSubsequence fr.hyps db.frame.hyps := by
     -- unfold and reason about result, not loop structure
   ```

2. **Tail recursion with an invariant**

   Re‑encode loop as tail recursion where the invariant is an explicit parameter.

3. **Reflection / `decide`**

   For small decidable properties, rely on `decide` / `native_decide`.

   ```lean
   example : IsSubsequence arr1 arr2 := by
     decide
   ```

---

## 8. Finsets and combinatorics (mathlib patterns)

All of this assumes mathlib’s `Finset` and `BigOperators`. 

### 8.1 Critical API gotcha: `mem_erase` order (⭐)

`mem_erase` unfolds as **inequality first, membership second**:

```lean
example {α : Type*} [DecidableEq α]
    (s : Finset α) (a w : α) (h : w ∈ s.erase a) :
    w ≠ a ∧ w ∈ s := by
  simp [Finset.mem_erase] at h
  exact h
```

Thus:

```lean
-- CORRECT:
intro ⟨hne, hs⟩

-- WRONG:
intro ⟨hs, hne⟩  -- type error
```

Example partition:

```lean
have h_partition_eq : vertices.erase v =
  (vertices.filter (fun w => w ≠ v ∧ G.Adj v w)) ∪
  (vertices.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)) := by
  ext w
  simp [Finset.mem_union, Finset.mem_erase, Finset.mem_filter]
  constructor
  · intro ⟨hne, hw⟩
    by_cases h : G.Adj v w
    · left;  exact ⟨hw, hne, h⟩
    · right; exact ⟨hw, hne, h⟩
  · intro h; cases h with
    | inl h =>
        obtain ⟨hw, hne, _⟩ := h
        exact ⟨hne, hw⟩
    | inr h =>
        obtain ⟨hw, hne, _⟩ := h
        exact ⟨hne, hw⟩
```

---

### 8.2 Variable scope after `rfl` substitutions

Pattern: `obtain (rfl | rfl | rfl) := hx` *eliminates* the original variable.

So collect necessary facts **before** such substitutions: 

```lean
intros x hx y hy hxy h_adj

-- collect facts about x, y
have hx_nonadj_v : ¬ G.Adj v x := ...
have hy_nonadj_v : ¬ G.Adj v y := ...

simp [I, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
obtain (rfl | rfl | rfl) := hx <;> obtain (rfl | rfl | rfl) := hy
· exact hxy rfl
· exact hx_nonadj_v h_adj
· ...
```

---

### 8.3 Disjointness: use `disjoint_left`

Avoid reasoning via explicit intersections; the canonical lemma is:

```lean
disjoint_left :
  Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t
```

Example:

```lean
have h_disj : Disjoint B C := by
  rw [Finset.disjoint_left]
  intro w hw hw'
  -- show a contradiction from w ∈ B and w ∈ C
```

Used in partition arithmetic:

```lean
rw [h_partition_eq, Finset.card_union_of_disjoint h_disj] at h_others_card
```

---

### 8.4 Partition/cardinality patterns

**Union of disjoint parts:**

```lean
-- A = B ∪ C and B, C disjoint → |A| = |B| + |C|
have h_partition : A = B ∪ C := ...
have h_disj : Disjoint B C := ...
have : A.card = B.card + C.card := by
  simpa [h_partition] using
    Finset.card_union_of_disjoint h_disj
```

**Extracting elements from a card‑n Finset:**

```lean
have h_card : P.card = 4
have h_nonempty : P.Nonempty := Finset.card_pos.mp (by omega)
obtain ⟨p1, hp1⟩ := h_nonempty

have h_erase1 : (P.erase p1).card = 3 := by
  rw [Finset.card_erase_of_mem hp1, h_card]
  norm_num

have h_nonempty2 : (P.erase p1).Nonempty :=
  Finset.card_pos.mp (by omega)
obtain ⟨p2, hp2⟩ := h_nonempty2
-- and so on
```

**Extract subset of specified size:**

```lean
-- Given 3 ≤ s.card, get S ⊆ s with S.card = 3
have h_size : 3 ≤ s.card := ...
obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq h_size
-- Now: S ⊆ s and S.card = 3
```

---

### 8.5 Graph‑theoretic patterns (mathlib’s `SimpleGraph`)

Adjacency symmetry:

```lean
-- Prefer: G.symm
have h : G.Adj x y
have h' : G.Adj y x := G.symm h
```

Triangle/clique construction:

```lean
def tri : Finset V := {v, x, y}

have h_clique : G.IsNClique 3 tri := by
  -- clique condition
  constructor
  · intro a ha b hb hne
    simp [tri, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    obtain (rfl | rfl | rfl) := ha <;> obtain (rfl | rfl | rfl) := hb
    · exact hne rfl
    · -- use pre‑collected facts like hx_adj, hy_adj, etc.
      ...
  · -- cardinality = 3
    have h_v_ne_x : v ≠ x := ...
    have h_v_ne_y : v ≠ y := ...
    have h_x_ne_y : x ≠ y := ...
    simp [tri, Finset.card_insert_of_notMem,
          Finset.card_singleton, h_v_ne_x, h_v_ne_y, h_x_ne_y]
```

---

### 8.6 Meta‑lessons for finset work

* Test important API behavior (like `mem_erase`) in a **small scratch file** first.
* Pre‑collect facts you’ll need after destructive pattern matches (`rfl` cases).
* Use specialized lemmas:

  * `disjoint_left`
  * `card_union_of_disjoint`
  * `exists_subset_card_eq`
* Offload arithmetic of cardinalities to `omega` or `linarith`.

Example test file:

```lean
import Mathlib.Data.Finset.Card

open Finset

example {α} [DecidableEq α] (s : Finset α) (a w : α) (h : w ∈ s.erase a) :
    w ≠ a ∧ w ∈ s := by
  simp [Finset.mem_erase] at h
  exact h
```

---

## 9. LeanHammer (ATP integration)

### 9.1 What Hammer is

LeanHammer combines: 

* Neural premise selection
* Translation to external provers (E, Vampire, Zipperposition, etc.)
* Proof reconstruction back into Lean tactics

Install in `lakefile.lean`:

```lean
require Hammer from git "https://github.com/JOSHCLUNE/LeanHammer.git"
```

Use in files:

```lean
import Hammer
```

Basic usage:

```lean
example (h : P → Q) (hp : P) : Q := by
  hammer
```

Config:

```lean
example : _ := by
  hammer (config := { aesopPremises := 64, autoPremises := 32 })
```

---

### 9.2 Key principle: tactical decomposition

> **Hammer is a finisher, not a magic solver.**

It works well on **tiny, well‑prepared subgoals**, not on massive goals. 

Workflow:

1. **Break down with tactics first**

   * `intro`, `simp`, `simp_all`, `constructor`, `cases`, `rw`, `have`…

2. **Call `hammer` on the tiny pieces**

   * It usually proposes something like `simp_all only` or `intro; simp_all`.

3. **Apply its suggestions**

   * Even when it “fails”, it prints suggested tactics that often solve the goal.

Examples where Hammer shines:

```lean
-- trivial goal
example (a : α) (ha : a ∈ A) : a ∈ A := by
  hammer  -- suggests `simp_all only`

-- implication chains
example (a : α) (ha : a ∈ A) :
    R a b → b ∈ B → a ∈ A := by
  hammer  -- suggests `intro; simp_all only`

-- product membership
example (a : α) (b : β) (ha : a ∈ A) (hb : b ∈ B) :
    (a, b) ∈ A ×ˢ B := by
  hammer  -- uses finset product facts
```

Example where it *doesn’t* work: big double‑counting identity over sums—too many moving pieces unless you first set up intermediate structures and lemmas.

---

### 9.3 Premise limits and minimal imports

Hammer has a hardcoded limit (~2048 unindexed premises). If you see:

> Found 3045 unindexed premises…

Make a **minimal file** importing only what you need:

```lean
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Hammer

open Finset BigOperators

-- Now your theorem here with fewer premises in scope
```

---

### 9.4 Troubleshooting Hammer

Common messages and fixes:

* `"aesop: failed to prove the goal after exhaustive search"`
  → Goal too complex. Break it down, simplify more, re‑run.

* `"made no progress"`
  → Decompose, `simp only`, introduce variables, set up simpler sublemma.

* `"timeout at isDefEq"`
  → Too much computation. Reduce premise counts, avoid heavy `simp` with huge lemma sets.

Best practices:

* Keep `aesopPremises`/`autoPremises` in ~16–32 range.
* Use on **membership**, **simple contradictions**, **basic product/filter** goals.
* Use it to *learn* good tactic sequences (`simp_all only`, etc.).

---

## 10. Batteries‑only notes (Metamath style)

All patterns above work **without mathlib** as long as you: 

* Use the **batteries** core plus `Std` structures (`HashMap`, `Array`, `List`).
* Provide instances like `LawfulBEq`, `LawfulHashable` for key types.
* Implement your own small combinators where mathlib would usually help (e.g. set/finset analogues, simple cardinality lemmas).

Important batteries‑specific points:

* **Verification testing**: same pattern, but IO tests live in the batteries project.
* **HashMap**: use `Std.HashMap` lemmas with wrappers.
* **Loops**: `Id.run` and for‑in lemmas work the same; you may need to re‑implement some helper theorems (like `idRun_forIn_yield_eq_foldl`).
* **Finite combinatorics**: you’ll likely mirror a subset of mathlib’s `Finset` API with custom structures.

When you later port from batteries‑only to mathlib:

* Replace custom combinatorics with finset lemmas in §8.
* Keep the core patterns (Bool → Prop, success‑condition extraction, HashMap proofs, array indexing, loop/fold equivalence) unchanged.

---

## 11. Tiny reusable proof idioms (pattern library)

These are small but ubiquitous bricks. 

### 11.1 Contradiction from incompatible equalities

```lean
have h1 : a = true  := ...
have h2 : a = false := ...
simp [h1] at h2  -- closes goal via False
```

### 11.2 Boolean case analysis

```lean
match h : someBool with
| true  => ...
| false => ...
```

### 11.3 Option case analysis

```lean
match h : someOpt with
| none   => ...
| some x => ...
```

### 11.4 Existential unpacking with `obtain`

```lean
have h_exists : ∃ x, P x := ...
obtain ⟨x, hx⟩ := h_exists
-- x and hx now in scope
```

### 11.5 Deriving contradictions from Bool + Option

```lean
-- h_err  : ¬ db.error = true
-- h_some : db.error? = some e

unfold DB.error at h_err
simp [Option.isSome, h_some] at h_err  -- gives False
```

Use this chapter as a mental “tool belt” for everyday situations.

