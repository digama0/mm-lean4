# Lean 4 Proof Patterns - Quick Reference

One-page cheat sheet for all critical patterns used in stuck proofs.

---

## Pattern 1: List Induction (Lesson 1)

```lean
induction xs with
| nil =>
    -- Base case: xs = []
    simp
| cons x xs ih =>
    -- Recursive case: xs = x :: xs
    -- ih : <property of xs>
    simp [ih]
```

**Use when**: Proving properties of list operations directly

---

## Pattern 2: Fold Induction with Generalized Accumulator (Lesson 2) ⭐

```lean
induction xs generalizing acc with
| nil =>
    simp [List.foldl]
| cons x xs ih =>
    simp only [List.foldl_cons]
    -- ih : ∀ acc', xs.foldl f (f acc x) acc' = ...
    rw [ih]
    -- Now continue with new accumulator
```

**Use when**: Proving properties of `List.foldl`
**Critical**: Without `generalizing`, IH won't apply to modified accumulator

---

## Pattern 3: Monadic Fold Induction (Lesson 3)

```lean
induction xs generalizing init with
| nil =>
    simp [List.foldlM, List.sum]
| cons x xs ih =>
    simp [List.foldlM, step_function]
    rw [ih]
    simp
    omega
```

**Use when**: Proving properties of `List.foldlM` when step never fails
**Note**: Use `simp [List.foldlM]` to unfold the monadic definition

---

## Pattern 4: List Splitting (Lesson 4) ⭐

```lean
-- Convert size/length property to existential split
have h_ne : 0 < xs.length := ...
obtain ⟨head, tail, h_split⟩ := list_nonempty_split xs h_ne
-- Now: xs = head :: tail

-- Or directly with cases
cases xs with
| nil =>
    -- Size > 0 contradicts []
    simp at h_ne
| cons head tail =>
    -- Now xs = head :: tail
    rw [h_split]  -- or just use the structure
    sorry
```

**Use when**: Need to pattern-match on array size or list head
**Key insight**: `cases` automatically discharges nil impossibility

---

## Pattern 5: Function Pattern Normalization (Lesson 5)

```lean
-- Method 1: Simplification
simp only [...]  -- Reduces both patterns to normal form

-- Method 2: Function extensionality
have : f = g := by
  ext x
  simp

-- Method 3: Direct proof
rfl  -- Often works after unfolding both definitions
```

**Use when**: Two lambdas should be equal but look different
**Example**:
```lean
-- These should be equal:
fun (c, v) => c.length + v.length
fun x => x.fst.length + x.snd.length
```

---

## Pattern 6: FoldlM Case Analysis (Lesson 6) ⭐⭐

```lean
-- Step 1: Create helper with generalized accumulator
have helper : ∀ (acc : ArrayType),
    xs.foldlM f acc = .ok result →
    <desired property of result, acc, xs> := by
  intro acc h_fold
  -- Step 2: Induct on xs with generalized acc
  induction xs generalizing acc result with
  | nil =>
      simp [List.foldlM] at h_fold
      exact h_fold ▸ <proof>
  | cons s syms ih =>
      simp [List.foldlM] at h_fold
      -- Step 3: Case on whether step succeeded
      cases h_step : f acc s with
      | error _ =>
          -- Step failed → whole fold fails
          -- This contradicts h_fold : ... = .ok
          simp [h_step] at h_fold  -- Leads to false
      | ok acc' =>
          -- Step succeeded → continue with acc'
          simp [h_step] at h_fold
          -- h_fold : syms.foldlM f acc' = .ok result
          -- Step 4: Use IH with new accumulator
          have := ih acc' h_fold
          <relate to property>

-- Step 5: Apply helper with initial accumulator
exact helper init_acc h_fold_eq
```

**Use when**: Proving fold properties when step can fail
**Critical**:
1. Generalize accumulator in helper
2. Case on success/failure at each step
3. Discharge error case as contradiction
4. Use IH with new accumulator for ok case

---

## Pattern 7: Array Splitting (Lesson 4)

```lean
-- Convert array property to list
have h_list : 0 < a.toList.length := by
  simpa using h_size  -- or omega

-- Split the list
obtain ⟨head, tail, h_split⟩ := list_nonempty_split a.toList h_list

-- Now work with list structure
-- to.Array : Array α
-- Get: head :: tail = a.toList
```

**Use when**: Need to work with array structure in induction/case analysis

---

## Quick Decision Tree

**"How do I prove properties of..."**

- **Simple list operations** (length, map, etc.)
  → Pattern 1: List Induction

- **List.foldl**
  → Pattern 2: Fold with `generalizing`

- **List.foldlM (no failure)**
  → Pattern 3: Monadic Fold (simple)

- **Array indexing or head/tail properties**
  → Pattern 4: List Splitting

- **Two extensionally equal functions**
  → Pattern 5: Function Normalization

- **List.foldlM (with potential failure)**
  → Pattern 6: Two-level induction + case analysis

- **Array operations with size > 0**
  → Pattern 7: Array Splitting

---

## Common Mistakes

### ❌ Mistake 1: Not generalizing accumulator
```lean
-- WRONG
induction xs with
| cons x xs ih =>
    -- ih only applies to specific accumulator

-- RIGHT
induction xs generalizing acc with
| cons x xs ih =>
    -- ih applies to any acc
```

### ❌ Mistake 2: Skipping case analysis on foldlM step
```lean
-- WRONG
simp [List.foldlM] at h
-- h might have .error, but you didn't check

-- RIGHT
simp [List.foldlM] at h
cases h_step : f acc x with
| error _ => simp [h_step] at h  -- Must handle this
| ok acc' => simp [h_step] at h  -- And this
```

### ❌ Mistake 3: Directly pattern-matching arrays
```lean
-- WRONG
cases a with  -- Arrays don't case like lists
| cons head tail => ...

-- RIGHT
cases a.toList with
| nil => ...
| cons head tail => ...
```

### ❌ Mistake 4: Assuming function patterns are equivalent
```lean
-- WRONG
rw [h_allM]  -- Fails because patterns don't syntactically match

-- RIGHT
simp only [...]  -- Normalize both patterns first
rw [h_allM]
```

---

## Tactic Cheat Sheet

| Tactic | Use Case | Example |
|--------|----------|---------|
| `induction` | Structural recursion | `induction xs with \| nil => \| cons x xs ih =>` |
| `generalizing` | Include parameter in IH | `induction xs generalizing acc with` |
| `cases` | Case analysis | `cases h_step : f acc x with \| error _ => \| ok acc' =>` |
| `simp [...]` | Unfold definitions | `simp [List.foldlM, f]` |
| `rw [...]` | Rewrite with IH | `rw [ih]` |
| `omega` | Linear arithmetic | `omega` |
| `ext` | Function extensionality | `ext x` |
| `obtain ⟨...⟩ := ...` | Destruct existential | `obtain ⟨head, tail, h⟩ := split` |

---

## Common Lemmas

### List Operations
- `List.length_append`: `(xs ++ ys).length = xs.length + ys.length`
- `List.map_cons`: `(x :: xs).map f = f x :: xs.map f`
- `List.foldl_cons`: `(x :: xs).foldl f acc = xs.foldl f (f acc x)`
- `List.sum_cons`: `(x :: xs).sum = x + xs.sum`
- `List.foldlM`: Unfold monadic folds with `simp [List.foldlM]`

### Array Operations
- `Array.toList`: Convert array to list
- `Array.size`: Get array length
- `Array.getElem!`: Index with default (uses `!`)

### Monadic Operations
- `Except.bind`: Threading exceptions
- `Option.bind`: Threading optionals
- `.ok`/`.error`: Except constructors

---

## Debugging Tips

1. **If `omega` fails on arithmetic**: Add more context with `have` statements first
2. **If `simp` makes no progress**: Try `simp only [...]` with explicit lemmas
3. **If case analysis succeeds but next step is stuck**: Try `omega` or `contradiction`
4. **If induction hypothesis doesn't apply**: Check for `generalizing` keyword
5. **If pattern match fails on arrays**: Convert to list first with `.toList`

---

## For Each Stuck Proof

### Line 328: subst_preserves_head_of_const0
Use: **Pattern 4 (List Splitting)** + **Pattern 2 (Fold)**
```lean
obtain ⟨head, tail, _⟩ := list_nonempty_split f.toList
induction tail generalizing acc with
```

### Line 370: subst_ok_flatMap_tail
Use: **Pattern 6 (Case Analysis)** + **Pattern 2 (Fold)**
```lean
have helper : ∀ acc, xs.foldlM f acc = .ok result → ... := by
  intro acc h
  induction xs generalizing acc result with
    cases h_step : f acc x with
```

### Line 401: subst_preserves_head
Use: **Pattern 4 (List Splitting)** setup
```lean
obtain ⟨head, tail, _⟩ := list_nonempty_split f.toList
```

---

**Print this page and reference while working on proofs!**
