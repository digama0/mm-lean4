# Task for Codex: Prove `subst_ok_flatMap_tail`

## Location
File: `Metamath/KernelClean.lean`, lines 381-390

## Current State
```lean
/-- Tail correspondence: When substituting, the tail of the result matches
    the flatMap of the tail with the substitution step. -/
theorem subst_ok_flatMap_tail {σ : Std.HashMap String Formula} {f g : Formula}
    (h_sub : f.subst σ = Except.ok g) :
    g.toList.tail = (f.toList.tail).flatMap fun s =>
      match s with
      | .const _ => [s]
      | .var v   =>
        match σ[v]? with
        | none => []
        | some e => e.toList.drop 1 :=
  sorry
```

## What This Theorem Says
After substitution `f.subst σ = ok g`, the tail of the result formula `g` is exactly the flatMap of the original tail `f.toList.tail`, where:
- Constants map to themselves: `const c → [const c]`
- Variables map to the tail of their substitution: `var v → (σ[v]).toList.drop 1`

This is the **tail correspondence** property that complements the **head preservation** property we just proved.

## Key Definitions

### Formula.subst (Verify.lean:155)
```lean
def Formula.subst (σ : HashMap String Formula) (f : Formula) : Except String Formula :=
  f.foldlM (Formula.substStep σ) #[]
```

### Formula.substStep (Verify.lean:144)
```lean
def Formula.substStep (σ : HashMap String Formula)
    (acc : Formula) (s : Sym) : Except String Formula :=
  match s with
  | .const _ => .ok (acc.push s)
  | .var v   =>
    match σ[v]? with
    | none   => .error s!"variable {v} not found"
    | some e => .ok (e.foldl Array.push acc 1)
```

## Where This Theorem Is Used

This is a **high-leverage theorem** used in `subst_correspondence` (line 2418), which is critical for Phase 6 soundness proofs. Specifically:

```lean
-- At line 2456 in subst_correspondence:
have h_impl_tail := subst_ok_flatMap_tail h_subst
-- This is used to show that the tail of concl_impl matches the
-- flatMap of f_impl.toList.tail under substitution
```

`subst_correspondence` proves that implementation-level substitution matches spec-level applySubst, which is essential for the assert step soundness.

## Available Infrastructure

You have access to these recently proven lemmas:

1. **`subst_preserves_head_of_const0`** (KernelClean.lean:330) - Head preservation for constants
2. **`foldlM_substStep_preserves_head_of_const`** (KernelClean.lean:313) - Head preservation during foldlM
3. **`foldl_eq_list_foldl_drop`** (ArrayListExt.lean:349) - Bridge between array and list foldl
4. **`Array.foldlM_toList`** - Bridge between array and list foldlM
5. **`List.tail_eq_tailD_of_ne_nil`** - List tail properties
6. **`Array.toList_push`** - Array push to list append
7. **`List.append_left_inj`** - List append injectivity

## Proof Strategy

**Key Insight:** `f.subst σ` processes `f[0]` (the head), then folds over `f.toList.drop 1` (the tail).

**Step 1:** Unfold `f.subst σ` to see it's `f.foldlM (substStep σ) #[]`

**Step 2:** Use `Array.foldlM_toList` to convert to list foldlM:
```lean
have h_list : f.toList.foldlM (substStep σ) #[] = ok g := ...
```

**Step 3:** Decompose `f.toList` into head and tail using `List.exists_cons_of_ne_nil`:
```lean
obtain ⟨s0, rest, h_cons⟩ := List.exists_cons_of_ne_nil h_ne_nil
-- where rest = f.toList.tail
```

**Step 4:** Use `List.foldlM_cons` to split the fold:
```lean
-- (s0 :: rest).foldlM (substStep σ) #[] =
-- do { acc1 ← substStep σ #[] s0; rest.foldlM (substStep σ) acc1 }
```

**Step 5:** Show that after processing `s0`, we get `#[s0]` (assuming s0 is const):
```lean
-- substStep σ #[] (const c) = ok (#[const c])
```

**Step 6:** Prove by induction on `rest` that:
```lean
rest.foldlM (substStep σ) #[s0] = ok g
-- implies
g.toList = [s0] ++ (rest.flatMap substStep_tail_map)
-- where substStep_tail_map matches the pattern in the theorem
```

**Step 7:** Extract `g.toList.tail = rest.flatMap substStep_tail_map`

## Key Challenges

1. **List induction over tail:** You'll need induction on `f.toList.tail` (which is `rest`)
2. **substStep behavior:** Pattern match on const vs var cases
3. **Array ++ List correspondence:** When processing variables, `e.foldl Array.push acc 1` appends `e.toList.drop 1`
4. **flatMap composition:** Build up the flatMap result incrementally

## Expected Proof Length
60-100 lines (similar complexity to the bridge lemma `foldl_eq_list_foldl_drop`)

## Build Command
```bash
lake build Metamath.KernelClean
```

## Success Criteria
- Remove the `sorry` at line 390
- Proof compiles without errors
- No new axioms introduced
- Uses existing foldlM and list infrastructure

## Notes
- You may need a helper lemma for the induction
- The pattern matching on const/var in the flatMap should align with substStep's behavior
- Consider using `calc` chains for clarity
- Watch out for array vs list boundaries (use `toList` and `Array.push` lemmas)

This theorem unlocks `subst_correspondence`, which is blocking Phase 6 soundness!
