# Task for Codex: Prove `subst_preserves_head_of_const0`

## Location
File: `Metamath/KernelClean.lean`, lines 330-333

## Current State
```lean
theorem subst_preserves_head_of_const0 {σ : Std.HashMap String Formula} {f g : Formula}
    (hf : 0 < f.size) (hhead : ∃ c, f[0]! = Sym.const c) (h_sub : f.subst σ = Except.ok g) :
    ∃ (hg : 0 < g.size), g[0]'hg = f[0]'hf := by
  sorry  -- TODO: Use Array.foldlM_toList_eq to decompose and apply helper theorems
```

## What This Theorem Says
If `f` starts with a constant `c` (i.e., `f[0]! = Sym.const c`), then after substitution,
`g` also starts with the same constant `c` (i.e., `g[0] = f[0] = Sym.const c`).

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

## Available Infrastructure (Just Proven!)

You have access to these recently proven lemmas:

1. **`foldl_push_preserves_head`** (KernelClean.lean:192) - Array.foldl with Array.push preserves the head element
2. **`foldl_push_size_pos`** (KernelClean.lean:148) - Array.foldl with Array.push preserves nonemptiness
3. **`foldlM_substStep_preserves_head_general`** (KernelClean.lean:288) - foldlM with substStep preserves head when starting from nonempty
4. **`foldlM_substStep_preserves_head_of_const`** (KernelClean.lean:313) - foldlM with substStep preserves head when starting from `#[const c]`

## Proof Strategy

The key insight: `f.subst σ` starts from `#[]` (empty), then processes `f[0]` (which is `const c`),
then processes the rest of `f.toList.drop 1`.

**Step 1:** Extract the constant from `hhead`
```lean
obtain ⟨c, hc⟩ := hhead
```

**Step 2:** Unfold `subst` to see it's `f.foldlM (substStep σ) #[]`

**Step 3:** Use the fact that `f = f[0] :: f.toList.drop 1` (via List.cons_head_tail or similar)

**Step 4:** Show that after processing `f[0] = const c`, we have `#[const c]`
- `substStep σ #[] (const c) = .ok (#[].push (const c)) = .ok #[const c]`

**Step 5:** Apply `foldlM_substStep_preserves_head_of_const` to the rest of the list
- This shows that folding the tail over `#[const c]` preserves the head

**Step 6:** Combine to show `g[0] = const c = f[0]`

## Expected Proof Length
30-60 lines (similar to `foldlM_substStep_preserves_head_of_const` at line 313)

## Build Command
```bash
lake build Metamath.KernelClean
```

## Success Criteria
- Remove the `sorry` at line 333
- Proof compiles without errors
- No new axioms introduced
- Uses the existing foldl infrastructure lemmas

## Notes
- You may need `List.foldlM_cons` to split the foldl into head + tail
- You may need to unfold/simp `substStep` to show it preserves the constant
- The dependent type `g[0]'hg = f[0]'hf` requires careful handling - use `calc` or explicit witnesses

Good luck! This is the theorem that unlocks Phase 5-8 soundness proofs.
