/-
# Lesson 5: Function Pattern Matching Mismatch

Goal: Learn how to handle when function lambdas use different pattern styles.
This is what toSubstTyped_of_allM_true is stuck on!

Key Challenge: Two functions are extensionally equal but syntactically use different patterns:
- Version A: `fun (c, v) => body`  (tuple destructuring in pattern)
- Version B: `fun x => ... x.fst x.snd`  (pair access)

Lean's pattern matching is strict: these are not automatically interchangeable.
-/

-- Pattern 1: Direct tuple destructuring
def process_pair_v1 (p : Nat × String) : Nat :=
  let (a, b) := p
  a + b.length

-- Pattern 2: Pair access
def process_pair_v2 (p : Nat × String) : Nat :=
  let a := p.fst
  let b := p.snd
  a + b.length

-- These are equal as functions
theorem pair_versions_equal : process_pair_v1 = process_pair_v2 := by
  rfl  -- Definitionally equal!

-- Pattern 3: The allM case - this is the REAL blocker
-- The allM in List uses: fun x => predicate x
-- But we define the predicate with destructuring: fun (c, v) => ...

def checkPair (c : Nat) (v : String) : Bool :=
  c > 0 && v.length > 0

-- allM expects: (Nat × String) → Bool
-- checkPair expects: Nat → String → Bool
-- Need to curry/uncurry

def checkPair_uncurried : Nat × String → Bool :=
  fun (c, v) => checkPair c v

def checkPair_uncurried_v2 : Nat × String → Bool :=
  fun x => checkPair x.fst x.snd

-- These are the same!
theorem check_pair_versions_equal : checkPair_uncurried = checkPair_uncurried_v2 := by
  rfl

-- Pattern 4: Working with allM when predicates don't perfectly match
-- This is what toSubstTyped_of_allM_true needs

def all_true_list (ps : List (Nat × String)) (h : ps.allM checkPair_uncurried = some true) :
    ∀ p ∈ ps, checkPair_uncurried p = true := by
  -- allM processes with checkPair_uncurried
  -- We want to extract witnesses
  sorry

-- Pattern 5: The solution - normalize the function before using it
-- This is the key trick: use Function.uncurry

def Bridge_floats_example : List (String × String) := [("a", "b"), ("c", "d")]

-- The actual problem: these use different patterns
def check_float_v1 : String × String → Bool :=
  fun (c, v) => c.length > 0 && v.length > 0

def check_float_v2 : String × String → Bool :=
  fun x => x.fst.length > 0 && x.snd.length > 0

-- Solution: Use Function.uncurry to canonicalize
def uncurried_check : String → String → Bool :=
  fun c v => c.length > 0 && v.length > 0

def check_float_via_uncurry : String × String → Bool :=
  Function.uncurry uncurried_check

theorem check_float_v1_via_uncurry : check_float_v1 = check_float_via_uncurry := by
  rfl

/-
KEY PATTERN FROM ACTUAL CODE (line 859):

```lean
theorem toSubstTyped_of_allM_true
    (fr : Spec.Frame) (σ_impl : Std.HashMap String Verify.Formula)
    (hAll : (Bridge.floats fr).allM (fun (c, v) => checkFloat σ_impl c v) = some true) :
  ∃ σ_typed : Bridge.TypedSubst fr, toSubstTyped fr σ_impl = some σ_typed := by
  sorry
```

The blocker is:
- hAll uses: `fun (c, v) => checkFloat σ_impl c v`
- But toSubstTyped internally probably uses: `fun x => checkFloat σ_impl x.fst x.snd`

**Solution A: Unfold and normalize**
```lean
-- Unfold toSubstTyped's implementation
unfold toSubstTyped
-- Now both use the same pattern
```

**Solution B: Use Function.uncurry**
```lean
-- Both sides use the same function
let h := Function.ext fun x => ...
```

**Solution C: Direct pattern proof**
```lean
-- Show the two patterns behave identically
have h_pattern_eq : ∀ c v, checkFloat σ_impl c v =
                             (fun x => checkFloat σ_impl x.fst x.snd) (c, v) := by
  intro c v
  rfl
```

-/

-- Pattern 6: The complete working solution pattern
-- Simulating the actual toSubstTyped problem

def simulated_toSubstTyped (items : List (String × String)) : Option Bool :=
  items.allM (fun x => x.fst.length > 0 && x.snd.length > 0)

-- We have a proof with different pattern style
def simulated_all_true_with_tuples
    (items : List (String × String))
    (h : items.allM (fun (c, v) => c.length > 0 && v.length > 0) = some true) :
  ∃ result, simulated_toSubstTyped items = some result := by
  -- Method 1: Show the patterns are the same via simp
  simp only at h
  use true
  exact h

/-
EXERCISE: Complete this proof simulating the toSubstTyped_of_allM_true structure.

def checkFloat_sim (c : String) (v : String) : Bool :=
  c.length > 0 && v.length > 0

def toSubstTyped_sim (floats : List (String × String)) : Option (List String) :=
  floats.allM (fun x => checkFloat_sim x.fst x.snd)

theorem toSubstTyped_of_allM_true_sim
    (floats : List (String × String))
    (hAll : floats.allM (fun (c, v) => checkFloat_sim c v) = some true) :
  ∃ σ_typed : List String, toSubstTyped_sim floats = some σ_typed := by
  -- TODO: Extract witness using the pattern mismatch solution
  -- Hint: normalize the patterns first
  sorry
-/

/-
CONCEPTUAL SUMMARY:

When working with higher-order predicates and allM/allMonad:
1. Pattern matching is strict: `fun (a,b) =>` ≠ `fun x => ... x.fst x.snd` syntactically
2. But they're extensionally equal: both define the same function
3. Solution: Use simp, Function.ext, or unfold to normalize before comparing

The real issue in toSubstTyped_of_allM_true:
- hAll: proven with pattern `fun (c, v) => ...`
- toSubstTyped: implemented with pattern `fun x => ... x.fst x.snd`
- Need to show the patterns match

Tactics that help:
- `simp only [...]` to reduce both to normal form
- `unfold ...` to expand definitions
- `Function.ext` to prove function equality pointwise
- `rfl` after normalization (they may be definitionally equal)
-/
