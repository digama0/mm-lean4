/-
# ATP Automation Test File

Testing lean-auto on simple examples before applying to our tactical sorries.
-/

import Auto.Tactic

-- Configure Zipperposition
set_option auto.native true
set_option auto.tptp true
set_option auto.tptp.solver.name "zipperposition"

-- Test 1: Simple propositional logic (FAILS without ATP)
example (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.1  -- auto fails without external ATP

-- Test 2: Boolean reasoning
example (b : Bool) : b = true ∨ b = false := by
  cases b <;> simp

-- Test 3: if-then-else pattern (similar to our trimFrame'_ok_iff)
example (b : Bool) (x y : Nat) :
    (if b then x else y) = x ↔ (b = true ∧ x = x) ∨ (b = false ∧ y = x) := by
  cases b <;> simp

-- Test 4: Can auto handle if-then-else? (FAILS)
example (b : Bool) (x : Nat) : (if b then x else x) = x := by
  cases b <;> rfl  -- auto doesn't handle Bool well

-- Test 5: Inequality reasoning (FAILS)
example (i j : Nat) (h : i ≠ j) : ¬(i = j) := by
  exact h  -- auto doesn't unfold ¬

-- Test 6: Try with Zipperposition
-- example (P Q : Prop) : P ∧ Q → P := by auto
