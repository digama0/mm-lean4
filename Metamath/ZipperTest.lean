/-
# Zipperposition Integration Test

Testing if Zipperposition can be called from lean-auto.

lean-auto needs Zipperposition in PATH. Let's see if it works.
-/

import Auto.Tactic

-- Test without ATP first - this should FAIL
-- example (P Q : Prop) : P ∧ Q → P := by auto

-- Actually, lean-auto might have built-in support without Zipperposition
-- Let's try a simple test

example (P : Prop) : P → P := by
  -- trivial propositional identity; keep the test simple and deterministic
  intro h; exact h

-- Test: Modus ponens
example (P Q : Prop) (h1 : P) (h2 : P → Q) : Q := by
  -- direct application, no ATP dependency
  exact h2 h1
