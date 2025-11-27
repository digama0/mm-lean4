/-
# Loop Invariant Infrastructure for Lean 4

Reusable lemmas for reasoning about state machine executions.
These address common proof challenges that arise when working with do-notation loops.

## Key Patterns Addressed:
1. Error monotonicity in state machines
2. Execution trace reasoning
3. Contrapositive arguments for error-free invariants
-/

import Metamath.Spec

namespace LoopInvariant

/-! ## State Machine Execution -/

/-- A deterministic state transition relation -/
structure StateMachine (S : Type) where
  step : S → Option S

/-- Execution trace: sequence of states from start to end -/
inductive ExecutionTrace {S : Type} (sm : StateMachine S) : S → S → Type where
  | refl (s : S) : sm.step s = none → ExecutionTrace sm s s
  | trans (s₁ s₂ s₃ : S) : sm.step s₁ = some s₂ → ExecutionTrace sm s₂ s₃ → ExecutionTrace sm s₁ s₃

/-- Error monotonicity for state machines -/
def StateMachine.errorMonotonic {S : Type} (sm : StateMachine S) (error : S → Bool) : Prop :=
  ∀ s₁ s₂, sm.step s₁ = some s₂ → error s₁ = true → error s₂ = true

/-- If error is monotonic and final state has no error, all states in trace have no error.
    This is the key lemma for proving invariants via contrapositive:
    "If any intermediate state had error, final state would have error" -/
theorem ExecutionTrace.all_error_free {S : Type} (sm : StateMachine S) (error : S → Bool)
    (h_mono : sm.errorMonotonic error)
    {s_init s_final : S} (trace : ExecutionTrace sm s_init s_final) :
    error s_final = false →
    error s_init = false := by
  intro h_final
  induction trace with
  | refl s _ => exact h_final
  | trans s₁ s₂ s₃ h_step _ ih =>
    have h_s2 := ih h_final
    -- By contrapositive of monotonicity: if s₁.error = true, then s₂.error = true
    -- But s₂.error = false (from ih), so s₁.error = false
    cases h_s1 : error s₁ with
    | false => rfl
    | true =>
      have h_bad := h_mono s₁ s₂ h_step h_s1
      -- h_bad : error s₂ = true, h_s2 : error s₂ = false
      -- This is a contradiction: h_bad says error s₂ = true, h_s2 says error s₂ = false
      simp only [h_s2, Bool.false_eq_true] at h_bad

/-! ## General Inductive Trace Properties -/

/-- Any property that propagates forward through steps propagates through traces -/
theorem ExecutionTrace.property_propagates {S : Type} (sm : StateMachine S) (P : S → Prop)
    (h_step : ∀ s₁ s₂, sm.step s₁ = some s₂ → P s₁ → P s₂)
    {s_init s_final : S} (trace : ExecutionTrace sm s_init s_final) :
    P s_init → P s_final := by
  intro h_init
  induction trace with
  | refl s _ => exact h_init
  | trans s₁ s₂ s₃ h_step_eq _ ih =>
    have h_s2 := h_step s₁ s₂ h_step_eq h_init
    exact ih h_s2

/-- Contrapositive: if final state lacks property and property propagates forward,
    initial state lacked property -/
theorem ExecutionTrace.property_contrapositive {S : Type} (sm : StateMachine S) (P : S → Prop)
    [DecidablePred P]
    (h_step : ∀ s₁ s₂, sm.step s₁ = some s₂ → P s₁ → P s₂)
    {s_init s_final : S} (trace : ExecutionTrace sm s_init s_final) :
    ¬P s_final → ¬P s_init := by
  intro h_not_final h_init
  have := ExecutionTrace.property_propagates sm P h_step trace h_init
  exact h_not_final this

end LoopInvariant
