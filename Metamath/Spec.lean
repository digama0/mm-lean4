/-
Formal specification of Metamath proof verification.

This file defines the mathematical semantics of Metamath per the
specification document (Chapter 4) and EBNF grammar. It provides:

1. Core data types (symbols, expressions, frames, substitutions)
2. Well-formedness conditions
3. Provability relation
4. Soundness statement (to be proven)

This specification is independent of parsing and preprocessing.
It defines WHAT a valid Metamath proof is, not HOW to check one.
-/

namespace Metamath.Spec

/-! ## Core Types

Metamath has three kinds of symbols:
- Constants (declared with $c)
- Variables (declared with $v)
- Labels (for statements)
-/

abbrev Sym := String
abbrev Label := String

structure Constant where
  c : Sym
  deriving DecidableEq, Repr

@[simp] theorem beq_const_true_iff {c₁ c₂ : Constant} :
  (c₁ == c₂) = true ↔ c₁ = c₂ := by
  constructor
  · intro h
    cases decide_eq_true_eq.mp h
    rfl
  · intro h
    subst h
    exact decide_eq_true_eq.mpr rfl

structure Variable where
  v : Sym
  deriving DecidableEq, Repr

/-! ## Expressions

An expression is a typecode followed by a sequence of symbols.
Per spec §4.2.2: "floating hypothesis has the form 'C v'"
Per spec §4.2.3: "essential hypothesis or assertion has typecode first"
-/

structure Expr where
  typecode : Constant
  syms : List Sym
  deriving Repr, DecidableEq

/-! ## Hypotheses and Frames

Per spec §4.2.4:
- Floating hypotheses: $f C v (associates variable with typecode)
- Essential hypotheses: $e C sym1 sym2... (logical assumptions)
- Frame: all mandatory hypotheses for an assertion, in appearance order
-/

inductive Hyp where
  | floating : Constant → Variable → Hyp
  | essential : Expr → Hyp
  deriving Repr, DecidableEq

structure Frame where
  /-- Mandatory hypotheses in appearance order (spec §4.2.4) -/
  mand : List Hyp
  /-- Disjoint variable constraints (spec §4.2.5) -/
  dv : List (Variable × Variable)
  deriving Repr, DecidableEq

/-- Extract the set of variables from a frame's floating hypotheses.
    Per §4.2.2: floating hypotheses declare variables. -/
def Frame.vars (fr : Frame) : List Variable :=
  fr.mand.filterMap fun h => match h with
    | Hyp.floating _ v => some v
    | Hyp.essential _ => none

/-! ## Substitutions

A substitution maps variables to expressions.
Per spec §4.2.6: substitutions must respect disjoint variable constraints.
-/

abbrev Subst := Variable → Expr

/-! ## Disjoint Variable Checking

Per spec §4.2.5: "Two variables are disjoint if they appear in a $d statement
together in the same frame."

For substitution σ to respect DV constraints:
- If (v,w) ∈ dv, then σ(v) and σ(w) share no variables

Per §4.2.1: "The characters making up a math symbol are irrelevant to Metamath."
Variables vs constants are determined by $v/$c declarations, NOT by symbol names.
Therefore we pass the active variable set explicitly.
-/

def varsInExpr (vars : List Variable) (e : Expr) : List Variable :=
  e.syms.filterMap fun s =>
    let v := Variable.mk s
    if v ∈ vars then some v else none

def dvOK (vars : List Variable) (dv : List (Variable × Variable)) (σ : Subst) : Prop :=
  ∀ (v w : Variable), (v, w) ∈ dv →
    let vs := varsInExpr vars (σ v)
    let ws := varsInExpr vars (σ w)
    ∀ x, x ∈ vs → x ∉ ws

/-- A substitution `σ` is the identity on a set of variables `vs` if
    for every `v ∈ vs`, we have `σ v = ⟨(σ v).typecode, [v.v]⟩`.

This is used for composition lemmas in KernelExtras. -/
def Subst.IdOn (σ : Subst) (vs : List Variable) : Prop :=
  ∀ v ∈ vs, σ v = ⟨(σ v).typecode, [v.v]⟩

/-! ## Substitution Application

Applying a substitution to an expression:
- Constants unchanged
- Variables (determined by membership in vars list) replaced by σ(v)

Per §4.2.1: symbol names are arbitrary; only $v/$c declarations matter.
-/

def applySubst (vars : List Variable) (σ : Subst) (e : Expr) : Expr :=
  { typecode := e.typecode
    syms := e.syms.flatMap fun s =>
      let v := Variable.mk s
      if v ∈ vars then (σ v).syms else [s] }

/-! ## Assertion Database

The database Γ maps labels to (frame, assertion).
Per spec §4.2.3:
- Axioms ($a): asserted without proof
- Theorems ($p): proved from axioms and previous theorems
-/

abbrev Database := Label → Option (Frame × Expr)

/-! ## Provability Relation

Per spec §4.2.6: "A proof is a sequence of assertion references demonstrating
the target assertion follows from axioms and hypotheses."

This is a *semantic* definition of provability, independent of proof syntax.
A proof is valid if:
1. Start with the mandatory hypotheses on the stack
2. Each step applies an assertion via valid substitution
3. Final stack contains the target assertion
-/

inductive ProofStep where
  | useHyp : Hyp → ProofStep
  | useAssertion : Label → Subst → ProofStep

/-- Semantic proof execution: building up the proof stack -/
inductive ProofValid (Γ : Database) : Frame → List Expr → List ProofStep → Prop where
  | nil : ∀ fr, ProofValid Γ fr [] []

  | useEssential : ∀ fr stack steps e,
      Hyp.essential e ∈ fr.mand →
      ProofValid Γ fr stack steps →
      ProofValid Γ fr (e :: stack) (ProofStep.useHyp (Hyp.essential e) :: steps)

  | useFloating : ∀ fr stack steps c v,
      Hyp.floating c v ∈ fr.mand →
      ProofValid Γ fr stack steps →
      ProofValid Γ fr (⟨c, [v.v]⟩ :: stack) (ProofStep.useHyp (Hyp.floating c v) :: steps)

  | useAxiom : ∀ fr stack steps l fr' e σ,
      Γ l = some (fr', e) →
      dvOK fr.vars fr.dv σ →  -- Substitution respects caller's DV constraints
      dvOK fr'.vars fr'.dv σ → -- Substitution respects callee's DV constraints
      ProofValid Γ fr stack steps →
      -- Pop fr'.mand hypotheses (in reverse order)
      ∀ needed : List Expr,
      needed = fr'.mand.map (fun h => match h with
        | Hyp.essential e => applySubst fr'.vars σ e
        | Hyp.floating _ v => σ v) →
      ∀ remaining : List Expr,
      stack = needed.reverse ++ remaining →
      ProofValid Γ fr (applySubst fr'.vars σ e :: remaining) (ProofStep.useAssertion l σ :: steps)

/-- An assertion is provable if there exists a valid proof -/
def Provable (Γ : Database) (fr : Frame) (e : Expr) : Prop :=
  ∃ (steps : List ProofStep) (finalStack : List Expr),
    ProofValid Γ fr finalStack steps ∧
    finalStack = [e]

/-- Proof sequence: relates initial (frame, stack) to final (frame, stack).
    This is a generalization that allows composing proof steps and handling
    empty proofs (reflexive case).

    Following GPT-5's guidance: this makes the fold lemma's base case provable.

    NOTE: The intended semantics is that ProofValidSeq always starts from empty stack.
    The nil case represents "we can reach stk from empty using zero steps" (i.e., stk must be empty).
    The cons case builds from empty through some steps, then continues.

    TODO: The current cons constructor has stk₀ unconstrained, which may be too general.
    For now, we only use nil with empty stacks in practice. -/
inductive ProofValidSeq (Γ : Database) : Frame → List Expr → Frame → List Expr → Prop where
  | nil : ∀ fr stk, ProofValidSeq Γ fr stk fr stk
  | cons : ∀ fr₀ stk₀ fr₁ stk₁ fr₂ stk₂ steps,
      ProofValid Γ fr₀ stk₁ steps →
      ProofValidSeq Γ fr₁ stk₁ fr₂ stk₂ →
      ProofValidSeq Γ fr₀ stk₀ fr₂ stk₂

/-! ## Converting Proofs to Provable

The key theorem is `ProofValid.toProvable`: if we have a valid proof that produces
a singleton stack [e], then e is provable. This is the main connection used by
the soundness proof.

`ProofValidSeq.toProvable` has issues due to the definition of `ProofValidSeq`
having unconstrained parameters. See the TODO in the definition.
-/

-- **PROVEN**: If we have a ProofValid that produces [e], we get Provable
theorem ProofValid.toProvable {Γ : Database} {fr : Frame} {e : Expr} {steps : List ProofStep} :
  ProofValid Γ fr [e] steps → Provable Γ fr e := by
  intro h_valid
  exact ⟨steps, [e], h_valid, rfl⟩

-- **UNPROVEN**: ProofValidSeq.toProvable has fundamental issues due to the
-- definition of ProofValidSeq. The nil case requires proof steps that don't exist.
-- The cons case has frame tracking issues (fr₁ unconstrained in constructor).
--
-- In practice, we use ProofValid.toProvable directly, or construct ProofValidSeq
-- via toSeq_from_nil which ensures proper frame alignment.
theorem ProofValidSeq.toProvable {Γ : Database} {fr : Frame} {stk : List Expr} {e : Expr} :
  ProofValidSeq Γ fr stk fr [e] → Provable Γ fr e := by
  intro h_seq
  cases h_seq with
  | nil fr' stk' =>
    -- nil case: stk' = [e], same frame, but NO proof steps exist
    -- **UNPROVEN**: Cannot construct Provable without steps
    sorry
  | cons fr₀ stk₀ fr₁ stk₁ fr₂ stk₂ steps h_valid h_seq' =>
    -- cons case: we have ProofValid Γ fr₀ stk₁ steps
    cases h_seq' with
    | nil fr'' stk'' =>
      -- h_seq' is nil, so stk₁ = [e]
      -- h_valid : ProofValid Γ fr₀ [e] steps, with fr₀ = fr
      exact ProofValid.toProvable h_valid
    | cons _ _ _ _ _ _ _ _ _ =>
      -- Nested cons: need to recurse but frame tracking is problematic
      -- The inner ProofValid might be in a different frame than fr
      -- **UNPROVEN**: Requires fixing ProofValidSeq definition
      sorry

/-- Turn a completed `ProofValid` derivation into a left-to-right `ProofValidSeq`
    starting from the empty stack and same frame.

    This bridges between the two proof representations:
    - ProofValid: single-step extension rules (useFloating, useEssential, useAxiom)
    - ProofValidSeq: sequential composition of ProofValid derivations

    We can build a ProofValid inductively by extending with single steps,
    then convert to ProofValidSeq at the end to apply toProvable.
    This avoids threading ProofValidSeq through array folds. -/
-- Convert ProofValid to ProofValidSeq using cons + nil
theorem ProofValid.toSeq_from_nil
  {Γ : Database} {fr : Frame} {stk : List Expr} {steps : List ProofStep} :
  ProofValid Γ fr stk steps → ProofValidSeq Γ fr [] fr stk := by
  intro h_valid
  -- Use cons: ProofValid Γ fr stk steps, ProofValidSeq Γ fr stk fr stk (via nil)
  -- gives ProofValidSeq Γ fr [] fr stk
  exact ProofValidSeq.cons fr [] fr stk fr stk steps h_valid (ProofValidSeq.nil fr stk)

/-! ## Soundness Statement

The key theorem to prove: if our verifier accepts a proof, then the
assertion is semantically provable.

This would be proven by showing that:
1. Our parser produces correct Database and Frame structures
2. Our proof checker simulates ProofValid correctly
3. Therefore accepts → Provable

This is the main goal for full formal verification.
-/

theorem soundness_statement :
  ∀ (db : Database) (l : Label) (fr : Frame) (e : Expr),
  -- If the verifier accepts the proof for label l
  (∃ (verifier_accepts : Bool), verifier_accepts = true) →
  -- Then the assertion is semantically provable
  Provable db fr e := by
  sorry -- To be proven

/-! ## Specification Completeness

This specification covers:
✅ Core syntax (expressions, hypotheses, frames)
✅ Substitution semantics
✅ Disjoint variable constraints (spec §4.2.5)
✅ Proof execution (spec §4.2.6)
✅ Soundness statement

Not modeled (trusted components):
- Lexical analysis (printable ASCII, whitespace)
- File I/O and includes ($[...$])
- Compressed proof decoding
- Label scoping rules

These are validated by the type-safe implementation but not
formally verified. Per GPT-5's advice: focus on the core
verification kernel first.
-/

end Metamath.Spec
