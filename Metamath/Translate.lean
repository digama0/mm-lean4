-- WIP stuff. see Metamath.Verify for the verifier

import Lean.Elab.Term
import Metamath.Verify

namespace Metamath
open Lean Elab
open Verify in
partial def foo : TermElabM Unit := do
  let h ← IO.FS.Handle.mk "/home/mario/Documents/metamath/mm/iset.mm" IO.FS.Mode.read
  let rec loop (s : ParserState) (base : Nat) : IO (Except ParserState DB) := do
    let buf ← h.read 1024
    if buf.isEmpty then
      pure $ Except.ok $ s.done base
    else
      let s := s.feedAll base buf
      if s.db.error?.isSome then pure $ Except.error s
      else loop s (base + buf.size)
  match ← loop Inhabited.default 0 with
  | Except.ok _ => pure ()
  | Except.error s' => match s'.db.error? with
    | some ⟨Error.ax _pos l f fr, _i⟩ =>
      IO.println s!"axiom {l}: {fr} |- {f}"
    | some ⟨Error.thm _pos l f fr, _i⟩ =>
      IO.println s!"theorem {l}: {fr} |- {f}"
    | some ⟨Error.error pos msg, _⟩ =>
      IO.println s!"at {pos}: {msg}"
    | _ => pure ()

-- #eval foo

def CN := String
instance : Inhabited CN := inferInstanceAs (Inhabited String)
instance : DecidableEq CN := inferInstanceAs (DecidableEq String)

structure VR where (type : CN) (i : Nat)
deriving DecidableEq

inductive Sym
  | const (c : CN)
  | var (n : VR)
  deriving Inhabited, DecidableEq
open Sym

instance : Coe String Sym := ⟨const⟩
def Sym.isVar : Sym → Bool
  | const _ => false
  | var _ => true

def Expr := List Sym
def VR.expr (v : VR) : Expr := [var v]

instance : Append Expr := inferInstanceAs (Append (List Sym))
instance : Membership Sym Expr := inferInstanceAs (Membership Sym (List Sym))
def Expr.sn (s : Sym) : Expr := [s]
instance : Coe String Expr := ⟨fun c => Expr.sn c⟩
instance : Coe VR Expr := ⟨fun v => Expr.sn (var v)⟩
def Expr.cons (c : String) : Expr → Expr := List.cons c
def Expr.mem (e : Expr) (v : VR) : Prop := var v ∈ e

scoped notation:50 a:51 " ∈' " b:51 => Expr.mem b a

def Expr.vars : Expr → List VR
  | [] => []
  | const _ :: e => vars e
  | var v :: e => v :: vars e

def Expr.subst (σ : VR → Expr) : Expr → Expr
  | [] => []
  | const c :: e => const c :: subst σ e
  | var v :: e => σ v ++ subst σ e

theorem Expr.subst_id : (e : Expr) → Expr.subst VR.expr e = e
  | [] => rfl
  | const c :: e => congrArg (const c :: .) (subst_id e)
  | var v :: e => congrArg (var v :: .) (subst_id e)

theorem Expr.subst_append (σ) : (e₁ e₂ : Expr) → Expr.subst σ (e₁ ++ e₂) = e₁.subst σ ++ e₂.subst σ
  | [], _ => rfl
  | const c :: (e₁ : Expr), e₂ => by
    rw [subst, List.cons_append, subst, subst_append ..]; rfl
  | var v :: e, e₂ => by
    rw [List.cons_append]; simp only [Expr.subst]; rw [List.append_assoc, subst_append ..]

theorem Expr.mem_subst {σ a} : {e : Expr} → a ∈' Expr.subst σ e → ∃ b, b ∈' e ∧ a ∈' σ b
  | const _ :: _, .tail _ h => let ⟨b, h₁, h₂⟩ := mem_subst h; ⟨b, .tail _ h₁, h₂⟩
  | var v :: _, h =>
    match List.mem_append.1 h with
    | Or.inl h => ⟨v, .head _, h⟩
    | Or.inr h => let ⟨b, h₁, h₂⟩ := mem_subst h; ⟨b, .tail _ h₁, h₂⟩

def subst.trans (σ σ' : VR → Expr) (v : VR) : Expr := (σ v).subst σ'

theorem Expr.subst_tr (σ σ' : VR → Expr) : (e : Expr) →
    e.subst (subst.trans σ σ') = (e.subst σ).subst σ'
  | [] => rfl
  | const c :: e => congrArg (const c :: .) (subst_tr _ _ e)
  | var v :: e => by simp only [subst]; rw [subst_append, subst_tr _ _ e]; rfl

def Formula := CN × Expr

def Formula.subst (σ : VR → Expr) : Formula → Formula
  | (c, e) => (c, e.subst σ)

theorem Formula.subst_id : (e : Formula) → Formula.subst VR.expr e = e
  | (c, e) => congrArg (c, .) e.subst_id

theorem Formula.subst_tr (σ σ' : VR → Expr) : (e : Formula) →
    e.subst (subst.trans σ σ') = (e.subst σ).subst σ'
  | (c, e) => congrArg (c, .) (e.subst_tr _ _)

def VR.vhyp (v : VR) : Formula := (v.type, [var v])
instance : Coe VR Formula := ⟨VR.vhyp⟩

def Expr.δ (a b : Expr) : Bool :=
  a.all fun
  | const _ => true
  | var a => b.all fun
    | const _ => true
    | var b => a != b

structure DJ where
  disj : VR → VR → Prop
  irr : ¬ disj x x
  symm : disj x y → disj y x

instance : CoeFun DJ (fun _ => VR → VR → Prop) := ⟨DJ.disj⟩
instance : LE DJ := ⟨fun dj dj' => ∀ a b, dj a b → dj' a b⟩

theorem DJ.refl (dj : DJ) : dj ≤ dj := fun _ _ => id

theorem DJ.ne (dj : DJ) {a b} (h : dj a b) : a ≠ b :=
  fun e => by cases e; exact dj.irr h

theorem DJ.ext : {dj₁ dj₂ : DJ} → (∀ a b, dj₁ a b ↔ dj₂ a b) → dj₁ = dj₂
  | ⟨dj₁, _, _⟩, ⟨dj₂, _, _⟩, h =>
    have : dj₁ = dj₂ := funext fun a => funext fun b => propext (h a b)
    by cases this; rfl

theorem DJ.le_antisymm {dj₁ dj₂ : DJ} (H₁ : dj₁ ≤ dj₂) (H₂ : dj₂ ≤ dj₁) : dj₁ = dj₂ :=
  DJ.ext fun _ _ => ⟨H₁ _ _, H₂ _ _⟩

def DJ.mk' (disj : List (VR × VR)) : DJ where
  disj := fun a b => a ≠ b ∧ ((a, b) ∈ disj ∨ (b, a) ∈ disj)
  irr := fun h => h.1 rfl
  symm := fun ⟨h, h'⟩ => ⟨h.symm, h'.symm⟩

def Expr.disjoint (dj : DJ) (e₁ e₂ : Expr) : Prop :=
  ∀ a b, a ∈' e₁ → b ∈' e₂ → dj a b

theorem Expr.disjoint.mono {dj₁ dj₂ : DJ} (h : dj₁ ≤ dj₂) {e₁ e₂}
    (H : Expr.disjoint dj₁ e₁ e₂) : Expr.disjoint dj₂ e₁ e₂ :=
  fun a b ha hb => h _ _ (H a b ha hb)

def DJ.subst (σ : VR → Expr) (dj dj' : DJ) :=
  ∀ a b, dj a b → (σ a).disjoint dj' (σ b)

theorem DJ.subst.mono {σ : VR → Expr} {dj₁ dj₂ dj₁' dj₂' : DJ}
    (h : dj₂ ≤ dj₁) (h' : dj₁' ≤ dj₂') (H : dj₁.subst σ dj₁') : dj₂.subst σ dj₂' :=
  fun _ _ d => Expr.disjoint.mono h' (H _ _ (h _ _ d))

def DJ.trim (dj : DJ) (P : VR → Prop) : DJ :=
  { disj := fun x y => dj x y ∧ P x ∧ P y
    irr := fun x => dj.irr x.1
    symm := fun ⟨h₁, h₂, h₃⟩ => ⟨dj.symm h₁, h₃, h₂⟩ }

theorem DJ.trim.mono {dj₁ dj₂ : DJ} (hdj : dj₁ ≤ dj₂) {P Q : VR → Prop}
    (pq : ∀ x, P x → Q x) : dj₁.trim P ≤ dj₂.trim Q :=
  fun _ _ ⟨h, ha, hb⟩ => ⟨hdj _ _ h, pq _ ha, pq _ hb⟩

def DJ.trimmed (dj : DJ) (P : VR → Prop) : Prop :=
  ∀ a b, dj a b → P a ∧ P b

theorem DJ.trimmed.mono (dj : DJ) {P Q : VR → Prop}
    (h : ∀ x, P x → Q x) (H : dj.trimmed P) : dj.trimmed Q
  | a, b, d => let ⟨h₁, h₂⟩ := H a b d; ⟨h _ h₁, h _ h₂⟩

theorem DJ.trim_le_self (dj : DJ) (P : VR → Prop) : dj.trim P ≤ dj := fun _ _ d => d.1

theorem DJ.trim.trimmed (dj : DJ) (P : VR → Prop) : (dj.trim P).trimmed P := fun _ _ h => h.2

theorem DJ.trimmed.trim_eq {dj : DJ} {P} (h : dj.trimmed P) : dj.trim P = dj :=
  DJ.ext fun _ _ => ⟨fun h => h.1, fun h' => ⟨h', h _ _ h'⟩⟩

def DJ.untrim (dj : DJ) (P : VR → Prop) : DJ where
  disj := fun x y => x ≠ y ∧ (P x → P y → dj x y)
  irr := fun x => x.1 rfl
  symm := fun ⟨h₁, h₂⟩ => ⟨h₁.symm, fun x y => dj.symm (h₂ y x)⟩

theorem DJ.untrim.mono {dj₁ dj₂ : DJ} (hdj : dj₁ ≤ dj₂) {P Q : VR → Prop}
    (qp : ∀ x, Q x → P x) : dj₁.untrim P ≤ dj₂.untrim Q :=
  fun _ _ ⟨h₁, h₂⟩ => ⟨h₁, fun ha hb => hdj _ _ (h₂ (qp _ ha) (qp _ hb))⟩

theorem DJ.trim_le {dj₁ dj₂ : DJ} {P} : dj₁.trim P ≤ dj₂ ↔ dj₁ ≤ dj₂.untrim P :=
  ⟨fun H _ _ h => ⟨dj₁.ne h, fun ha hb => H _ _ ⟨h, ha, hb⟩⟩,
   fun H _ _ ⟨h, ha, hb⟩ => (H _ _ h).2 ha hb⟩

theorem DJ.self_le_untrim (dj : DJ) (P : VR → Prop) : dj ≤ dj.untrim P :=
  DJ.trim_le.1 $ DJ.trim_le_self _ _

theorem DJ.trim_untrim (dj : DJ) (P : VR → Prop) : (dj.untrim P).trim P = dj.trim P :=
  DJ.le_antisymm (fun _ _ ⟨h, ha, hb⟩ => ⟨h.2 ha hb, ha, hb⟩)
    (DJ.trim.mono (DJ.self_le_untrim _ _) (fun _ => id))

theorem DJ.untrim_trim (dj : DJ) (P : VR → Prop) : (dj.trim P).untrim P = dj.untrim P :=
  DJ.le_antisymm (DJ.untrim.mono (DJ.trim_le_self _ _) (fun _ => id))
    fun _ _ ⟨h, H⟩ => ⟨h, fun ha hb => ⟨H ha hb, ha, hb⟩⟩

structure Context where
  hyps : List Formula
  dj : DJ

def Context.mk' (disj : List (VR × VR)) (hyps : List Formula) : Context :=
  ⟨hyps, DJ.mk' disj⟩

instance : LE Context := ⟨fun Γ Γ' => (∀ a, a ∈ Γ.hyps → a ∈ Γ'.hyps) ∧ Γ.dj ≤ Γ'.dj⟩

theorem Context.refl (Γ : Context) : Γ ≤ Γ := ⟨fun _ => id, DJ.refl _⟩

structure Statement where
  ctx : Context
  fmla : Formula

instance : LE Statement := ⟨fun s s' => s.ctx ≤ s'.ctx ∧ s.fmla = s'.fmla⟩

theorem Statement.refl (s : Statement) : s ≤ s := ⟨Context.refl _, rfl⟩

def Statement.vars (s : Statement) : List VR :=
  (s.fmla :: s.ctx.hyps).flatMap fun e => e.2.vars

theorem Statement.vars.mono' {s₁ s₂ : Statement}
    (H : ∀ a, a ∈ s₁.ctx.hyps → a ∈ s₂.ctx.hyps) (H₂ : s₁.fmla = s₂.fmla)
    (v) : v ∈ s₁.vars → v ∈ s₂.vars := by
  simp only [vars, List.mem_flatMap, List.mem_cons, H₂]
  exact fun ⟨a, b, c⟩ => ⟨a, b.imp_right (H _), c⟩

theorem Statement.vars.mono {s₁ s₂ : Statement} (H : s₁ ≤ s₂) : ∀ v, v ∈ s₁.vars → v ∈ s₂.vars :=
  Statement.vars.mono' H.1.1 H.2

def Statement.trim (s : Statement) : Statement :=
  ⟨⟨s.ctx.hyps, s.ctx.dj.trim fun v => v ∈ s.vars⟩, s.fmla⟩

def Statement.untrim' (s : Statement) (P : VR → Prop) : Statement :=
  ⟨⟨s.ctx.hyps, s.ctx.dj.untrim P⟩, s.fmla⟩
def Statement.untrim (s : Statement) : Statement := s.untrim' fun v => v ∈ s.vars

theorem Statement.trim_le_self (s : Statement) : s.trim ≤ s :=
  ⟨⟨fun _ => id, DJ.trim_le_self _ _⟩, rfl⟩

theorem Statement.self_le_untrim' (s : Statement) (P) : s ≤ s.untrim' P :=
  ⟨⟨fun _ => id, DJ.self_le_untrim _ _⟩, rfl⟩
theorem Statement.self_le_untrim (s : Statement) : s ≤ s.untrim := s.self_le_untrim' _

theorem Statement.trim.mono {s₁ s₂ : Statement} (h : s₁ ≤ s₂) : s₁.trim ≤ s₂.trim :=
  ⟨⟨h.1.1, DJ.trim.mono h.1.2 (Statement.vars.mono h)⟩, h.2⟩

theorem Statement.untrim'.mono {s₁ s₂ : Statement} {P Q}
    (H : ∀ x, Q x → P x) (h : s₁ ≤ s₂) : s₁.untrim' P ≤ s₂.untrim' Q :=
  ⟨⟨h.1.1, DJ.untrim.mono h.1.2 H⟩, h.2⟩
theorem Statement.untrim.mono {s₁ s₂ : Statement}
    (H : s₁.ctx.hyps = s₂.ctx.hyps) (h : s₁ ≤ s₂) : s₁.untrim ≤ s₂.untrim :=
  Statement.untrim'.mono (Statement.vars.mono' (by rw [H]; exact fun _ => id) h.2.symm) h

theorem Statement.trim_vars (s : Statement) : s.trim.vars = s.vars := rfl
theorem Statement.untrim'_vars (s : Statement) (P) : (s.untrim' P).vars = s.vars := rfl
theorem Statement.untrim_vars (s : Statement) : s.untrim.vars = s.vars := rfl

theorem Statement.trim_untrim (s : Statement) : s.untrim.trim = s.trim := by
  simp only [trim, untrim_vars]; simp only [untrim, untrim', DJ.trim_untrim]

theorem Statement.untrim_trim (s : Statement) : s.trim.untrim = s.untrim := by
  simp only [untrim, untrim', trim_vars]; simp only [trim, DJ.untrim_trim]

theorem Statement.trim_le {s₁ s₂ : Statement} (e : s₁.vars = s₂.vars) :
    s₁.trim.ctx ≤ s₂.ctx ↔ s₁.ctx ≤ s₂.untrim.ctx :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, DJ.trim_le.1 $ by rw [← e]; exact h₂⟩,
   fun ⟨h₁, h₂⟩ => ⟨h₁, DJ.trim_le.2 $ by rw [e]; exact h₂⟩⟩

def Statement.trimmed (s : Statement) : Prop := s.ctx.dj.trimmed fun v => v ∈ s.vars

theorem Statement.trim.trimmed (s : Statement) : s.trim.trimmed := DJ.trim.trimmed _ _

theorem Statement.trimmed.trim_eq : {s : Statement} → s.trimmed → s.trim = s
  | ⟨⟨a, b⟩, c⟩, h => by simp only [trim]; rw [DJ.trimmed.trim_eq h]

inductive Provable (axs : Statement → Prop) (Γ : Context) : Formula → Prop
  | hyp (h) : h ∈ Γ.hyps → Provable axs Γ h
  | var (v:VR) : Provable axs Γ v
  | ax (σ) {ax} : axs ax → ax.ctx.dj.subst σ Γ.dj →
    (∀ h, h ∈ ax.ctx.hyps ∨ (∃ v:VR, h = v) → Provable axs Γ (h.subst σ)) →
    Provable axs Γ (ax.fmla.subst σ)

theorem Provable.mono {axs₁ axs₂} (haxs : ∀ a, axs₁ a → axs₂ a)
    {Γ₁ Γ₂} (hΓ : Γ₁ ≤ Γ₂) {e} (pr : Provable axs₁ Γ₁ e) : Provable axs₂ Γ₂ e := by
  induction pr with
  | hyp e h => exact hyp e (hΓ.1 _ h)
  | var v => exact var v
  | ax σ ha h₁ _ IH =>
    exact ax σ (haxs _ ha) (h₁.mono (DJ.refl _) hΓ.2) fun e h => IH _ h

def Statement.provable' (axs : Statement → Prop) (s : Statement) : Prop :=
  Provable axs s.ctx s.fmla

theorem Statement.provable'.mono {axs₁ axs₂} (haxs : ∀ a, axs₁ a → axs₂ a) :
    {s₁ s₂ : Statement} → s₁ ≤ s₂ → s₁.provable' axs₁ → s₂.provable' axs₂
  | ⟨_Γ₁, _⟩, ⟨_Γ₂, _⟩, ⟨hΓ, rfl⟩ => Provable.mono haxs hΓ

def Statement.provable (axs : Statement → Prop) (s : Statement) : Prop :=
  s.untrim.provable' axs

-- theorem Statement.provable.mono {axs₁ axs₂} (haxs : ∀ a, axs₁ a → axs₂ a) :
--   {s₁ s₂ : Statement} → s₁ ≤ s₂ → s₁.provable axs₁ → s₂.provable axs₂
-- | s₁, s₂, h, hs, pr =>
--   Statement.provable'.mono haxs (untrim'.mono (fun _ => id) hs) $
--   Statement.provable'.mono (fun _ => id) _ pr

theorem Statement.provable'.of {axs} {s : Statement} (h : s.provable' axs) : s.provable axs :=
  h.mono (fun _ => id) (self_le_untrim _)

theorem Statement.provable.trim {axs} {s : Statement} : s.trim.provable axs ↔ s.provable axs := by
  simp only [provable, untrim_trim]

theorem Provable.ax_self (axs : Statement → Prop) {ax} (H : axs ax) : ax.provable' axs := by
  have := Provable.ax (Γ := ax.ctx) VR.expr H ?disj ?hyp
  rw [Formula.subst_id] at this; exact this
  case disj =>
    intro a b h a' b' h₁ h₂
    match a', b', h₁, h₂ with | _, _, .head _, .head _ => ?_
    exact h
  case hyp =>
    intro fmla h
    match fmla, h with
    | fmla, Or.inl h => rw [Formula.subst_id]; exact Provable.hyp _ h
    | _, Or.inr ⟨v, rfl⟩ => exact Provable.var v

theorem Provable.trans' {axs Γ} (σ) {Γ' fmla} (pr : Provable axs Γ' fmla)
    (dj : Γ'.dj.subst σ Γ.dj)
    (hh : ∀ h, h ∈ Γ'.hyps ∨ (∃ v:VR, h = v) → Provable axs Γ (h.subst σ)) :
    Provable axs Γ (fmla.subst σ) := by
  induction pr with
  | hyp f h => exact hh _ (Or.inl h)
  | var v => exact hh _ (Or.inr ⟨v, rfl⟩)
  | @ax σ' a ha dj' hh' IH =>
    rw [← Formula.subst_tr]
    apply ax (subst.trans σ' σ) ha
    focus
      intros a b ab c d hc hd
      let ⟨e, ea, ce⟩ := Expr.mem_subst hc
      let ⟨f, fb, df⟩ := Expr.mem_subst hd
      refine dj _ _ ?_ _ _ ce df
      exact dj' _ _ ab _ _ ea fb
    focus { intros f; rw [Formula.subst_tr]; refine IH _ }

theorem Provable.trans'' {axs Γ σ} (s : Statement) : s.provable' axs →
    s.ctx.dj.subst σ Γ.dj →
    (∀ h, h ∈ s.ctx.hyps ∨ (∃ v:VR, h = v) → Provable axs Γ (h.subst σ)) →
    Provable axs Γ (s.fmla.subst σ) :=
  Provable.trans' (axs := axs) σ

def subst_of : List (VR × Expr) → VR → Expr
  | [], v => v
  | (a, e)::l, v => if a = v then e else subst_of l v

class Subst (σ : VR → Expr) (e : Expr) (e' : outParam Expr) where (out : e.subst σ = e')

instance [Subst σ e₁ e₁'] [Subst σ e₂ e₂'] : Subst σ (e₁ ++ e₂) (e₁' ++ e₂') :=
  ⟨by rw [Expr.subst_append, Subst.out, Subst.out]⟩

instance (s : String) : Subst σ s s := ⟨rfl⟩

instance (s : String) [Subst σ e e'] : Subst σ (s ++ e) (s ++ e') :=
  inferInstanceAs (Subst σ (Expr.sn _ ++ e) _)
instance (s : String) [Subst σ e e'] : Subst σ (e ++ s) (e' ++ s) :=
  inferInstanceAs (Subst σ (e ++ Expr.sn _) _)

def subst.ok (axs Γ) (σ : VR → Expr) := ∀ v, Provable axs Γ (v.type, σ v)

theorem subst.ok.nil {axs Γ} : subst.ok axs Γ (subst_of []) := Provable.var
theorem subst.ok.cons {axs Γ e σ} (x) (h₁ : Provable axs Γ (x.type, e))
    (h₂ : subst.ok axs Γ (subst_of σ)) : subst.ok axs Γ (subst_of ((x, e)::σ)) := by
  intro v
  simp only [subst_of]
  cases Decidable.em (x = v) with simp [h]
  | inl h => cases h; exact h₁
  | inr h => exact h₂ v

theorem Provable.thm {axs} {Γ : Context}
    {σ : VR → Expr} {dj hyps c s} (pr : Provable axs (Context.mk' dj hyps) (c, s))
    (hv : subst.ok axs Γ σ)
    (dj : (DJ.mk' dj).subst σ Γ.dj)
    (hh : ∀ h, h ∈ hyps → Provable axs Γ (h.subst σ))
    {e} [inst : Subst σ s e] : Provable axs Γ (c, e) := by
  rw [← inst.out]
  exact Metamath.Provable.trans' σ pr dj fun
    | f, Or.inl h => hh _ h
    | _, Or.inr ⟨v, rfl⟩ =>
      show Provable axs Γ (v.type, σ v ++ show Expr from []) by
      rw [List.append_nil]; exact hv v

theorem DJ_nil {σ dj'} : (DJ.mk' []).subst σ dj' | _, _, h => nomatch h
theorem DJ_cons {a b l σ dj'}
    (h₁ : (σ a).disjoint dj' (σ b))
    (h₂ : (DJ.mk' l).subst σ dj') : (DJ.mk' ((a, b) :: l)).subst σ dj'
  | _, _, ⟨_, Or.inl (List.Mem.head _)⟩ => h₁
  | _, _, ⟨_, Or.inr (List.Mem.head _)⟩ => fun x y hx hy => dj'.symm (h₁ y x hy hx)
  | _, _, ⟨h, Or.inl (List.Mem.tail _ h')⟩ => h₂ _ _ ⟨h, Or.inl h'⟩
  | _, _, ⟨h, Or.inr (List.Mem.tail _ h')⟩ => h₂ _ _ ⟨h, Or.inr h'⟩

theorem HH_nil {axs Γ σ} : ∀ h:Formula, h ∈ [] → Provable axs Γ (h.subst σ)
  | _, h => nomatch h

theorem HH_cons {axs Γ σ c f hyps}
    {e} [Subst σ f e] (h₁ : Provable axs Γ (c, e))
    (h₂ : ∀ h:Formula, h ∈ hyps → Provable axs Γ (h.subst σ)) :
    ∀ h:Formula, h ∈ (c, f)::hyps → Provable axs Γ (h.subst σ)
  | _, .head _ => by rw [← @Subst.out σ f e] at h₁; exact h₁
  | _, .tail _ h => h₂ _ h

class Typed (axs : outParam _) (c : outParam CN) (e : Expr) where
  type Γ : Provable axs Γ (c, e)

def Expr.ty (e) {axs c} [Typed axs c e] {Γ} : Provable axs Γ (c, e) := Typed.type Γ

-- This is a by hand translation of demo0.mm, ideally the tactic will write this

namespace Demo

def ze : Expr := "0"
instance : Subst σ ze ze := inferInstanceAs (Subst σ "0" _)

def pl (t r : Expr) : Expr := "(" ++ t ++ "+" ++ r ++ ")"
instance [Subst σ t t'] [Subst σ r r'] : Subst σ (pl t r) (pl t' r') :=
  inferInstanceAs (Subst σ (_++_) _)

def eq (t r : Expr) : Expr := t ++ "=" ++ r
instance [Subst σ t t'] [Subst σ r r'] : Subst σ (eq t r) (eq t' r') :=
  inferInstanceAs (Subst σ (_++_) _)

def im (P Q : Expr) : Expr := "(" ++ P ++ "->" ++ Q ++ ")"
instance {P Q P' Q'} [Subst σ P P'] [Subst σ Q Q'] : Subst σ (im P Q) (im P' Q') :=
  inferInstanceAs (Subst σ (_++_) _)

def al (x P : Expr) : Expr := "A." ++ x ++ P
instance {x P x' P'} [Subst σ x x'] [Subst σ P P'] : Subst σ (al x P) (al x' P') :=
  inferInstanceAs (Subst σ (_++_) _)

def vt : VR := ⟨"term", 0⟩
def vr : VR := ⟨"term", 1⟩
def vs : VR := ⟨"term", 2⟩
def vP : VR := ⟨"wff", 0⟩
def vQ : VR := ⟨"wff", 1⟩
def vx : VR := ⟨"set", 0⟩

def axs (s : Statement) : Prop := s ∈ [
  ⟨Context.mk' [] [], ("term", ze)⟩,
  ⟨Context.mk' [] [], ("term", pl vt vr)⟩,
  ⟨Context.mk' [] [], ("wff", eq vt vr)⟩,
  ⟨Context.mk' [] [], ("wff", im vP vQ)⟩,
  ⟨Context.mk' [] [], ("wff", al vx vP)⟩,
  ⟨Context.mk' [] [], ("|-", im (eq vt vr) (im (eq vt vs) (eq vr vs)))⟩,
  ⟨Context.mk' [] [], ("|-", eq (pl vt ze) vt)⟩,
  ⟨Context.mk' [] [("|-", vP), ("|-", im vP vQ)], ("|-", vQ)⟩,
  ⟨Context.mk' [(vx, vP)] [], ("|-", im vP (al vx vP))⟩
]

abbrev Provable := Metamath.Provable axs
abbrev Typed := Metamath.Typed axs

instance tze : Typed "term" ze :=
  ⟨fun _Γ => (Provable.ax_self axs (.head _)).thm subst.ok.nil DJ_nil HH_nil⟩

instance tpl {t r} [Typed "term" t] [Typed "term" r] :
    Typed "term" (pl t r) :=
  ⟨fun _Γ =>
    have : Subst (subst_of [(vt, t), (vr, r)]) vt t := ⟨List.append_nil _⟩
    have : Subst (subst_of [(vt, t), (vr, r)]) vr r := ⟨List.append_nil _⟩
    (Provable.ax_self axs (.tail _ <| .head _)).thm
      (subst.ok.cons vt t.ty $ subst.ok.cons vr r.ty subst.ok.nil)
      DJ_nil HH_nil⟩

instance weq {t r} [Typed "term" t] [Typed "term" r] :
    Typed "wff" (eq t r) :=
  ⟨fun _Γ =>
    have : Subst (subst_of [(vt, t), (vr, r)]) vt t := ⟨List.append_nil _⟩
    have : Subst (subst_of [(vt, t), (vr, r)]) vr r := ⟨List.append_nil _⟩
    (Provable.ax_self axs (.tail _ <| .tail _ <| .head _)).thm
      (subst.ok.cons vt t.ty $ subst.ok.cons vr r.ty subst.ok.nil)
      DJ_nil HH_nil⟩

instance wim {P Q} [Typed "wff" P] [Typed "wff" Q] :
    Typed "wff" (im P Q) :=
  ⟨fun _Γ =>
    have : Subst (subst_of [(vP, P), (vQ, Q)]) vP P := ⟨List.append_nil _⟩
    have : Subst (subst_of [(vP, P), (vQ, Q)]) vQ Q := ⟨List.append_nil _⟩
    (Provable.ax_self axs (.tail _ <| .tail _ <| .tail _ <| .head _)).thm
      (subst.ok.cons vP P.ty $ subst.ok.cons vQ Q.ty subst.ok.nil)
      DJ_nil HH_nil⟩

instance wal {x P} [Typed "set" x] [Typed "wff" P] :
    Typed "wff" (al x P) :=
  ⟨fun _Γ =>
    have : Subst (subst_of [(vx, x), (vP, P)]) vx x := ⟨List.append_nil _⟩
    have : Subst (subst_of [(vx, x), (vP, P)]) vP P := ⟨List.append_nil _⟩
    (Provable.ax_self axs (.tail _ <| .tail _ <| .tail _ <| .tail _ <| .head _)).thm
      (subst.ok.cons vx x.ty $ subst.ok.cons vP P.ty subst.ok.nil)
      DJ_nil HH_nil⟩

theorem a1 {Γ t r s} [Typed "term" t] [Typed "term" r] [Typed "term" s] :
    Provable Γ ("|-", im (eq t r) (im (eq t s) (eq r s))) :=
  have : Subst (subst_of [(vt, t), (vr, r), (vs, s)]) vt t := ⟨List.append_nil _⟩
  have : Subst (subst_of [(vt, t), (vr, r), (vs, s)]) vr r := ⟨List.append_nil _⟩
  have : Subst (subst_of [(vt, t), (vr, r), (vs, s)]) vs s := ⟨List.append_nil _⟩
  (Provable.ax_self axs (.tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .head _)).thm
    (subst.ok.cons vt t.ty $ subst.ok.cons vr r.ty $ subst.ok.cons vs s.ty subst.ok.nil)
    DJ_nil HH_nil

theorem a2 {Γ t} [Typed "term" t] :
    Provable Γ ("|-", eq (pl t ze) t) :=
  have : Subst (subst_of [(vt, t)]) vt t := ⟨List.append_nil _⟩
  (Provable.ax_self axs (.tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .head _)).thm
    (subst.ok.cons vt t.ty subst.ok.nil)
    DJ_nil HH_nil

theorem mp {Γ P Q} [Typed "wff" P] [Typed "wff" Q]
    (min : Provable Γ ("|-", P))
    (maj : Provable Γ ("|-", im P Q)) :
    Provable Γ ("|-", Q) :=
  have : Subst (subst_of [(vP, P), (vQ, Q)]) vP P := ⟨List.append_nil _⟩
  have : Subst (subst_of [(vP, P), (vQ, Q)]) vQ Q := ⟨List.append_nil _⟩
  (Provable.ax_self axs (.tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .head _)).thm
    (subst.ok.cons vP P.ty $ subst.ok.cons vQ Q.ty subst.ok.nil)
    DJ_nil (HH_cons min $ HH_cons maj HH_nil)

theorem ax5 {Γ x P} [Typed "set" x] [Typed "wff" P]
    (xp : x.disjoint Γ.dj P) :
    Provable Γ ("|-", im P (al x P)) :=
  have : Subst (subst_of [(vx, x), (vP, P)]) vx x := ⟨List.append_nil _⟩
  have : Subst (subst_of [(vx, x), (vP, P)]) vP P := ⟨List.append_nil _⟩
  (Provable.ax_self axs (.tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .head _)).thm
    (subst.ok.cons vx x.ty $ subst.ok.cons vP P.ty subst.ok.nil)
    (DJ_cons xp DJ_nil) HH_nil

theorem th1 {Γ t} [Typed "term" t] :
  Provable Γ ("|-", eq t t) := mp a2 (mp a2 a1)

end Demo
end Metamath
