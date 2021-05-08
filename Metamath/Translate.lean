-- WIP stuff. see Metamath.Verify for the verifier

import Lean
import Metamath.Verify

open Or in
theorem or_assoc {a b c} : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
⟨fun | inl (inl h) => inl h
     | inl (inr h) => inr (inl h)
     | inr h => inr (inr h),
 fun | inl h => inl (inl h)
     | inr (inl h) => inl (inr h)
     | inr (inr h) => inr h⟩

theorem Or.symm : a ∨ b → b ∨ a
| Or.inl h => Or.inr h
| Or.inr h => Or.inl h

namespace List

def mem (a : α) : List α → Prop
| [] => False
| (b :: l) => a = b ∨ mem a l

infix:50 " ∈ " => mem

theorem mem_append {a} : ∀ {l₁ l₂ : List α}, a ∈ l₁ ++ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂
| [], _ => by simp [mem]
| b :: l₁, l₂ => by simp only [List.cons_append, mem, or_assoc, mem_append]; exact Iff.rfl

end List

namespace Metamath
open Lean Elab
open Verify in
partial def foo : TermElabM Unit := do
  let mut s : ParserState := Inhabited.default
  s := s.withDB fun db => { db with interrupt := true }
  let h ← IO.FS.Handle.mk "/home/mario/Documents/metamath/mm/iset.mm" IO.FS.Mode.read true
  let rec loop (s : ParserState) (base : Nat) : IO (Except ParserState DB) := do
    if ← h.isEof then
      pure $ Except.ok $ s.done base
    else
      let buf ← h.read 1024
      let s := s.feedAll base buf
      if s.db.error?.isSome then pure $ Except.error s
      else loop s (base + buf.size)
  match ← loop Inhabited.default 0 with
  | Except.ok _ => ()
  | Except.error s => match s.db.error? with
    | some ⟨Error.ax pos l f fr, i⟩ =>
      IO.println s!"axiom {l}: {fr} |- {f}"
    | some ⟨Error.thm pos l f fr, i⟩ =>
      IO.println s!"theorem {l}: {fr} |- {f}"
    | some ⟨Error.error pos msg, _⟩ =>
      IO.println s!"at {pos}: {msg}"
    | _ => ()

-- #eval foo

def CN := String
instance : Inhabited CN := inferInstanceAs (Inhabited String)
instance : DecidableEq CN := inferInstanceAs (DecidableEq String)

structure VR := (type : CN) (i : Nat)
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
def Expr.sn (s : Sym) : Expr := [s]
instance : Coe String Expr := ⟨fun c => Expr.sn c⟩
instance : Coe VR Expr := ⟨fun v => Expr.sn (var v)⟩
def Expr.cons (c : String) : Expr → Expr := List.cons c
def Expr.mem (e : Expr) (v : VR) : Prop := var v ∈ e

scoped notation:50 a:51 " ∈' " b:51 => Expr.mem b a

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
  simp only [Expr.subst]; rw [List.cons_append, List.cons_append, ← subst_append]; rfl
| var v :: e, e₂ => by
  rw [List.cons_append]; simp only [Expr.subst]; rw [List.append_assoc, subst_append]

theorem Expr.mem_subst {σ a} : {e : Expr} → a ∈' Expr.subst σ e → ∃ b, b ∈' e ∧ a ∈' σ b
| const c :: (e : Expr), Or.inr h => let ⟨b, h₁, h₂⟩ := mem_subst h; ⟨b, Or.inr h₁, h₂⟩
| var v :: e, h =>
  match List.mem_append.1 h with
  | Or.inl h => ⟨v, Or.inl rfl, h⟩
  | Or.inr h => let ⟨b, h₁, h₂⟩ := mem_subst h; ⟨b, Or.inr h₁, h₂⟩

def subst.trans (σ σ' : VR → Expr) (v : VR) : Expr := (σ v).subst σ'

theorem Expr.subst_tr (σ σ' : VR → Expr) : (e : Expr) →
  e.subst (subst.trans σ σ') = (e.subst σ).subst σ'
| [] => rfl
| const c :: e => congrArg (const c :: .) (subst_tr _ _ e)
| var v :: e => by simp only [subst]; rw [subst_append, subst_tr]; rfl

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

structure DJ :=
  disj : VR → VR → Prop
  irr : ¬ disj x x
  symm : disj x y → disj y x

instance : CoeFun DJ (fun _ => VR → VR → Prop) := ⟨DJ.disj⟩

def DJ.mk' (disj : List (VR × VR)) : DJ :=
{ disj := fun a b => a ≠ b ∧ ((a, b) ∈ disj ∨ (b, a) ∈ disj)
  irr := fun h => h.1 rfl
  symm := fun ⟨h, h'⟩ => ⟨h.symm, h'.symm⟩ }

def Expr.disjoint (dj : DJ) (e₁ e₂ : Expr) : Prop :=
  ∀ c d, c ∈' e₁ → d ∈' e₂ → dj c d

def DJ.subst (σ : VR → Expr) (dj dj' : DJ) :=
  ∀ a b, dj a b → (σ a).disjoint dj' (σ b)

structure Context :=
  hyps : Formula → Prop
  dj : DJ

def Context.mk' (disj : List (VR × VR)) (hyps : List Formula) : Context :=
  ⟨fun h => h ∈ hyps, DJ.mk' disj⟩

structure Statement :=
  ctx : Context
  fmla : Formula

inductive Provable (axioms : Statement → Prop) (Γ : Context) : Formula → Prop
| hyp (h) : Γ.hyps h → Provable axioms Γ h
| var (v:VR) : Provable axioms Γ v
| ax (σ : VR → Expr) {ax} : axioms ax → ax.ctx.dj.subst σ Γ.dj →
  (∀ h, ax.ctx.hyps h ∨ (∃ v:VR, h = v) → Provable axioms Γ (h.subst σ)) →
  Provable axioms Γ (ax.fmla.subst σ)

def Statement.provable (axioms : Statement → Prop) (s : Statement) : Prop :=
  Provable axioms s.ctx s.fmla

theorem Provable.ax_self (axioms : Statement → Prop)
  {ax} (H : axioms ax) : ax.provable axioms := by
  have _ from Provable.ax (Γ := ax.ctx) VR.expr H ?disj ?hyp
  rw [Formula.subst_id] at this; exact this
  case disj =>
    intro a b h a' b' h₁ h₂
    match a', b', h₁, h₂ with | _, _, Or.inl rfl, Or.inl rfl => ?_
    exact h
  case hyp =>
    intro fmla h
    match fmla, h with
    | fmla, Or.inl h => rw [Formula.subst_id]; exact Provable.hyp _ h
    | _, Or.inr ⟨v, rfl⟩ => exact Provable.var v

theorem Provable.trans' {axioms : Statement → Prop} {Γ : Context}
  (σ : VR → Expr) {Γ' fmla} (pr : Provable axioms Γ' fmla)
  (dj : Γ'.dj.subst σ Γ.dj)
  (hh : ∀ h, Γ'.hyps h ∨ (∃ v:VR, h = v) → Provable axioms Γ (h.subst σ)) :
  Provable axioms Γ (fmla.subst σ) := by
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

theorem Provable.trans {axioms : Statement → Prop} {Γ : Context}
  (σ : VR → Expr) (s : Statement) : s.provable axioms →
  s.ctx.dj.subst σ Γ.dj →
  (∀ h, s.ctx.hyps h ∨ (∃ v:VR, h = v) → Provable axioms Γ (h.subst σ)) →
  Provable axioms Γ (s.fmla.subst σ) :=
  Provable.trans' (axioms := axioms) σ

def subst_of : List (VR × Expr) → VR → Expr
| [], v => v
| (a, e)::l, v => if a = v then e else subst_of l v

class Subst (σ : VR → Expr) (e : Expr) (e' : outParam Expr) := (out : e.subst σ = e')

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
| _, _, ⟨_, Or.inl (Or.inl rfl)⟩ => h₁
| _, _, ⟨_, Or.inr (Or.inl rfl)⟩ => fun x y hx hy => dj'.symm (h₁ y x hy hx)
| _, _, ⟨h, Or.inl (Or.inr h')⟩ => h₂ _ _ ⟨h, Or.inl h'⟩
| _, _, ⟨h, Or.inr (Or.inr h')⟩ => h₂ _ _ ⟨h, Or.inr h'⟩

theorem HH_nil {axs Γ σ} : ∀ h:Formula, h ∈ [] → Provable axs Γ (h.subst σ)
| _, h => nomatch h

theorem HH_cons {axs Γ σ c f hyps}
  {e} [Subst σ f e] (h₁ : Provable axs Γ (c, e))
  (h₂ : ∀ h:Formula, h ∈ hyps → Provable axs Γ (h.subst σ)) :
  ∀ h:Formula, h ∈ (c, f)::hyps → Provable axs Γ (h.subst σ)
| _, Or.inl rfl => by rw [← @Subst.out σ f e] at h₁; exact h₁
| _, Or.inr h => h₂ _ h

class Typed (axs : outParam _) (c : outParam CN) (e : Expr) :=
  type (Γ) : Provable axs Γ (c, e)

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

def axioms (s : Statement) : Prop := s ∈ [
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

abbrev Provable := Metamath.Provable axioms
abbrev Typed := Metamath.Typed axioms

instance tze : Typed "term" ze :=
⟨fun Γ =>
  (Provable.ax_self axioms (Or.inl rfl)).thm subst.ok.nil DJ_nil HH_nil⟩

instance tpl {t r} [Typed "term" t] [Typed "term" r] :
  Typed "term" (pl t r) :=
⟨fun Γ =>
  have Subst (subst_of [(vt, t), (vr, r)]) vt t from ⟨List.append_nil _⟩
  have Subst (subst_of [(vt, t), (vr, r)]) vr r from ⟨List.append_nil _⟩
  (Provable.ax_self axioms (Or.inr $ Or.inl rfl)).thm
    (subst.ok.cons vt t.ty $ subst.ok.cons vr r.ty subst.ok.nil)
    DJ_nil HH_nil⟩

instance weq {t r} [Typed "term" t] [Typed "term" r] :
  Typed "wff" (eq t r) :=
⟨fun Γ =>
  have Subst (subst_of [(vt, t), (vr, r)]) vt t from ⟨List.append_nil _⟩
  have Subst (subst_of [(vt, t), (vr, r)]) vr r from ⟨List.append_nil _⟩
  (Provable.ax_self axioms (Or.inr $ Or.inr $ Or.inl rfl)).thm
    (subst.ok.cons vt t.ty $ subst.ok.cons vr r.ty subst.ok.nil)
    DJ_nil HH_nil⟩

instance wim {P Q} [Typed "wff" P] [Typed "wff" Q] :
  Typed "wff" (im P Q) :=
⟨fun Γ =>
  have Subst (subst_of [(vP, P), (vQ, Q)]) vP P from ⟨List.append_nil _⟩
  have Subst (subst_of [(vP, P), (vQ, Q)]) vQ Q from ⟨List.append_nil _⟩
  (Provable.ax_self axioms (Or.inr $ Or.inr $ Or.inr $ Or.inl rfl)).thm
    (subst.ok.cons vP P.ty $ subst.ok.cons vQ Q.ty subst.ok.nil)
    DJ_nil HH_nil⟩

instance wal {x P} [Typed "set" x] [Typed "wff" P] :
  Typed "wff" (al x P) :=
⟨fun Γ =>
  have Subst (subst_of [(vx, x), (vP, P)]) vx x from ⟨List.append_nil _⟩
  have Subst (subst_of [(vx, x), (vP, P)]) vP P from ⟨List.append_nil _⟩
  (Provable.ax_self axioms (Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl rfl)).thm
    (subst.ok.cons vx x.ty $ subst.ok.cons vP P.ty subst.ok.nil)
    DJ_nil HH_nil⟩

theorem a1 {Γ t r s} [Typed "term" t] [Typed "term" r] [Typed "term" s] :
  Provable Γ ("|-", im (eq t r) (im (eq t s) (eq r s))) :=
  have Subst (subst_of [(vt, t), (vr, r), (vs, s)]) vt t from ⟨List.append_nil _⟩
  have Subst (subst_of [(vt, t), (vr, r), (vs, s)]) vr r from ⟨List.append_nil _⟩
  have Subst (subst_of [(vt, t), (vr, r), (vs, s)]) vs s from ⟨List.append_nil _⟩
  (Provable.ax_self axioms (Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl rfl)).thm
    (subst.ok.cons vt t.ty $ subst.ok.cons vr r.ty $ subst.ok.cons vs s.ty subst.ok.nil)
    DJ_nil HH_nil

theorem a2 {Γ t} [Typed "term" t] :
  Provable Γ ("|-", eq (pl t ze) t) :=
  have Subst (subst_of [(vt, t)]) vt t from ⟨List.append_nil _⟩
  (Provable.ax_self axioms (Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl rfl)).thm
    (subst.ok.cons vt t.ty subst.ok.nil)
    DJ_nil HH_nil

theorem mp {Γ P Q} [Typed "wff" P] [Typed "wff" Q]
  (min : Provable Γ ("|-", P))
  (maj : Provable Γ ("|-", im P Q)) :
  Provable Γ ("|-", Q) :=
  have Subst (subst_of [(vP, P), (vQ, Q)]) vP P from ⟨List.append_nil _⟩
  have Subst (subst_of [(vP, P), (vQ, Q)]) vQ Q from ⟨List.append_nil _⟩
  (Provable.ax_self axioms (Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl rfl)).thm
    (subst.ok.cons vP P.ty $ subst.ok.cons vQ Q.ty subst.ok.nil)
    DJ_nil (HH_cons min $ HH_cons maj HH_nil)

theorem ax5 {Γ x P} [Typed "set" x] [Typed "wff" P]
  (xp : x.disjoint Γ.dj P) :
  Provable Γ ("|-", im P (al x P)) :=
  have Subst (subst_of [(vx, x), (vP, P)]) vx x from ⟨List.append_nil _⟩
  have Subst (subst_of [(vx, x), (vP, P)]) vP P from ⟨List.append_nil _⟩
  (Provable.ax_self axioms (Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inr $ Or.inl rfl)).thm
    (subst.ok.cons vx x.ty $ subst.ok.cons vP P.ty subst.ok.nil)
    (DJ_cons xp DJ_nil) HH_nil

theorem th1 {Γ t} [Typed "term" t] :
  Provable Γ ("|-", eq t t) := mp a2 (mp a2 a1)

end Demo
end Metamath
