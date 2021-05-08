-- WIP stuff. see Metamath.Verify for the verifier

import Lean
import Metamath.Verify

namespace Metamath
open Lean Elab
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

namespace Translate

def VR := Nat
instance : BEq VR := inferInstanceAs (BEq Nat)

inductive Sym
| const (c : String)
| var (c : String) (n : VR)
deriving Inhabited, BEq
open Sym

instance : Coe String Sym := ⟨const⟩
def Sym.isVar : Sym → Bool
| const _ => false
| var _ _ => true

abbrev Formula := List Sym

def Formula.δ (a b : Formula) : Bool :=
a.all fun
| const _ => true
| var _ a => b.all fun
  | const _ => true
  | var _ b => a != b

def ze : Formula := ["0"]
def pl (t r : Formula) := ↑"(" :: t ++ ↑"+" :: r ++ [↑")"]
def eq (t r : Formula) := t ++ ↑"=" :: r
def im (P Q : Formula) := ↑"(" :: P ++ ↑"->" :: Q ++ [↑")"]
def al (x P : Formula) := ↑"A." :: x ++ P

class Proof where
  ρ : Sym → Formula → Prop
open Proof

-- This is a by hand translation of demo0.mm, ideally the tactic will write this

def Set [Proof] := {t // ρ "set" t}
def Term [Proof] := {t // ρ "term" t}
def Wff [Proof] := {t // ρ "wff" t}

def Prf [Proof] (P : Wff) : Prop := ρ "|-" P.1
prefix "⊢" => Prf

class Database extends Proof where
  tze : ρ "term" ze
  tpl : ∀ {t r}, ρ "term" t → ρ "term" r → ρ "term" (pl t r)
  weq : ∀ {t r}, ρ "term" t → ρ "term" r → ρ "wff" (eq t r)
  wim : ∀ {P Q}, ρ "wff" P → ρ "wff" Q → ρ "wff" (im P Q)
  wal : ∀ {x P}, ρ "set" x → ρ "wff" P → ρ "wff" (al x P)
  a1 : ∀ {t r s}, ρ "term" t → ρ "term" r → ρ "term" s → ρ "|-" (im (eq t r) (im (eq t s) (eq r s)))
  a2 : ∀ {t}, ρ "term" t → ρ "|-" (eq (pl t ze) t)
  mp : ∀ {P Q}, ρ "wff" P → ρ "wff" Q → ρ "|-" P → ρ "|-" (im P Q) → ρ "|-" Q
  ax5 : ∀ {x P}, ρ "set" x → ρ "wff" P → x.δ P → ρ "|-" (im P (al x P))

namespace Database
variable [Database]

def Ze : Term := ⟨ze, tze⟩
def Pl (t r : Term) : Term := ⟨_, tpl t.2 r.2⟩
def Eq (t r : Term) : Wff := ⟨_, weq t.2 r.2⟩
def Im (P Q : Wff) : Wff := ⟨_, wim P.2 Q.2⟩
def Al (x : Set) (P : Wff) : Wff := ⟨_, wal x.2 P.2⟩
def A1 {t r s} : ⊢ Im (Eq t r) (Im (Eq t s) (Eq r s)) := a1 t.2 r.2 s.2
def A2 {t} : ⊢ Eq (Pl t Ze) t := a2 t.2
def Mp {P Q} (h1 : ⊢ P) (h2 : ⊢ Im P Q) : ⊢ Q := mp P.2 Q.2 h1 h2

theorem th1 {t} : ⊢ Eq t t := Mp A2 (Mp A2 A1)

end Database