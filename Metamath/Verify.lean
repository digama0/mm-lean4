import Std.Data.HashMap
import Std.Data.HashSet

section forMathlib

namespace Nat

protected theorem sub_sub : ∀ (n m k : Nat), n - m - k = n - (m + k)
| n, m, 0        => by rw [Nat.add_zero, Nat.sub_zero]
| n, m, (succ k) => by rw [add_succ, sub_succ, sub_succ, Nat.sub_sub n m k]

protected theorem add_sub_add_right : ∀ (n k m : Nat), (n + k) - (m + k) = n - m
| n, 0,      m => by rw [Nat.add_zero, Nat.add_zero]
| n, succ k, m => by rw [add_succ, add_succ, succ_sub_succ, Nat.add_sub_add_right n k m]

protected theorem sub_add_cancel : {a b : Nat} → a ≤ b → b - a + a = b
| 0, b, _ => rfl
| a+1, b+1, h => congrArg Nat.succ $ show (b + 1) - (a + 1) + a = b by
  rw [Nat.add_comm  a, ← Nat.sub_sub]
  exact Nat.sub_add_cancel h

protected theorem lt_of_not_le {a b : Nat} (h : ¬ a ≤ b) : b < a :=
  match Nat.ltOrGe b a with | Or.inl h' => h' | Or.inr h' => nomatch h h'

protected theorem lt_add_of_pos_right {n k : Nat} (h : 0 < k) : n < n + k :=
Nat.addLtAddLeft h n

protected theorem lt_of_add_lt_add_right {a b c : Nat} (h : a + b < c + b) : a < c :=
  Nat.lt_of_not_le fun h' => Nat.notLeOfGt h (Nat.addLeAddRight h' _)

protected theorem sub_pos_of_lt {m n : Nat} (h : m < n) : 0 < n - m := by
  apply Nat.lt_of_add_lt_add_right (b := m)
  rw [Nat.zero_add, Nat.sub_add_cancel (Nat.leOfLt h)]; exact h

protected theorem sub_lt_sub_left : ∀ {k m n : Nat} (H : k < m) (h : k < n), m - n < m - k
| 0, m+1, n+1, _, _ => by rw [Nat.add_sub_add_right]; exact lt_succ_of_le (Nat.subLe _ _)
| k+1, m+1, n+1, h1, h2 => by
  rw [Nat.add_sub_add_right, Nat.add_sub_add_right]
  exact Nat.sub_lt_sub_left h1 h2

end Nat

def UpNat (ub a i : Nat) := i < a ∧ i < ub

theorem UpNat.next {ub i} (h : i < ub) : UpNat ub (i+1) i := ⟨Nat.ltSuccSelf _, h⟩

theorem upNatWF (ub) : WellFounded (UpNat ub) :=
  Subrelation.wf (h₂ := measureWf (ub - .)) @fun a i ⟨ia, iu⟩ => Nat.sub_lt_sub_left iu ia

end forMathlib

theorem Fin.val_eq_of_lt : a < n.succ → (@Fin.ofNat n a).val = a := Nat.mod_eq_of_lt
theorem UInt32.val_eq_of_lt : a < UInt32.size → (UInt32.ofNat a).val = a := Fin.val_eq_of_lt

theorem toChar_aux (n : Nat) (h : n < UInt8.size) : Nat.isValidChar (UInt32.ofNat n).1 := by
  rw [UInt32.val_eq_of_lt]
  exact Or.inl (Nat.ltTrans h (by decide))
  exact Nat.ltTrans h (by decide)

def UInt8.toChar (n : UInt8) : Char := ⟨n.toUInt32, toChar_aux n.1 n.1.2⟩
def Char.toUInt8 (n : Char) : UInt8 := n.1.toUInt8

theorem Char.utf8Size_pos (c : Char) : 0 < c.utf8Size :=
  let foo {c} {t e : UInt32} : [Decidable c] → 0 < t → 0 < e → 0 < ite c t e
  | Decidable.isTrue _, h, _ => h
  | Decidable.isFalse _, _, h => h
  foo (by decide) $ foo (by decide) $ foo (by decide) (by decide)

theorem String.csize_pos : (c : Char) → 0 < String.csize c := Char.utf8Size_pos

namespace UInt8

def isUpper (c : UInt8) : Bool :=
  c ≥ 65 && c ≤ 90

def isLower (c : UInt8) : Bool :=
  c ≥ 97 && c ≤ 122

def isAlpha (c : UInt8) : Bool :=
  c.isUpper || c.isLower

def isDigit (c : UInt8) : Bool :=
  c ≥ 48 && c ≤ 57

def isAlphanum (c : UInt8) : Bool :=
  c.isAlpha || c.isDigit

end UInt8

structure ByteSliceT where
  arr : ByteArray
  off : Nat

namespace ByteSliceT

@[inline] def size (self : ByteSliceT) : Nat := self.arr.size - self.off

@[inline] def getOp (self : ByteSliceT) (idx : Nat) : UInt8 := self.arr.get! (self.off + idx)

end ByteSliceT

def ByteArray.toSliceT (arr : ByteArray) : ByteSliceT := ⟨arr, 0⟩

structure ByteSlice where
  arr : ByteArray
  off : Nat
  len : Nat

namespace ByteSlice

def toArray : ByteSlice → ByteArray
| ⟨arr, off, len⟩ => arr.extract off len

@[inline] def getOp (self : ByteSlice) (idx : Nat) : UInt8 := self.arr.get! (self.off + idx)

partial def forIn.loop.impl [Monad m] (f : UInt8 → β → m (ForInStep β))
  (arr : ByteArray) (off _end : Nat) (i : Nat) (b : β) : m β :=
  if i < _end then do
    match ← f (arr.get! i) b with
    | ForInStep.done b => pure b
    | ForInStep.yield b => impl f arr off _end (i+1) b
  else b

set_option codegen false in
@[implementedBy forIn.loop.impl]
def forIn.loop [Monad m] (f : UInt8 → β → m (ForInStep β))
  (arr : ByteArray) (off _end : Nat) (i : Nat) (b : β) : m β := do
(upNatWF _end).fix (x := i) (C := fun _ => ∀ b, m β) (b := b)
  fun i IH b =>
    if h : i < _end then do
      let b ← f (arr.get! i) b
      match b with
      | ForInStep.done b => pure b
      | ForInStep.yield b => IH (i+1) (UpNat.next h) b
    else b

instance : ForIn m ByteSlice UInt8 :=
  ⟨fun ⟨arr, off, len⟩ b f => forIn.loop f arr off (off + len) off b⟩

end ByteSlice

def ByteSliceT.toSlice : ByteSliceT → ByteSlice
| ⟨arr, off⟩ => ⟨arr, off, arr.size - off⟩

def ByteArray.toSlice (arr : ByteArray) : ByteSlice := ⟨arr, 0, arr.size⟩

partial def ByteSlice.eqArray.loop.impl (arr₁ arr₂ : ByteArray) (i j : Nat) : Bool :=
  if j < arr₂.size then
    arr₁.get! i == arr₂.get! j && impl arr₁ arr₂ (i+1) (j+1)
  else true

set_option codegen false in
@[implementedBy ByteSlice.eqArray.loop.impl]
def ByteSlice.eqArray.loop (arr₁ arr₂ : ByteArray) (i j : Nat) : Bool :=
(upNatWF arr₂.size).fix (x := j) (C := fun _ => ∀ i, Bool) (i := i)
  fun j IH i =>
    if h : j < arr₂.size then
      arr₁.get! i == arr₂.get! j && IH (j+1) (UpNat.next h) (i+1)
    else true

partial def ByteSlice.eqArray (bs : ByteSlice) (arr : ByteArray) : Bool :=
  bs.len == arr.size && ByteSlice.eqArray.loop bs.arr arr bs.off 0

partial def String.toAscii.loop.impl (s : String) (out : ByteArray) (p : Pos) : ByteArray :=
  if s.atEnd p then out else
  let c := s.get p
  impl s (out.push c.toUInt8) (s.next p)

set_option codegen false in
@[implementedBy String.toAscii.loop.impl]
def String.toAscii.loop (s : String) (out : ByteArray) (p : Pos) : ByteArray :=
(upNatWF (utf8ByteSize s)).fix (x := p) (C := fun _ => ∀ out, ByteArray) (out := out)
  fun p IH i =>
    if h : s.atEnd p then out else
    let c := s.get p
    IH (s.next p) (out := out.push c.toUInt8)
      ⟨Nat.lt_add_of_pos_right (String.csize_pos _),
      Nat.lt_of_not_le (mt decideEqTrue h)⟩

def String.toAscii (s : String) : ByteArray :=
  String.toAscii.loop s ByteArray.empty 0

def ByteSlice.toString (bs : ByteSlice) : String := do
  let mut s := ""
  for c in bs do s := s.push c.toChar
  s

instance : ToString ByteSlice where
  toString bs := do
    let mut s := ""
    for c in bs do s := s.push c.toChar
    s

namespace Metamath
namespace Verify

open IO.FS (Handle)
open Std (HashMap HashSet)

def isLabelChar (c : UInt8) : Bool :=
c.isAlphanum || c == '-'.toUInt8 || c == '_'.toUInt8 || c == '.'.toUInt8

def isWhitespace (c : UInt8) : Bool :=
c == ' '.toUInt8 || c == '\n'.toUInt8 || c == '\r'.toUInt8 || c == '\t'.toUInt8

def isPrintable (c : UInt8) : Bool := c >= 32 && c <= 126

def isMathChar (c : UInt8) : Bool := c ≠ '$'.toUInt8 && isPrintable c

def toLabel (bs : ByteSlice) : Bool × String := do
  let mut ok := true
  let mut s := ""
  for c in bs do
    s := s.push c.toChar
    unless isLabelChar c do ok := false
  (ok, s)

def toMath (bs : ByteSlice) : Bool × String := do
  let mut ok := true
  let mut s := ""
  for c in bs do
    s := s.push c.toChar
    unless isPrintable c do ok := false
  (ok, s)

structure Pos := (line col : Nat)

instance : ToString Pos := ⟨fun ⟨l, c⟩ => s!"{l}:{c}"⟩

def DJ := String × String
instance : BEq DJ := instBEqProd

structure Frame where
  dj : Array DJ
  hyps : Array String
deriving Inhabited

def Frame.size : Frame → Nat × Nat
| ⟨dj, hyps⟩ => (dj.size, hyps.size)

def Frame.shrink : Frame → Nat × Nat → Frame
| ⟨dj, hyps⟩, (x, y) => ⟨dj.shrink x, hyps.shrink y⟩

instance : ToString Frame := ⟨fun fr => toString fr.hyps⟩

inductive Sym
| const (c : String)
| var (v : String)
deriving Inhabited

def Sym.isVar : Sym → Bool
| const _ => false
| var _ => true

def Sym.value : Sym → String
| const c => c
| var v => v

instance : BEq Sym := ⟨fun a b => a.value == b.value⟩

abbrev Formula := Array Sym

instance : ToString Formula where
  toString f := do
    let s := f[0].value
    f.foldl (init := f[0].value) (start := 1) fun (s:String) v =>
      s ++ " " ++ v.value

def Formula.subst (σ : HashMap String Formula) (f : Formula) : Except String Formula := do
  let mut f' := #[]
  for c in f do
    match c with
    | Sym.const _ => f' := f'.push c
    | Sym.var v =>
      match σ.find? v with
      | none => throw s!"variable {v} not found"
      | some e => f' := e.foldl Array.push f' 1
  f'

def Formula.foldlVars (self : Formula) (init : α) (f : α → String → α) : α :=
self.foldl (init := init) (start := 1) fun a v =>
  match v with
  | Sym.var v => f a v
  | _ => a

inductive Object
| const : String → Object
| var : String → Object
| hyp : Bool → Formula → String → Object
| assert : Formula → Frame → String → Object

inductive ProofTokenParser
| start
| preload
| normal
| compressed (chr : Nat)

inductive HeapEl
| fmla (f : Formula)
| assert (f : Formula) (fr : Frame)

instance : ToString HeapEl where
  toString
  | HeapEl.fmla f => toString f
  | HeapEl.assert f fr => s!"{fr} |- {f}"

structure ProofState where
  pos : Pos
  label : String
  fmla : Formula
  frame : Frame
  heap : Array HeapEl
  stack : Array Formula
  ptp : ProofTokenParser

instance : ToString ProofState where
  toString p := do
    let mut s := s!"at {p.pos}: {p.label}\n"
    let mut i := 0
    for el in p.heap do
      s := s ++ s!"heap {i} := {el}\n"
      i := i + 1
    s := s ++ "\n"
    for el in p.stack do
      s := s ++ s!"{el}\n"
    s

namespace ProofState

def push (pr : ProofState) (f : Formula) : ProofState :=
  { pr with stack := pr.stack.push f }

def pushHeap (pr : ProofState) (el : HeapEl) : ProofState :=
  { pr with heap := pr.heap.push el }

def save (pr : ProofState) : Except String ProofState :=
  if pr.stack.isEmpty then
    throw "can't save empty stack"
  else
    let f := pr.stack.back
    pr.pushHeap (HeapEl.fmla f)

end ProofState

inductive Error
| error (pos : Pos) (msg : String)
| ax (pos : Pos) (l : String) (f : Formula) (fr : Frame)
| thm (pos : Pos) (l : String) (f : Formula) (fr : Frame)

structure Interrupt :=
  e : Error
  idx : Nat

structure DB where
  frame : Frame
  scopes : Array (Nat × Nat)
  objects : HashMap String Object
  interrupt : Bool
  error? : Option Interrupt
deriving Inhabited

namespace DB

@[inline] def error (s : DB) : Bool := s.error?.isSome

def mkError (s : DB) (pos : Pos) (msg : String) : DB :=
  { s with error? := some ⟨Error.error pos msg, arbitrary⟩ }

def pushScope (s : DB) : DB :=
  { s with scopes := s.scopes.push s.frame.size }

def popScope (pos : Pos) (db : DB) : DB :=
  if db.scopes.isEmpty then
    db.mkError pos "can't pop global scope"
  else
    { db with frame := db.frame.shrink db.scopes.back, scopes := db.scopes.pop }

def find? (db : DB) (l : String) : Option Object := db.objects.find? l

def isConst (db : DB) (tk : String) : Bool :=
  if let some (Object.const _) := db.find? tk then true else false

def isVar (db : DB) (tk : String) : Bool :=
  if let some (Object.var _) := db.find? tk then true else false

def isSym (db : DB) (tk : String) : Bool :=
  match db.find? tk with
  | some (Object.const _) => true
  | some (Object.var _) => true
  | _ => false

@[inline] def withFrame (f : Frame → Frame) (db : DB) : DB :=
  { db with frame := f db.frame }

@[inline] def withDJ (f : Array DJ → Array DJ) (db : DB) : DB :=
  db.withFrame fun ⟨dj, hyps⟩ => ⟨f dj, hyps⟩

@[inline] def withHyps (f : Array String → Array String) (db : DB) : DB :=
  db.withFrame fun ⟨dj, hyps⟩ => ⟨dj, f hyps⟩

def insert (db : DB) (pos : Pos) (l : String) (obj : String → Object) : DB :=
  if let some o := db.find? l then
    let ok : Bool := match o with
    | Object.var v => if let Object.var _ := obj l then true else false
    | _ => false
    if ok then db else db.mkError pos s!"duplicate symbol/assert {l}"
  else
    { db with objects := db.objects.insert l (obj l) }

def insertHyp (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula) : DB :=
  let db := db.insert pos l (Object.hyp ess f)
  db.withHyps fun hyps => hyps.push l

def trimFrame (db : DB) (fmla : Formula) (fr := db.frame) : Bool × Frame := do
  let collectVars (fmla : Formula) vars :=
    fmla.foldlVars vars HashSet.insert
  let mut vars : HashSet String := collectVars fmla HashSet.empty
  for l in fr.hyps do
    if let some (Object.hyp true f _) := db.find? l then
      vars := collectVars f vars
  let mut dj := #[]
  for v in fr.dj do
    if vars.contains v.1 && vars.contains v.2 then
      dj := dj.push v
  let mut hyps := #[]
  let mut inHyps := false
  let mut ok := true
  for l in fr.hyps do
    let ess ←
      if let some (Object.hyp false f _) := db.find? l then
        if inHyps then ok := false
        vars.contains f[1].value
      else
        inHyps := true
        true
    if ess then hyps := hyps.push l
  (ok, ⟨dj, hyps⟩)

def trimFrame' (db : DB) (fmla : Formula) : Except String Frame :=
  let (ok, fr) := db.trimFrame fmla
  if ok then pure fr
  else throw s!"out of order hypotheses in frame"

def insertAxiom (db : DB) (pos : Pos) (l : String) (fmla : Formula) : DB :=
  match db.trimFrame' fmla with
  | Except.ok fr =>
    if db.interrupt then { db with error? := some ⟨Error.ax pos l fmla fr, arbitrary⟩ }
    else db.insert pos l (Object.assert fmla fr)
  | Except.error msg => db.mkError pos msg

def mkProofState (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) : ProofState := do
  let mut heap := #[]
  for l in fr.hyps do
    if let some (Object.hyp _ f _) := db.find? l then
      heap := heap.push (HeapEl.fmla f)
  ⟨pos, l, fmla, fr, heap, #[], ProofTokenParser.start⟩

def preload (db : DB) (pr : ProofState) (l : String) : Except String ProofState :=
  match db.find? l with
  | some (Object.hyp true _ _) => throw "$e found in paren list"
  | some (Object.hyp _ f _) => pr.pushHeap (HeapEl.fmla f)
  | some (Object.assert f fr _) => pr.pushHeap (HeapEl.assert f fr)
  | _ => throw s!"statement {l} not found"

@[inline] def checkHypF (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off // off + hyps.size = stack.size})
  (IH : HashMap String Formula → Except String (HashMap String Formula))
  (i : Nat) (h : i < hyps.size)
  (subst : HashMap String Formula) : Except String (HashMap String Formula) := do
  let val := stack.get ⟨off.1 + i,
    let thm {a b n} : i < a → n + a = b → n + i < b
    | h, rfl => Nat.addLtAddLeft h _
    thm h off.2⟩
  if let some (Object.hyp ess f _) := db.find? (hyps.get ⟨i, h⟩) then
    if f[0] == val[0] then
      if ess then
        if (← f.subst subst) == val then
          IH subst
        else throw "type error in substitution"
      else
        IH (subst.insert f[1].value val)
    else throw s!"bad typecode in substitution {hyps[i]}: {f} / {val}"
  else unreachable!

partial def checkHyp.impl (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off // off + hyps.size = stack.size}) (i : Nat) (subst : HashMap String Formula) :
  Except String (HashMap String Formula) := do
  if h : i < hyps.size then
    checkHypF db hyps stack off (impl db hyps stack off (i+1)) i h subst
  else subst

set_option codegen false in
@[implementedBy checkHyp.impl]
def checkHyp (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off // off + hyps.size = stack.size}) (i : Nat) (subst : HashMap String Formula) :
  Except String (HashMap String Formula) :=
(upNatWF hyps.size).fix (x := i) (C := fun _ => ∀ σ, Except String (HashMap String Formula)) (σ := subst)
  fun i IH subst =>
    if h : i < hyps.size then
      checkHypF db hyps stack off (IH (i+1) (UpNat.next h)) i h subst
    else subst

def stepAssert (db : DB) (pr : ProofState) (f : Formula) : Frame → Except String ProofState
| ⟨dj, hyps⟩ => do
  if h : hyps.size ≤ pr.stack.size then
    let off : {off // off + hyps.size = pr.stack.size} :=
      ⟨pr.stack.size - hyps.size, Nat.sub_add_cancel h⟩
    let subst ← checkHyp db hyps pr.stack off 0 HashMap.empty
    let disj s1 s2 := s1 != s2 &&
      db.frame.dj.contains (if s1 < s2 then (s1, s2) else (s2, s1))
    for (v1, v2) in dj do
      let e1 := subst.find! v1
      let e2 := subst.find! v2
      let disjoint :=
        e1.foldlVars (init := true) fun b s1 =>
          e2.foldlVars b fun b s2 => b && disj s1 s2
      if !disjoint then throw "disjoint variable violation"
    let concl ← f.subst subst
    pure { pr with stack := (pr.stack.shrink off).push concl }
  else throw "stack underflow"

def stepNormal (db : DB) (pr : ProofState) (l : String) : Except String ProofState :=
  match db.find? l with
  | some (Object.hyp _ f _) => pr.push f
  | some (Object.assert f fr _) => db.stepAssert pr f fr
  | _ => throw s!"statement {l} not found"

def stepProof (db : DB) (pr : ProofState) (i : Nat) : Except String ProofState :=
  match pr.heap.get? i with
  | none => throw "proof backref index out of range"
  | some (HeapEl.fmla f) => pr.push f
  | some (HeapEl.assert f fr) => db.stepAssert pr f fr

end DB

inductive CharParser
| ws : CharParser
| token : Nat → ByteSliceT → CharParser
deriving Inhabited

inductive TokensKind
| float
| ess
| ax
| thm

open TokensKind in
instance : ToString TokensKind where
  toString
  | float => "float"
  | ess => "ess"
  | ax => "ax"
  | thm => "thm"

def TokensKind.delim
| thm => "$=".toAscii
| _ => "$.".toAscii

structure TokensParser where
  k : TokensKind
  pos : Pos
  label : String

instance : ToString TokensParser where
  toString | ⟨k, pos, label⟩ => s!"at {pos}: {k} {label}"

inductive TokenParser
| start : TokenParser
| comment : TokenParser → TokenParser
| const : TokenParser
| var : TokenParser
| djvars : Array String → TokenParser
| math : Array Sym → TokensParser → TokenParser
| label : Pos → String → TokenParser
| proof : ProofState → TokenParser
deriving Inhabited

def TokenParser.toString : TokenParser → String
| start => "start"
| comment p => "comment " ++ toString p
| const => "const"
| var => "var"
| djvars s => s!"djvars {s}"
| math s p => s!"math {s} {p}"
| label pos l => s!"at {pos}: ? {l}"
| proof p => ToString.toString p

instance : ToString TokenParser := ⟨TokenParser.toString⟩

structure ParserState where
  db : DB
  tokp : TokenParser
  charp : CharParser
  line : Nat
  linepos : Nat
deriving Inhabited

namespace ParserState

@[inline] def withDB (f : DB → DB) (s : ParserState) : ParserState :=
  { s with db := f s.db }

def mkPos (s : ParserState) (pos : Nat) : Pos := ⟨s.line, pos - s.linepos⟩

def mkError (s : ParserState) (pos : Pos) (msg : String) : ParserState :=
  s.withDB fun db => db.mkError pos msg

def mkErrorAt (s : ParserState) (pos : Pos) (l msg : String) : ParserState :=
  s.mkError pos s!"at {l}: {msg}"

def withAt (l : String) (f : Unit → ParserState) : ParserState :=
  let s := f ()
  if let some ⟨Error.error pos msg, i⟩ := s.db.error? then
    s.withDB fun db => { db with error? := some ⟨Error.error pos s!"at {l}: {msg}", i⟩ }
  else s

def label (s : ParserState) (pos : Pos) (tk : ByteSlice) : ParserState :=
  let (ok, tk) := toLabel tk
  if ok then { s with tokp := TokenParser.label pos tk }
  else s.mkError pos s!"invalid label '{tk}'"

def withMath (s : ParserState) (pos : Pos) (tk : ByteSlice)
  (f : ParserState → String → ParserState) : ParserState :=
  let (ok, tk) := toMath tk
  if !ok then s.mkError pos s!"invalid math string '{tk}'" else
  f s tk

def sym (s : ParserState) (pos : Pos) (tk : ByteSlice) (f : String → Object) : ParserState :=
  if tk.eqArray "$.".toAscii then
    { s with tokp := TokenParser.start }
  else s.withMath pos tk fun s tk =>
    s.withDB fun db => db.insert pos tk f

def resumeAxiom (s : ParserState)
  (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) : ParserState :=
  s.withDB fun db => db.insert pos l (Object.assert fmla fr)

def resumeThm (s : ParserState)
  (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) : ParserState :=
  let pr := s.db.mkProofState pos l fmla fr
  { s with tokp := TokenParser.proof pr }

def feedTokens (s : ParserState) (arr : Array Sym) : TokensParser → ParserState
| ⟨k, pos, l⟩ => withAt l fun _ => do
  unless arr.size > 0 && !arr[0].isVar do
    return s.mkError pos "first symbol is not a constant"
  match k with
  | TokensKind.float =>
    unless arr.size == 2 && arr[1].isVar do
      return s.mkError pos "expected a constant and a variable"
    let s := s.withDB fun db => db.insertHyp pos l false arr
    pure { s with tokp := TokenParser.start }
  | TokensKind.ess =>
    let s := s.withDB fun db => db.insertHyp pos l true arr
    pure { s with tokp := TokenParser.start }
  | TokensKind.ax =>
    let s := s.withDB fun db => db.insertAxiom pos l arr
    pure { s with tokp := TokenParser.start }
  | TokensKind.thm =>
    match s.db.trimFrame' arr with
    | Except.ok fr =>
      if s.db.interrupt then
        s.withDB fun db => { db with error? := some ⟨Error.thm pos l arr fr, arbitrary⟩ }
      else s.resumeThm pos l arr fr
    | Except.error msg => s.mkError pos msg

def feedProof (s : ParserState) (tk : ByteSlice) (pr : ProofState) : ParserState :=
  withAt pr.label fun _ =>
    match go pr with
    | Except.ok pr => { s with tokp := TokenParser.proof pr }
    | Except.error msg => s.mkError pr.pos msg
where
  goNormal (pr : ProofState) :=
    let (ok, tk) := toLabel tk
    if ok then s.db.stepNormal pr tk
    else throw s!"invalid label '{tk}'"
  go (pr : ProofState) : Except String ProofState := do
    match pr.ptp with
    | ProofTokenParser.start =>
      if tk.eqArray "(".toAscii then
        pure { pr with ptp := ProofTokenParser.preload }
      else goNormal { pr with ptp := ProofTokenParser.normal }
    | ProofTokenParser.preload =>
      if tk.eqArray ")".toAscii then
        pure { pr with ptp := ProofTokenParser.compressed 0 }
      else
        let (ok, tk) := toLabel tk
        if ok then s.db.preload pr tk
        else throw s!"invalid label '{tk}'"
    | ProofTokenParser.normal => goNormal pr
    | ProofTokenParser.compressed chr =>
      let mut pr := pr
      let mut chr := chr
      for c in tk do
        if 'A'.toUInt8 ≤ c && c ≤ 'Z'.toUInt8 then
          if c ≤ 'T'.toUInt8 then
            let n := 20 * chr + (c - 'A'.toUInt8).1
            pr ← s.db.stepProof pr n
            chr := 0
          else if c < 'Z'.toUInt8 then
            chr := 5 * chr + (c - 'T'.toUInt8).1
          else
            pr ← pr.save
            chr := 0
        else if c = '?'.toUInt8 then
          throw "proof contains '?'"
        else
          throw "proof parse error"
      pure { pr with ptp := ProofTokenParser.compressed chr }

def finishProof (s : ParserState) : ProofState → ParserState
| ⟨pos, l, fmla, fr, _, stack, ptp⟩ => withAt l fun _ => do
  let s := { s with tokp := TokenParser.start }
  match ptp with
  | ProofTokenParser.compressed 0 => ()
  | ProofTokenParser.normal => ()
  | _ => return s.mkError pos "proof parse error"
  unless stack.size == 1 do
    return s.mkError pos "more than one element on stack"
  unless stack[0] == fmla do
    return s.mkError pos "theorem does not prove what it claims"
  s.withDB fun db => db.insert pos l (Object.assert fmla fr)

def feedToken (s : ParserState) (pos : Nat) (tk : ByteSlice) : ParserState :=
  let pos := s.mkPos pos
  match s.tokp with
  | TokenParser.comment p =>
    if tk.eqArray "$)".toAscii then { s with tokp := p } else s
  | p =>
    if tk.eqArray "$(".toAscii then { s with tokp := p.comment } else
    match p with
    | TokenParser.comment p => unreachable!
    | TokenParser.start =>
      if tk.len == 2 && tk[0] == '$'.toUInt8 then
        match tk[1].toChar with
        | '{' => s.withDB DB.pushScope
        | '}' => s.withDB (DB.popScope pos)
        | 'c' => { s with tokp := TokenParser.const }
        | 'v' => { s with tokp := TokenParser.var }
        | 'd' => { s with tokp := TokenParser.djvars #[] }
        | _ => s.label pos tk
      else s.label pos tk
    | TokenParser.const => s.sym pos tk Object.const
    | TokenParser.var => s.sym pos tk Object.var
    | TokenParser.djvars arr =>
      if tk.eqArray "$.".toAscii then { s with tokp := TokenParser.start } else
      s.withMath pos tk fun s tk => do
        unless s.db.isVar tk do return s.mkError pos s!"{tk} is not a variable"
        let mut s := s
        for tk1 in arr do
          if tk1 == tk then
            return s.mkError pos s!"duplicate disjoint variable {tk}"
          let p := if tk1 < tk then (tk1, tk) else (tk, tk1)
          s := s.withDB fun db => db.withDJ fun dj => dj.push p
        { s with tokp := TokenParser.djvars (arr.push tk) }
    | TokenParser.math arr p =>
      if tk.eqArray p.k.delim then
        s.feedTokens arr p
      else
        s.withMath pos tk fun s tk => do
          let tk ← match s.db.find? tk with
          | some (Object.const _) => Sym.const tk
          | some (Object.var _) => Sym.var tk
          | _ => return s.mkError pos s!"{tk} is not a constant or variable"
          { s with tokp := TokenParser.math (arr.push tk) p }
    | TokenParser.label pos lab =>
      if tk.len == 2 && tk[0] == '$'.toUInt8 then
        let go (s : ParserState) (k : TokensKind) :=
          { s with tokp := TokenParser.math #[] ⟨k, pos, lab⟩ }
        match tk[1].toChar with
        | 'f' => go s TokensKind.float
        | 'e' => go s TokensKind.ess
        | 'a' => go s TokensKind.ax
        | 'p' => go s TokensKind.thm
        | _ => s.mkError pos s!"unknown statement type {(toLabel tk).2}"
      else s.mkError pos s!"unknown statement type {(toLabel tk).2}"
    | TokenParser.proof pr =>
      let s := { s with tokp := arbitrary }
      if tk.eqArray "$.".toAscii then s.finishProof pr
      else s.feedProof tk pr

inductive OldToken
| this (off : Nat)
| old (base off : Nat) (arr : ByteArray)

inductive FeedState
| ws : FeedState
| token : OldToken → FeedState

def updateLine (s : ParserState) (i : Nat) (c : UInt8) : ParserState :=
if c == '\n'.toUInt8 then { s with line := s.line + 1, linepos := i + 1 } else s

@[inline] def feedOne (base : Nat) (arr : ByteArray)
  (IH : FeedState → ParserState → ParserState)
  (i : Fin arr.size) (rs : FeedState) (s : ParserState) : ParserState :=
  let c := arr.get! i
  if isWhitespace c then
    match rs with
    | FeedState.ws =>
      let s := s.updateLine (base + i) c
      IH FeedState.ws s
    | FeedState.token ot =>
      let s := match ot with
      | OldToken.this off => s.feedToken (base + off) ⟨arr, off, i - off⟩
      | OldToken.old base off arr' => s.feedToken (base + off)
        ⟨arr.copySlice 0 arr' arr'.size i false, off, arr'.size - off + i⟩
      let s : ParserState := s.updateLine (base + i) c
      if let some ⟨e, _⟩ := s.db.error? then
        { s with db := { s.db with error? := some ⟨e, i.1+1⟩ } }
      else IH FeedState.ws s
  else
    let rs := if let FeedState.ws := rs then FeedState.token (OldToken.this i) else rs
    IH rs s

@[inline] def feedFinish (base : Nat) (arr : ByteArray)
  (rs : FeedState) (s : ParserState) : ParserState :=
  { s with charp :=
    match rs with
    | FeedState.ws => CharParser.ws
    | FeedState.token ot =>
      match ot with
      | OldToken.this off => CharParser.token base ⟨arr, off⟩
      | OldToken.old base off arr' => CharParser.token base ⟨arr' ++ arr, off⟩ }

partial def feed.impl (base : Nat) (arr : ByteArray)
  (i : Nat) (rs : FeedState) (s : ParserState) : ParserState :=
if h : i < arr.size then
  feedOne base arr (impl base arr (i+1)) ⟨i, h⟩ rs s
else feedFinish base arr rs s

set_option codegen false in
@[implementedBy feed.impl]
def feed (base : Nat) (arr : ByteArray)
  (i : Nat) (rs : FeedState) (s : ParserState) : ParserState :=
(upNatWF arr.size).fix (x := i) (C := fun _ => ∀ rs s, _) (rs := rs) (s := s)
  fun i IH rs s =>
    if h : i < arr.size then
      feedOne base arr (IH (i+1) (UpNat.next h)) ⟨i, h⟩ rs s
    else feedFinish base arr rs s

def feedAll (s : ParserState) (base : Nat) (arr : ByteArray) : ParserState :=
  match s.charp with
  | CharParser.ws => s.feed base arr 0 FeedState.ws
  | CharParser.token base' ⟨arr', off⟩ =>
    let s := { s with charp := arbitrary }
    s.feed base arr 0 (FeedState.token (OldToken.old base' off arr'))

def done (s : ParserState) (base : Nat) : DB := do
  let mut s := s
  if let CharParser.token pos tk := s.charp then
    s := s.feedToken pos tk.toSlice
  let base := s.mkPos base
  let { db := db, tokp := tokp, ..} := s
  match tokp with
  | TokenParser.start => db
  | TokenParser.comment _ => db.mkError base "unclosed comment"
  | TokenParser.const => db.mkError base "unclosed $c"
  | TokenParser.var => db.mkError base "unclosed $v"
  | TokenParser.djvars _ => db.mkError base "unclosed $d"
  | TokenParser.math _ p => match p.k with
    | TokensKind.float => db.mkError base "unclosed $f"
    | TokensKind.ess => db.mkError base "unclosed $e"
    | TokensKind.ax => db.mkError base "unclosed $a"
    | TokensKind.thm => db.mkError base "unclosed $p"
  | TokenParser.label pos _ => db.mkError pos "not a command"
  | TokenParser.proof _ => db.mkError base "unclosed $p proof"

end ParserState

partial def check (fname : String) : IO DB := do
  let h ← Handle.mk fname IO.FS.Mode.read true
  let rec loop (s : ParserState) (base : Nat) : IO DB := do
    if ← h.isEof then
      s.done base
    else
      let buf ← h.read 1024
      let s := s.feedAll base buf
      if s.db.error?.isSome then s.db
      else loop s (base + buf.size)
  loop Inhabited.default 0

end Verify
end Metamath
