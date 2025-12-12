import Std.Data.HashMap
import Std.Data.HashSet
import Std.Data.ByteSlice


def UInt8.toChar (n : UInt8) : Char := ⟨n.toUInt32, by
  have := n.toFin.2
  simp [size, UInt32.isValidChar, Nat.isValidChar] at *; omega⟩

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
  le_size : off ≤ arr.size

namespace ByteSliceT

@[inline] def size (self : ByteSliceT) : Nat := self.arr.size - self.off

instance : GetElem ByteSliceT Nat UInt8 fun _ _ => True where
  getElem self idx _ := self.arr[self.off + idx]!

end ByteSliceT

@[inline] def ByteArray.toByteSliceCore (as : ByteArray) (start : Nat) (stop : Nat)
    (h₁ : start ≤ stop) (h₂ : stop ≤ as.size) : ByteSlice := by
  let P (_ : ByteSlice) := True
  have : P (as.toByteSlice start stop) := trivial
  clear_value P
  simp [ByteArray.toByteSlice, h₁, h₂] at this
  exact let y := _; have : P y := this; y

def ByteArray.toSliceT (arr : ByteArray) : ByteSliceT := ⟨arr, 0, Nat.zero_le _⟩

def forIn.loop [Monad m] (f : UInt8 → β → m (ForInStep β))
    (arr : ByteArray) (off stop : Nat) (i : Nat) (b : β) : m β := do
  if i < stop then
    match ← f arr[i]! b with
    | ForInStep.done b => pure b
    | ForInStep.yield b => loop f arr off stop (i+1) b
  else pure b

instance : ForIn m ByteSlice UInt8 :=
  ⟨fun bs init f => forIn.loop f bs.byteArray bs.start bs.stop bs.start init⟩

@[inline] def ByteSliceT.toSlice : ByteSliceT → ByteSlice
  | ⟨arr, off, h⟩ => ByteArray.toByteSliceCore arr off _ h (Nat.le_refl _)

def ByteSlice.eqArray (bs : ByteSlice) (arr : ByteArray) : Bool :=
  if _ : bs.size = arr.size then
    let rec go (i : Nat) : Bool :=
      if _ : i < bs.size then
        bs[i] = arr[i] && go (i + 1)
      else true
    go 0
  else false

def String.toAscii (s : String) : ByteArray := loop ByteArray.empty 0 where
  loop (out : ByteArray) (p : Pos.Raw) : ByteArray :=
    if h : Pos.Raw.atEnd s p then out else
      let c := Pos.Raw.get s p
      have := Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h))
        (String.Pos.Raw.byteIdx_lt_byteIdx_next s _)
      loop (out.push c.toUInt8) (Pos.Raw.next s p)
  termination_by s.rawEndPos.1 - p.1

def ByteSlice.toString (bs : ByteSlice) : String := Id.run do
  let mut s := ""
  for c in bs do s := s.push c.toChar
  s

instance : ToString ByteSlice where
  toString bs := Id.run do
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

def toLabel (bs : ByteSlice) : Bool × String := Id.run do
  let mut ok := true
  let mut s := ""
  for c in bs do
    s := s.push c.toChar
    unless isLabelChar c do ok := false
  (ok, s)

def toMath (bs : ByteSlice) : Bool × String := Id.run do
  let mut ok := true
  let mut s := ""
  for c in bs do
    s := s.push c.toChar
    unless isPrintable c do ok := false
  (ok, s)

structure Pos where (line col : Nat)

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
  | .const _ => false
  | .var _ => true

def Sym.value : Sym → String
  | .const c => c
  | .var v => v

instance : BEq Sym := ⟨fun a b => a.value == b.value⟩

abbrev Formula := Array Sym

instance : ToString Formula where
  toString f := Id.run do
    let s := f[0]!.value
    f.foldl (init := s) (start := 1) fun (s:String) v =>
      s ++ " " ++ v.value

def Formula.subst (σ : HashMap String Formula) (f : Formula) : Except String Formula := do
  let mut f' := #[]
  for c in f do
    match c with
    | .const _ => f' := f'.push c
    | .var v =>
      match σ[v]? with
      | none => throw s!"variable {v} not found"
      | some e => f' := e.foldl Array.push f' 1
  pure f'

def Formula.foldlVars (self : Formula) (init : α) (f : α → String → α) : α :=
  self.foldl (init := init) (start := 1) fun a v =>
    match v with
    | .var v => f a v
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
  | .fmla f => toString f
  | .assert f fr => s!"{fr} |- {f}"

structure ProofState where
  pos : Pos
  label : String
  fmla : Formula
  frame : Frame
  heap : Array HeapEl
  stack : Array Formula
  ptp : ProofTokenParser

instance : ToString ProofState where
  toString p := Id.run do
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
  if let some f := pr.stack.back? then
    pure <| pr.pushHeap (.fmla f)
  else
    throw "can't save empty stack"

end ProofState

inductive Error
  | error (pos : Pos) (msg : String)
  | ax (pos : Pos) (l : String) (f : Formula) (fr : Frame)
  | thm (pos : Pos) (l : String) (f : Formula) (fr : Frame)

structure Interrupt where
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
  { s with error? := some ⟨.error pos msg, default⟩ }

def pushScope (s : DB) : DB :=
  { s with scopes := s.scopes.push s.frame.size }

def popScope (pos : Pos) (db : DB) : DB :=
  if let some sc := db.scopes.back? then
    { db with frame := db.frame.shrink sc, scopes := db.scopes.pop }
  else
    db.mkError pos "can't pop global scope"

def find? (db : DB) (l : String) : Option Object := db.objects[l]?

def isConst (db : DB) (tk : String) : Bool :=
  if let some (.const _) := db.find? tk then true else false

def isVar (db : DB) (tk : String) : Bool :=
  if let some (.var _) := db.find? tk then true else false

def isSym (db : DB) (tk : String) : Bool :=
  match db.find? tk with
  | some (.const _) => true
  | some (.var _) => true
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
    | .var _ => if let .var _ := obj l then true else false
    | _ => false
    if ok then db else db.mkError pos s!"duplicate symbol/assert {l}"
  else
    { db with objects := db.objects.insert l (obj l) }

def insertHyp (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula) : DB :=
  let db := db.insert pos l (.hyp ess f)
  db.withHyps fun hyps => hyps.push l

def trimFrame (db : DB) (fmla : Formula) (fr := db.frame) : Bool × Frame := Id.run do
  let collectVars (fmla : Formula) vars :=
    fmla.foldlVars vars HashSet.insert
  let mut vars : HashSet String := collectVars fmla ∅
  for l in fr.hyps do
    if let some (.hyp true f _) := db.find? l then
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
      if let some (.hyp false f _) := db.find? l then
        if inHyps then ok := false
        vars.contains f[1]!.value
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
  | .ok fr =>
    if db.interrupt then { db with error? := some ⟨.ax pos l fmla fr, default⟩ }
    else db.insert pos l (.assert fmla fr)
  | .error msg => db.mkError pos msg

def mkProofState (db : DB) (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) :
    ProofState := Id.run do
  let mut heap := #[]
  for l in fr.hyps do
    if let some (.hyp _ f _) := db.find? l then
      heap := heap.push (.fmla f)
  ⟨pos, l, fmla, fr, heap, #[], .start⟩

def preload (db : DB) (pr : ProofState) (l : String) : Except String ProofState :=
  match db.find? l with
  | some (.hyp true _ _) => throw "$e found in paren list"
  | some (.hyp _ f _) => return pr.pushHeap (.fmla f)
  | some (.assert f fr _) => return pr.pushHeap (.assert f fr)
  | _ => throw s!"statement {l} not found"

variable (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off // off + hyps.size = stack.size}) in
def checkHyp (i : Nat) (subst : HashMap String Formula) :
    Except String (HashMap String Formula) := do
  if h : i < hyps.size then
    let val := stack[off.1 + i]'(
      let thm {a b n} : i < a → n + a = b → n + i < b
      | h, rfl => Nat.add_lt_add_left h _
      thm h off.2)
    if let some (.hyp ess f _) := db.find? hyps[i] then
      if f[0]! == val[0]! then
        if ess then
          if (← f.subst subst) == val then
            checkHyp (i+1) subst
          else throw "type error in substitution"
        else
          checkHyp (i+1) (subst.insert f[1]!.value val)
      else throw s!"bad typecode in substitution {hyps[i]}: {f} / {val}"
    else unreachable!
  else pure subst

def stepAssert (db : DB) (pr : ProofState) (f : Formula) : Frame → Except String ProofState
  | ⟨dj, hyps⟩ => do
    if h : hyps.size ≤ pr.stack.size then
      let off : {off // off + hyps.size = pr.stack.size} :=
        ⟨pr.stack.size - hyps.size, Nat.sub_add_cancel h⟩
      let subst ← checkHyp db hyps pr.stack off 0 ∅
      let disj s1 s2 := s1 != s2 &&
        db.frame.dj.contains (if s1 < s2 then (s1, s2) else (s2, s1))
      for (v1, v2) in dj do
        let e1 := subst[v1]!
        let e2 := subst[v2]!
        let disjoint :=
          e1.foldlVars (init := true) fun b s1 =>
            e2.foldlVars b fun b s2 => b && disj s1 s2
        if !disjoint then throw "disjoint variable violation"
      let concl ← f.subst subst
      pure { pr with stack := (pr.stack.shrink off).push concl }
    else throw "stack underflow"

def stepNormal (db : DB) (pr : ProofState) (l : String) : Except String ProofState :=
  match db.find? l with
  | some (.hyp _ f _) => return pr.push f
  | some (.assert f fr _) => db.stepAssert pr f fr
  | _ => throw s!"statement {l} not found"

def stepProof (db : DB) (pr : ProofState) (i : Nat) : Except String ProofState :=
  match pr.heap[i]? with
  | none => throw "proof backref index out of range"
  | some (.fmla f) => return pr.push f
  | some (.assert f fr) => db.stepAssert pr f fr

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

instance : ToString TokensKind where
  toString
  | .float => "float"
  | .ess => "ess"
  | .ax => "ax"
  | .thm => "thm"

def TokensKind.delim : TokensKind → ByteArray
  | .thm => "$=".toAscii
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
  | .start => "start"
  | .comment p => "comment " ++ toString p
  | .const => "const"
  | .var => "var"
  | .djvars s => s!"djvars {s}"
  | .math s p => s!"math {s} {p}"
  | .label pos l => s!"at {pos}: ? {l}"
  | .proof p => ToString.toString p

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
  if let some ⟨.error pos msg, i⟩ := s.db.error? then
    s.withDB fun db => { db with error? := some ⟨.error pos s!"at {l}: {msg}", i⟩ }
  else s

def label (s : ParserState) (pos : Pos) (tk : ByteSlice) : ParserState :=
  let (ok, tk) := toLabel tk
  if ok then { s with tokp := .label pos tk }
  else s.mkError pos s!"invalid label '{tk}'"

def withMath (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (f : ParserState → String → ParserState) : ParserState :=
  let (ok, tk) := toMath tk
  if !ok then s.mkError pos s!"invalid math string '{tk}'" else
  f s tk

def sym (s : ParserState) (pos : Pos) (tk : ByteSlice) (f : String → Object) : ParserState :=
  if tk.eqArray "$.".toAscii then
    { s with tokp := .start }
  else s.withMath pos tk fun s tk =>
    s.withDB fun db => db.insert pos tk f

def resumeAxiom (s : ParserState)
    (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) : ParserState :=
  s.withDB fun db => db.insert pos l (.assert fmla fr)

def resumeThm (s : ParserState)
    (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) : ParserState :=
  let pr := s.db.mkProofState pos l fmla fr
  { s with tokp := .proof pr }

def feedTokens (s : ParserState) (arr : Array Sym) : TokensParser → ParserState
  | ⟨k, pos, l⟩ => withAt l fun _ => Id.run do
    unless arr.size > 0 && !arr[0]!.isVar do
      return s.mkError pos "first symbol is not a constant"
    match k with
    | .float =>
      unless arr.size == 2 && arr[1]!.isVar do
        return s.mkError pos "expected a constant and a variable"
      let s := s.withDB fun db => db.insertHyp pos l false arr
      pure { s with tokp := .start }
    | .ess =>
      let s := s.withDB fun db => db.insertHyp pos l true arr
      pure { s with tokp := .start }
    | .ax =>
      let s := s.withDB fun db => db.insertAxiom pos l arr
      pure { s with tokp := .start }
    | .thm =>
      match s.db.trimFrame' arr with
      | .ok fr =>
        if s.db.interrupt then
          s.withDB fun db => { db with error? := some ⟨.thm pos l arr fr, default⟩ }
        else s.resumeThm pos l arr fr
      | .error msg => s.mkError pos msg

def feedProof (s : ParserState) (tk : ByteSlice) (pr : ProofState) : ParserState :=
  withAt pr.label fun _ =>
    match go pr with
    | .ok pr => { s with tokp := .proof pr }
    | .error msg => s.mkError pr.pos msg
where
  goNormal (pr : ProofState) :=
    let (ok, tk) := toLabel tk
    if ok then s.db.stepNormal pr tk
    else throw s!"invalid label '{tk}'"
  go (pr : ProofState) : Except String ProofState := do
    match pr.ptp with
    | .start =>
      if tk.eqArray "(".toAscii then
        pure { pr with ptp := .preload }
      else goNormal { pr with ptp := .normal }
    | .preload =>
      if tk.eqArray ")".toAscii then
        pure { pr with ptp := .compressed 0 }
      else
        let (ok, tk) := toLabel tk
        if ok then s.db.preload pr tk
        else throw s!"invalid label '{tk}'"
    | .normal => goNormal pr
    | .compressed chr =>
      let mut pr := pr
      let mut chr := chr
      for c in tk do
        if 'A'.toUInt8 ≤ c && c ≤ 'Z'.toUInt8 then
          if c ≤ 'T'.toUInt8 then
            let n := 20 * chr + (c - 'A'.toUInt8).toNat
            pr ← s.db.stepProof pr n
            chr := 0
          else if c < 'Z'.toUInt8 then
            chr := 5 * chr + (c - 'T'.toUInt8).toNat
          else
            pr ← pr.save
            chr := 0
        else if c = '?'.toUInt8 then
          throw "proof contains '?'"
        else
          throw "proof parse error"
      pure { pr with ptp := .compressed chr }

def finishProof (s : ParserState) : ProofState → ParserState
  | ⟨pos, l, fmla, fr, _, stack, ptp⟩ => withAt l fun _ => Id.run do
    let s := { s with tokp := .start }
    match ptp with
    | .compressed 0 => ()
    | .normal => ()
    | _ => return s.mkError pos "proof parse error"
    unless stack.size == 1 do
      return s.mkError pos "more than one element on stack"
    unless stack[0]! == fmla do
      return s.mkError pos "theorem does not prove what it claims"
    s.withDB fun db => db.insert pos l (.assert fmla fr)

def feedToken (s : ParserState) (pos : Nat) (tk : ByteSlice) : ParserState :=
  let pos := s.mkPos pos
  match s.tokp with
  | .comment p =>
    if tk.eqArray "$)".toAscii then { s with tokp := p } else s
  | p =>
    if tk.eqArray "$(".toAscii then { s with tokp := p.comment } else
    match p with
    | .comment _ => unreachable!
    | .start =>
      if _ : tk.size = 2 then
        if tk[0] == '$'.toUInt8 then
          match tk[1].toChar with
          | '{' => s.withDB .pushScope
          | '}' => s.withDB (.popScope pos)
          | 'c' => { s with tokp := .const }
          | 'v' => { s with tokp := .var }
          | 'd' => { s with tokp := .djvars #[] }
          | _ => s.label pos tk
        else s.label pos tk
      else s.label pos tk
    | .const => s.sym pos tk .const
    | .var => s.sym pos tk .var
    | .djvars arr =>
      if tk.eqArray "$.".toAscii then { s with tokp := .start } else
      s.withMath pos tk fun s tk => Id.run do
        unless s.db.isVar tk do return s.mkError pos s!"{tk} is not a variable"
        let mut s := s
        for tk1 in arr do
          if tk1 == tk then
            return s.mkError pos s!"duplicate disjoint variable {tk}"
          let p := if tk1 < tk then (tk1, tk) else (tk, tk1)
          s := s.withDB fun db => db.withDJ fun dj => dj.push p
        { s with tokp := .djvars (arr.push tk) }
    | .math arr p =>
      if tk.eqArray p.k.delim then
        s.feedTokens arr p
      else
        s.withMath pos tk fun s tk => Id.run do
          let tk ← match s.db.find? tk with
          | some (.const _) => Sym.const tk
          | some (.var _) => Sym.var tk
          | _ => return s.mkError pos s!"{tk} is not a constant or variable"
          { s with tokp := .math (arr.push tk) p }
    | .label pos lab =>
      if _ : tk.size = 2 then
        let go (s : ParserState) (k : TokensKind) :=
          { s with tokp := .math #[] ⟨k, pos, lab⟩ }
        if tk[0] == '$'.toUInt8 then
          match tk[1].toChar with
          | 'f' => go s .float
          | 'e' => go s .ess
          | 'a' => go s .ax
          | 'p' => go s .thm
          | _ => s.mkError pos s!"unknown statement type {(toLabel tk).2}"
        else s.mkError pos s!"unknown statement type {(toLabel tk).2}"
      else s.mkError pos s!"unknown statement type {(toLabel tk).2}"
    | .proof pr =>
      let s := { s with tokp := default }
      if tk.eqArray "$.".toAscii then s.finishProof pr
      else s.feedProof tk pr

inductive OldToken (arr : ByteArray)
  | this (off : Nat) (h : off ≤ arr.size)
  | old (base off : Nat) (arr : ByteArray) (h : off ≤ arr.size)

inductive FeedState (arr : ByteArray)
  | ws : FeedState arr
  | token : OldToken arr → FeedState arr

def FeedState.below (i : Nat) : FeedState arr → Prop
  | .ws => True
  | .token (.this off _) => off < i
  | .token (.old ..) => True

theorem FeedState.below.mono : ∀ {rs : FeedState arr}, FeedState.below i rs → FeedState.below (i + 1) rs
  | .ws, _ => trivial
  | .token (.this ..), h => Nat.lt_succ_of_lt h
  | .token (.old ..), _ => trivial

def updateLine (s : ParserState) (i : Nat) (c : UInt8) : ParserState :=
  if c == '\n'.toUInt8 then { s with line := s.line + 1, linepos := i + 1 } else s

def feed (base : Nat) (arr : ByteArray)
    (i : Nat) (rs : {rs : FeedState arr // rs.below i}) (s : ParserState) : ParserState :=
  if h : i < arr.size then
    let c := arr[i]
    if isWhitespace c then
      match rs with
      | ⟨.ws, _⟩ =>
        let s := s.updateLine (base + i) c
        feed base arr (i+1) ⟨.ws, ⟨⟩⟩ s
      | ⟨.token ot, h⟩ =>
        let s := match ot with
        | .this off _ =>
          s.feedToken (base + off) (arr.toByteSliceCore off i (Nat.le_of_lt h) (by omega))
        | .old base off arr' h => s.feedToken (base + off)
          ((arr.copySlice 0 arr' arr'.size i false).toByteSliceCore off _
            (by simp [ByteArray.copySlice_eq_append]; omega) (Nat.le_refl _))
        let s : ParserState := s.updateLine (base + i) c
        if let some ⟨e, _⟩ := s.db.error? then
          { s with db := { s.db with error? := some ⟨e, i+1⟩ } }
        else feed base arr (i+1) ⟨.ws, ⟨⟩⟩ s
    else
      let rs := if let ⟨.ws, _⟩ := rs then
        ⟨.token (.this i (by omega)), Nat.lt_succ_self _⟩
      else ⟨rs, rs.2.mono⟩
      feed base arr (i+1) rs s
  else
    { s with charp :=
      match rs with
      | ⟨.ws, _⟩ => .ws
      | ⟨.token (.this off h), h'⟩ => .token base ⟨arr, off, h⟩
      | ⟨.token (.old base off arr' h), h'⟩ =>
        .token base ⟨arr' ++ arr, off, by simp; omega⟩ }

def feedAll (s : ParserState) (base : Nat) (arr : ByteArray) : ParserState :=
  match s.charp with
  | .ws => s.feed base arr 0 ⟨.ws, ⟨⟩⟩
  | .token base' ⟨arr', off, h⟩ =>
    let s := { s with charp := default }
    s.feed base arr 0 ⟨.token (.old base' off arr' h), ⟨⟩⟩

def done (s : ParserState) (base : Nat) : DB := Id.run do
  let mut s := s
  if let .token pos tk := s.charp then
    s := s.feedToken pos tk.toSlice
  let base := s.mkPos base
  let { db := db, tokp := tokp, ..} := s
  match tokp with
  | .start => db
  | .comment _ => db.mkError base "unclosed comment"
  | .const => db.mkError base "unclosed $c"
  | .var => db.mkError base "unclosed $v"
  | .djvars _ => db.mkError base "unclosed $d"
  | .math _ p => match p.k with
    | .float => db.mkError base "unclosed $f"
    | .ess => db.mkError base "unclosed $e"
    | .ax => db.mkError base "unclosed $a"
    | .thm => db.mkError base "unclosed $p"
  | .label pos _ => db.mkError pos "not a command"
  | .proof _ => db.mkError base "unclosed $p proof"

end ParserState

partial def check (fname : String) : IO DB := do
  let h ← Handle.mk fname IO.FS.Mode.read
  let rec loop (s : ParserState) (base : Nat) : IO DB := do
    let buf ← h.read 1024
    if buf.isEmpty then
      return s.done base
    else
      let s := s.feedAll base buf
      if s.db.error?.isSome then return s.db
      else loop s (base + buf.size)
  loop default 0
