import Std.Data.HashMap
import Std.Data.HashSet

section forMathlib

namespace Nat

protected theorem sub_sub : ∀ (n m k : Nat), n - m - k = n - (m + k)
| n, m, 0        => by rw [Nat.add_zero, Nat.sub_zero]
| n, m, (succ k) => by rw [add_succ, sub_succ, sub_succ, Nat.sub_sub n m k]

protected theorem sub_add_cancel : {a b : Nat} → a ≤ b → b - a + a = b
| 0, b, _ => rfl
| a+1, b+1, h => congrArg Nat.succ $ show (b+1) - (a + 1) + a = b by
  rw [Nat.add_comm  a, ← Nat.sub_sub]
  exact Nat.sub_add_cancel h

end Nat

end forMathlib

theorem Fin.val_eq_of_lt : a < n.succ → (@Fin.ofNat n a).val = a := Nat.mod_eq_of_lt
theorem UInt32.val_eq_of_lt : a < UInt32.size → (UInt32.ofNat a).val = a := Fin.val_eq_of_lt

theorem toChar_aux (n : Nat) (h : n < UInt8.size) : Nat.isValidChar (UInt32.ofNat n).1 := by
  rw [UInt32.val_eq_of_lt]
  exact Or.inl (Nat.ltTrans h (by decide))
  exact Nat.ltTrans h (by decide)

def UInt8.toChar (n : UInt8) : Char := ⟨n.toUInt32, toChar_aux n.1 n.1.2⟩
def Char.toUInt8 (n : Char) : UInt8 := n.1.toUInt8

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

partial instance : ForIn m ByteSlice UInt8 where
  forIn bs b f :=
    let ⟨arr, off, len⟩ := bs
    let _end := off + len
    let rec loop (i : Nat) (b) := do
      if i < _end then
        match ← f (arr.get! i) b with
        | ForInStep.done b => pure b
        | ForInStep.yield b => loop (i+1) b
      else b
    loop off b

end ByteSlice

def ByteSliceT.toSlice : ByteSliceT → ByteSlice
| ⟨arr, off⟩ => ⟨arr, off, arr.size - off⟩

def ByteArray.toSlice (arr : ByteArray) : ByteSlice := ⟨arr, 0, arr.size⟩

partial def ByteSlice.eqArray (bs : ByteSlice) (arr : ByteArray) : Bool :=
  let rec loop (i j : Nat) :=
    if j < arr.size then
      bs.arr.get! i == arr.get! j && loop (i+1) (j+1)
    else true
  bs.len == arr.size && loop bs.off 0

partial def String.toAscii (s : String) : ByteArray := do
  let mut out := ByteArray.empty
  let rec loop (out p) :=
    if s.atEnd p then out else
    let c := s.get p
    loop (out.push c.toUInt8) (s.next p)
  loop ByteArray.empty 0

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

structure Error := (pos : Pos) (msg : String)

def DJ := String × String
structure Frame where
  dj : Array DJ
  hyps : Array String
deriving Inhabited

def Frame.size : Frame → Nat × Nat
| ⟨dj, hyps⟩ => (dj.size, hyps.size)

def Frame.shrink : Frame → Nat × Nat → Frame
| ⟨dj, hyps⟩, (x, y) => ⟨dj.shrink x, hyps.shrink y⟩

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
| assert (l : String) (f : Formula) (fr : Frame)

instance : ToString HeapEl where
  toString
  | HeapEl.fmla f => toString f
  | HeapEl.assert l _ _ => s!"<{l}>"

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

structure DB where
  frame : Frame
  scopes : Array (Nat × Nat)
  objects : HashMap String Object
  error? : Option Error
deriving Inhabited

namespace DB

@[inline] def error (s : DB) : Bool := s.error?.isSome

def mkError (s : DB) (pos : Pos) (msg : String) : DB :=
  { s with error? := some ⟨pos, msg⟩ }

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

def insertAssert (db : DB) (pos : Pos) (l : String) (fmla : Formula) : DB := do
  match db.trimFrame' fmla with
  | Except.ok fr => db.insert pos l (Object.assert fmla fr)
  | Except.error msg => db.mkError pos msg

def mkProofState (db : DB) (pos : Pos) (l : String) (fmla : Formula) : ProofState := do
  let (ok, fr) := db.trimFrame fmla
  let mut heap := #[]
  for l in fr.hyps do
    if let some (Object.hyp _ f _) := db.find? l then
      heap := heap.push (HeapEl.fmla f)
  ⟨pos, l, fmla, fr, heap, #[], ProofTokenParser.start⟩

def preload (db : DB) (pr : ProofState) (l : String) : Except String ProofState :=
  match db.find? l with
  | some (Object.hyp true _ _) => throw "$e found in paren list"
  | some (Object.hyp _ f _) => pr.pushHeap (HeapEl.fmla f)
  | some (Object.assert f fr _) => pr.pushHeap (HeapEl.assert l f fr)
  | _ => throw s!"statement {l} not found"

partial def stepAssert (db : DB) (pr : ProofState) (f : Formula) (l : String) : Frame → Except String ProofState
| ⟨dj, hyps⟩ => do
  if h : hyps.size ≤ pr.stack.size then
    let off : {off // off + hyps.size = pr.stack.size} :=
      ⟨pr.stack.size - hyps.size, Nat.sub_add_cancel h⟩
    let rec checkHyp (subst : HashMap String Formula) (i : Nat) :
      Except String (HashMap String Formula) := do
      if h : i < hyps.size then
        let val := pr.stack.get ⟨off.1 + i,
          let thm {a b n} : i < a → n + a = b → n + i < b
          | h, rfl => Nat.addLtAddLeft h _
          thm h off.2⟩
        if let some (Object.hyp ess f _) := db.find? (hyps.get ⟨i, h⟩) then
          if f[0] == val[0] then
            if ess then
              if (← f.subst subst) == val then
                checkHyp subst (i+1)
              else throw "type error in substitution"
            else
              checkHyp (subst.insert f[1].value val) (i+1)
          else throw s!"bad typecode in substitution {hyps[i]}: {f} / {val}"
        else unreachable!
      else subst
    let subst ← checkHyp HashMap.empty 0
    for (v1, v2) in dj do
      let e1 := subst.find! v1
      let e2 := subst.find! v2
      let intersect :=
        e1.foldlVars (init := false) fun b s1 =>
          e2.foldlVars b fun b s2 => b || s1 == s2
      if intersect then throw "disjoint variable violation"
    let concl ← f.subst subst
    pure { pr with stack := (pr.stack.shrink off).push concl }
  else throw "stack underflow"

def stepNormal (db : DB) (pr : ProofState) (l : String) : Except String ProofState :=
  match db.find? l with
  | some (Object.hyp _ f _) => pr.push f
  | some (Object.assert f fr _) => db.stepAssert pr f l fr
  | _ => throw s!"statement {l} not found"

def stepProof (db : DB) (pr : ProofState) (i : Nat) : Except String ProofState :=
  match pr.heap.get? i with
  | none => throw "proof backref index out of range"
  | some (HeapEl.fmla f) => pr.push f
  | some (HeapEl.assert l f fr) => db.stepAssert pr f l fr

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
  if let some ⟨pos, msg⟩ := s.db.error? then
    s.withDB fun db => { db with error? := some ⟨pos, s!"at {l}: {msg}"⟩ }
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
    let s := s.withDB fun db => db.insertAssert pos l arr
    pure { s with tokp := TokenParser.start }
  | TokensKind.thm =>
    let pr := s.db.mkProofState pos l arr
    pure { s with tokp := TokenParser.proof pr }

partial def feedProof (s : ParserState) (tk : ByteSlice) (pr : ProofState) : ParserState :=
  withAt pr.label fun _ =>
    match go pr with
    | Except.ok pr => { s with tokp := TokenParser.proof pr }
    | Except.error msg => s.mkError pr.pos msg
where
  go (pr : ProofState) : Except String ProofState := do
    match pr.ptp with
    | ProofTokenParser.start =>
      if tk.eqArray "(".toAscii then
        pure { pr with ptp := ProofTokenParser.preload }
      else go { pr with ptp := ProofTokenParser.normal }
    | ProofTokenParser.preload =>
      if tk.eqArray ")".toAscii then
        pure { pr with ptp := ProofTokenParser.compressed 0 }
      else
        let (ok, tk) := toLabel tk
        if ok then s.db.preload pr tk
        else throw s!"invalid label '{tk}'"
    | ProofTokenParser.normal =>
      let (ok, tk) := toLabel tk
      if ok then s.db.stepNormal pr tk
      else throw s!"invalid label '{tk}'"
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

inductive RunState
| ws : RunState
| token : OldToken → RunState

def updateLine (s : ParserState) (i : Nat) (c : UInt8) : ParserState :=
if c == '\n'.toUInt8 then { s with line := s.line + 1, linepos := i + 1 } else s

partial def run (s : ParserState) (base : Nat) (arr : ByteArray)
  (i : Nat) (rs : RunState) : ParserState :=
if i < arr.size then
  let c := arr.get! i
  if isWhitespace c then
    match rs with
    | RunState.ws =>
      let s := s.updateLine (base + i) c
      s.run base arr (i+1) RunState.ws
    | RunState.token ot =>
      let s := match ot with
      | OldToken.this off => s.feedToken (base + off) ⟨arr, off, i - off⟩
      | OldToken.old base off arr' => s.feedToken (base + off)
        ⟨arr.copySlice 0 arr' arr'.size i false, off, arr'.size - off + i⟩
      if s.db.error?.isSome then s else
      let s := s.updateLine (base + i) c
      s.run base arr (i+1) RunState.ws
  else
    let rs := if let RunState.ws := rs then RunState.token (OldToken.this i) else rs
    s.run base arr (i+1) rs
else
  { s with charp :=
    match rs with
    | RunState.ws => CharParser.ws
    | RunState.token ot =>
      match ot with
      | OldToken.this off => CharParser.token base ⟨arr, off⟩
      | OldToken.old base off arr' => CharParser.token base ⟨arr' ++ arr, off⟩ }

def feed (s : ParserState) (base : Nat) (arr : ByteArray) : ParserState :=
  match s.charp with
  | CharParser.ws => s.run base arr 0 RunState.ws
  | CharParser.token base' ⟨arr', off⟩ =>
    let s := { s with charp := arbitrary }
    s.run base arr 0 (RunState.token (OldToken.old base' off arr'))

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
      let s := s.feed base buf
      if s.db.error?.isSome then s.db
      else loop s (base + buf.size)
  loop Inhabited.default 0

end Metamath

open Metamath in
def main (n : List String) : IO UInt32 := do
  let db ← check $ n.getD 0 "set.mm"
  match db.error? with
  | none =>
    IO.println s!"verified, {db.objects.size} objects"
    pure 0
  | some ⟨pos, err⟩ =>
    IO.println s!"at {pos}: {err}"
    pure 1
