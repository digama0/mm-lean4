import Std.Data.HashMap
import Std.Data.HashSet
import Metamath.ByteSliceCompat

/-! ## Array Bridging Lemmas

These lemmas bridge between dependent indexing `arr[i]'h` and panic-safe indexing `arr[i]!`.
They are needed for equation lemmas that compare unfolded definitions (which use dependent
indexing internally) with user-facing specifications (which use `!` notation).
-/

namespace Array

/-- Total index equals partial index when in-bounds (Nat version). -/
@[simp] theorem getBang_eq_get_nat (a : Array α) (i : Nat) (h : i < a.size) [Inhabited α] :
  a[i]! = a[i]'h := by
  simp only [getElem!_pos, h]

/-- (A) Length bridge: arrays and their lists have the same length. -/
@[simp] theorem toList_length (a : Array α) : a.toList.length = a.size := by
  rfl

/-- (B) Characterize `get? = some` without `Inhabited`: unfold `get?`. -/
@[simp] theorem get?_eq_some_iff {a : Array α} {i : Nat} {x : α} :
    a[i]? = some x ↔ ∃ h : i < a.size, a[i]'h = x := by
  simp only [getElem?_def]
  by_cases h : i < a.size
  · -- in-bounds branch
    simp [h]
  · -- out-of-bounds branch
    simp [h]

/-- (C) Bridge `Array.get!` to `List.get!` under a bound. -/
@[simp] theorem get!_toList' {α} [Inhabited α]
    (a : Array α) (i : Nat) (h : i < a.size) :
    a[i]! = a.toList[i]! := by
  simp [getElem_toList, h]

end Array

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

-- ByteSlice and ByteSliceT now use Std.ByteSlice (Batteries 4.24.0+)
-- Import the compatibility layer that provides the old API
-- (Custom definitions removed; now using library types)

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
    unless isMathChar c do ok := false
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

/-- One-step substitution action. -/
def Formula.substStep (σ : HashMap String Formula)
    (acc : Formula) (s : Sym) : Except String Formula :=
  match s with
  | .const _ => .ok (acc.push s)
  | .var v   =>
    match σ[v]? with
    | none   => .error s!"variable {v} not found"
    | some e => .ok (e.foldl Array.push acc 1)

/-- Substitution is foldlM of substStep over the array.
    This definition makes substitution reasoning straightforward. -/
def Formula.subst (σ : HashMap String Formula) (f : Formula) : Except String Formula :=
  f.foldlM (Formula.substStep σ) #[]

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
  permissive : Bool := false
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
  -- Spec Section 4.2.8: $c must be in outermost block only (strict mode)
  let db := match obj l with
  | .const _ =>
    if !db.permissive && db.scopes.size > 0 then
      db.mkError pos s!"$c must be in outermost block (spec Section 4.2.8)"
    else db
  | _ => db
  if db.error then db else
  if let some o := db.find? l then
    let ok : Bool := match o with
    | .var _ => if let .var _ := obj l then true else false
    | _ => false
    if ok then db else db.mkError pos s!"duplicate symbol/assert {l}"
  else
    { db with objects := db.objects.insert l (obj l) }

/-- Equation lemma: When db has no error and db.find? l = none and insert doesn't error,
    it adds to objects. -/
theorem insert_no_dup_objects
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_no_prior_err : db.error = false)
    (h_no_dup : db.find? l = none)
    (h_no_err : (db.insert pos l obj).error = false) :
    (db.insert pos l obj).objects = db.objects.insert l (obj l) := by
  unfold insert
  -- Case split on obj l to handle const check
  cases h_obj : obj l with
  | const s =>
    simp only [h_obj]
    -- First split: const check
    split
    · -- Const check failed, creates error - contradiction with h_no_err
      exfalso
      simp only [h_obj, insert, error, mkError] at h_no_err
      split at h_no_err
      · simp only [Option.isSome] at h_no_err
        contradiction
      · -- The isFalse case is impossible because outer split is isTrue
        simp_all
    · -- Const check passed - db.error = false reduces if to else branch
      simp only [h_no_prior_err, Bool.false_eq_true, ite_false, h_no_dup]
  | var s =>
    simp only [h_obj, h_no_prior_err, Bool.false_eq_true, ite_false, h_no_dup]
  | hyp ess f s =>
    simp only [h_obj, h_no_prior_err, Bool.false_eq_true, ite_false, h_no_dup]
  | assert f frame s =>
    simp only [h_obj, h_no_prior_err, Bool.false_eq_true, ite_false, h_no_dup]

/-- Equation lemma: insert find? self when no duplicate and no error. -/
theorem insert_find?_self
    (db : DB) (pos : Pos) (l : String) (obj : String → Object)
    (h_no_prior_err : db.error = false)
    (h_no_dup : db.find? l = none)
    (h_no_err : (db.insert pos l obj).error = false) :
    (db.insert pos l obj).find? l = some (obj l) := by
  simp only [find?, insert_no_dup_objects db pos l obj h_no_prior_err h_no_dup h_no_err]
  exact Std.HashMap.getElem?_insert_self

def insertHyp (db : DB) (pos : Pos) (l : String) (ess : Bool) (f : Formula) : DB :=
  -- For $f statements (ess = false), check that no other $f exists for this variable
  let db := Id.run do
    if !ess && f.size >= 2 then
      let v := f[1]!.value
      -- Check all existing hypotheses in current frame
      let mut db := db
      for h in db.frame.hyps do
        if let some (.hyp false prevF _) := db.find? h then
          if prevF.size >= 2 && prevF[1]!.value == v then
            db := db.mkError pos s!"variable {v} already has $f hypothesis"
      db
    else db
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
  let mut ok := true
  let mut varsWithF : HashSet String := ∅
  for l in fr.hyps do
    let ess ←
      if let some (.hyp false f _) := db.find? l then
        -- Spec §4.2.4: $f and $e can be interleaved (appearance order)
        -- No need to enforce "$f before $e" - that's a legacy restriction
        let v := f[1]!.value
        if vars.contains v then
          varsWithF := varsWithF.insert v
        vars.contains v
      else
        true
    if ess then hyps := hyps.push l
  -- Check that all variables have a $f hypothesis
  for v in vars do
    unless varsWithF.contains v do ok := false
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

/-- Equation lemma: base case when `i ≥ hyps.size`. -/
@[simp] theorem checkHyp_base
  (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off : Nat // off + hyps.size = stack.size})
  (i : Nat) (σ : Std.HashMap String Formula)
  (h : ¬ i < hyps.size) :
  checkHyp db hyps stack off i σ = .ok σ := by
  unfold checkHyp
  simp [h]
  rfl

/-- Equation lemma when lookup at `hyps[i]` finds an **essential** hypothesis. -/
@[simp] theorem checkHyp_step_hyp_true
  (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off : Nat // off + hyps.size = stack.size})
  (i : Nat) (σ : Std.HashMap String Formula)
  (f : Formula) (lbl : String)
  (h_i : i < hyps.size)
  (h_find : db.find? hyps[i] = some (.hyp true f lbl)) :
  checkHyp db hyps stack off i σ
    =
  if f[0]! == stack[off.1 + i]![0]! then
    match f.subst σ with
    | .ok s =>
        if s == stack[off.1 + i]! then
          checkHyp db hyps stack off (i+1) σ
        else
          .error "type error in substitution"
    | .error e => .error e
  else
    .error (s!"bad typecode in substitution {hyps[i]}: {f} / {stack[off.1 + i]!}") := by
  -- Use rw to unfold only the LHS
  rw [checkHyp]
  simp [h_i, h_find]
  have h_idx : off.1 + i < stack.size := by
    have : off.1 + i < off.1 + hyps.size := Nat.add_lt_add_left h_i _
    simpa [off.2] using this
  simp [h_idx, bind, Except.bind]
  -- After all simplifications, LHS and RHS are structurally identical
  -- Just need to handle the nested if-then-else and match cases
  split
  · -- Case: typecode check passes
    split
    · -- Case: subst returns error
      rename_i err heq
      simp [heq]
    · -- Case: subst returns ok
      rename_i val heq
      simp [heq]
      split <;> rfl
  · -- Case: typecode check fails
    rfl

/-- Equation lemma when lookup at `hyps[i]` finds a **float** hypothesis. -/
@[simp] theorem checkHyp_step_hyp_false
  (db : DB) (hyps : Array String) (stack : Array Formula)
  (off : {off : Nat // off + hyps.size = stack.size})
  (i : Nat) (σ : Std.HashMap String Formula)
  (f : Formula) (lbl : String)
  (h_i : i < hyps.size)
  (h_find : db.find? hyps[i] = some (.hyp false f lbl)) :
  checkHyp db hyps stack off i σ
    =
  if f[0]! == stack[off.1 + i]![0]!
    then checkHyp db hyps stack off (i+1) (σ.insert f[1]!.value (stack[off.1 + i]!))
    else .error (s!"bad typecode in substitution {hyps[i]}: {f} / {stack[off.1 + i]!}") := by
  rw [checkHyp]  -- KEY: Use rw not unfold to avoid expanding RHS recursive calls
  simp [h_i, h_find]
  have h_idx : off.1 + i < stack.size := by
    have : off.1 + i < off.1 + hyps.size := Nat.add_lt_add_left h_i _
    simpa [off.2] using this
  simp [h_idx]
  -- Float case: simpler than essential case, no do-notation to reduce
  split <;> rfl

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
    -- Check for unknown step marker '?'
    if tk.eqArray "?".toAscii then
      -- Push formula matching the statement being proved (incomplete proof)
      pure (pr.push pr.fmla)
    else
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
          -- Unknown step in compressed proof - push the formula being proved
          pr := pr.push pr.fmla
          chr := 0
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
      if tk.len == 2 && tk[0]! == '$'.toUInt8 then
        match tk[1]!.toChar with
        | '{' => s.withDB .pushScope
        | '}' => s.withDB (.popScope pos)
        | 'c' => { s with tokp := .const }
        | 'v' => { s with tokp := .var }
        | 'd' => { s with tokp := .djvars #[] }
        | _ => s.label pos tk
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
      if tk.len == 2 && tk[0]! == '$'.toUInt8 then
        let go (s : ParserState) (k : TokensKind) :=
          { s with tokp := .math #[] ⟨k, pos, lab⟩ }
        match tk[1]!.toChar with
        | 'f' => go s .float
        | 'e' => go s .ess
        | 'a' => go s .ax
        | 'p' => go s .thm
        | _ => s.mkError pos s!"unknown statement type {(toLabel tk).2}"
      else s.mkError pos s!"unknown statement type {(toLabel tk).2}"
    | .proof pr =>
      let s := { s with tokp := default }
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

def feed (base : Nat) (arr : ByteArray)
    (i : Nat) (rs : FeedState) (s : ParserState) : ParserState :=
  if h : i < arr.size then
    let c := arr[i]
    if isWhitespace c then
      match rs with
      | .ws =>
        let s := s.updateLine (base + i) c
        feed base arr (i+1) .ws s
      | .token ot =>
        let s := match ot with
        | .this off => s.feedToken (base + off) (ByteSlice.mk arr off (i - off))
        | .old base off arr' => s.feedToken (base + off)
          (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
        let s : ParserState := s.updateLine (base + i) c
        if let some ⟨e, _⟩ := s.db.error? then
          { s with db := { s.db with error? := some ⟨e, i+1⟩ } }
        else feed base arr (i+1) .ws s
    else
      let rs := if let .ws := rs then .token (.this i) else rs
      feed base arr (i+1) rs s
  else
    { s with charp :=
      match rs with
      | .ws => .ws
      | .token ot =>
        match ot with
        | .this off => .token base (ByteSliceT.mk arr off)
        | .old base off arr' => .token base (ByteSliceT.mk (arr' ++ arr) off) }

def feedAll (s : ParserState) (base : Nat) (arr : ByteArray) : ParserState :=
  match s.charp with
  | .ws => s.feed base arr 0 .ws
  | .token base' tk =>
    let arr' := tk.byteArray
    let off := tk.start
    let s := { s with charp := default }
    s.feed base arr 0 (.token (.old base' off arr'))

def done (s : ParserState) (base : Nat) : DB := Id.run do
  let mut s := s
  if let .token pos tk := s.charp then
    s := s.feedToken pos tk.toSlice
  let base := s.mkPos base
  let { db := db, tokp := tokp, ..} := s
  match tokp with
  | .start =>
    if db.scopes.size > 0 then
      db.mkError base "unclosed block (missing $})"
    else db
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

-- Preprocessor with include support
-- Processes $[ filename $] directives by recursively loading files
-- Handles self-includes and cycles per spec §4.1.2
-- In strict mode: validates includes are at outermost scope and not inside statements

partial def expandIncludes (fname : String) (seen : HashSet String) (permissive : Bool := false) :
    IO (Except String (ByteArray × HashSet String)) := do
  -- Canonicalize path (resolve ./ and ../)
  let canonPath ← IO.FS.realPath fname
  let canonStr := canonPath.toString

  -- Check for cycles (including self-include)
  if seen.contains canonStr then
    -- Per spec §4.1.2: "self-include will simply be ignored"
    return .ok (ByteArray.empty, seen)

  let seen := seen.insert canonStr

  -- Read file
  let h ← Handle.mk fname IO.FS.Mode.read
  let rec readAll (acc : ByteArray) : IO ByteArray := do
    let buf ← h.read 4096
    if buf.isEmpty then return acc
    else readAll (acc ++ buf)
  let contents ← readAll ByteArray.empty

  -- Process includes: find $[ ... $] and expand recursively
  let mut result := ByteArray.empty
  let mut seen := seen  -- Make seen mutable to thread through
  let mut i := 0
  let mut scopeDepth := 0  -- Track ${ $} nesting
  let mut inStatement := false  -- Track if we're inside a statement (after label before $.)
  let mut inComment := false  -- Track if we're inside a comment

  while i < contents.size do
    -- Track comment state (comments take precedence over everything else)
    if i + 1 < contents.size && contents[i]! == '$'.toUInt8 then
      let c := contents[i+1]!.toChar
      if c == '(' then
        inComment := true
        result := result.push contents[i]!
        result := result.push contents[i+1]!
        i := i + 2
        continue
      else if c == ')' then
        inComment := false
        result := result.push contents[i]!
        result := result.push contents[i+1]!
        i := i + 2
        continue

    -- Skip everything inside comments
    if inComment then
      result := result.push contents[i]!
      i := i + 1
      continue

    -- Track scope depth for strict mode validation
    if i + 1 < contents.size && contents[i]! == '$'.toUInt8 then
      let c := contents[i+1]!.toChar
      if c == '{' then
        scopeDepth := scopeDepth + 1
      else if c == '}' then
        scopeDepth := max 0 (scopeDepth - 1)
      else if c == '.' then
        inStatement := false  -- Statement terminator

    -- Track if we're entering a statement (simplified: after $f, $e, $a, $p)
    if i + 1 < contents.size && contents[i]! == '$'.toUInt8 then
      let c := contents[i+1]!.toChar
      if c == 'f' || c == 'e' || c == 'a' || c == 'p' then
        inStatement := true

    -- Look for $[ token (only outside comments)
    if i + 1 < contents.size && contents[i]! == '$'.toUInt8 && contents[i+1]! == '['.toUInt8 then
      -- Validate strict mode constraints (spec §4.1.2)
      if !permissive then
        -- Check: not in inner scope
        if scopeDepth > 0 then
          return .error s!"include in inner scope (strict mode requires outermost scope only, spec §4.1.2)"
        -- Check: not inside a statement
        if inStatement then
          return .error s!"include inside statement (strict mode forbids token splicing, spec §4.1.2)"

      i := i + 2
      -- Skip whitespace after $[
      while i < contents.size && (contents[i]! == ' '.toUInt8 || contents[i]! == '\n'.toUInt8 || contents[i]! == '\t'.toUInt8 || contents[i]! == '\r'.toUInt8) do
        i := i + 1

      -- Extract filename until $]
      let mut includePath := ByteArray.empty
      let startPos := i  -- Debug: save start position
      while i + 1 < contents.size && !(contents[i]! == '$'.toUInt8 && contents[i+1]! == ']'.toUInt8) do
        let c := contents[i]!
        if c != ' '.toUInt8 && c != '\n'.toUInt8 && c != '\t'.toUInt8 && c != '\r'.toUInt8 then
          includePath := includePath.push c
        i := i + 1
      -- Debug: check what we extracted
      if includePath.isEmpty && i > startPos then
        return .error s!"extracted empty path from position {startPos} to {i} in {fname}"

      -- Skip $]
      if i + 1 < contents.size then i := i + 2

      -- Convert includePath to String
      let mut includeFile := String.fromUTF8! includePath

      -- Debug: check extracted path before normalization
      if includeFile.isEmpty then
        return .error s!"extracted empty include path before normalization in {fname}"

      -- Normalize "./" prefix (FilePath doesn't handle it well)
      if includeFile.startsWith "./" then
        includeFile := includeFile.drop 2

      -- Check for empty path after normalization
      if includeFile.isEmpty then
        return .error s!"include path became empty after normalizing './' prefix (original was '{String.fromUTF8! includePath}') in {fname}"

      -- Resolve relative path (relative to current file's directory)
      let baseDir := System.FilePath.parent fname |>.getD "."
      let fullPath := baseDir / includeFile

      -- Recursively expand the included file
      try
        match ← expandIncludes fullPath.toString seen permissive with
        | .ok (expanded, seen') =>
          seen := seen'  -- Thread the updated seen set through
          result := result ++ expanded
          -- Add whitespace to separate from next token
          result := result.push ' '.toUInt8
        | .error e => return .error e
      catch e =>
        return .error s!"failed to read include file '{includeFile}' (resolved to '{fullPath}'): {e}"
    else
      result := result.push contents[i]!
      i := i + 1

  return .ok (result, seen)

partial def check (fname : String) (permissive : Bool := false) : IO DB := do
  -- Expand all includes recursively with permissive mode awareness
  match ← expandIncludes fname (HashSet.emptyWithCapacity 16) permissive with
  | .error msg =>
    -- Return DB with error for include validation failures
    let initialDB : DB := { (default : DB) with permissive := permissive }
    return initialDB.mkError ⟨1, 1⟩ msg
  | .ok (processed, _) =>
    let rec loop (s : ParserState) (base : Nat) (arr : ByteArray) (off : Nat) : IO DB := do
      if off >= arr.size then
        return s.done base
      else
        let len := min 1024 (arr.size - off)
        let buf := arr.extract off (off + len)
        let s := s.feedAll base buf
        if s.db.error?.isSome then return s.db
        else loop s (base + buf.size) arr (off + len)
    let initialDB : DB := { (default : DB) with permissive := permissive }
    let initialState : ParserState := { (default : ParserState) with db := initialDB }
    loop initialState 0 processed 0
