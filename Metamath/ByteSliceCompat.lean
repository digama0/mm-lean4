import Batteries.Data.ByteSlice

/-!
# ByteSlice Compatibility Layer

Provides a compatibility layer between the custom ByteSlice implementation
(used in Verify.lean before Lean 4.24.0) and ByteSlice (provided by Std in Lean 4.24.0).

This allows existing code using `tk.len`, `tk.off`, `tk.eqArray`, etc. to work
with the new ByteSlice API without changes to call sites.

Note: ByteSlice is now an abbreviation for `Std.Slice Internal.ByteSliceData`.
The type is already exported from Std, so we only add compatibility methods here.
-/

-- ByteSlice is already available from Std (via Batteries)
-- We just add the old API methods as extensions

namespace ByteSlice

-- Compatibility methods matching the old API
@[inline] def off (s : ByteSlice) : Nat := s.start
@[inline] def len (s : ByteSlice) : Nat := s.size

-- The new ByteSlice already has toByteArray, we can use it directly as toArray
@[inline] def toArray (s : ByteSlice) : ByteArray := s.toByteArray

-- Old eqArray compared the slice contents with a ByteArray
def eqArray (bs : ByteSlice) (arr : ByteArray) : Bool := Id.run do
  if bs.size ≠ arr.size then
    return false
  let mut i := 0
  let mut ok := true
  for b in bs do
    if arr[i]! ≠ b then
      ok := false
      break
    i := i + 1
  return ok

-- Old toString
def toString (bs : ByteSlice) : String := Id.run do
  let mut s := ""
  for c in bs do
    s := s.push (Char.ofUInt8 c)
  s

instance : ToString ByteSlice where
  toString := ByteSlice.toString

end ByteSlice

-- ByteSliceT was just an alias to ByteSlice in the old code
-- Since it's an abbrev, it inherits all methods from ByteSlice automatically
abbrev ByteSliceT := ByteSlice

namespace ByteSliceT

-- toSlice was an identity function in the old code
@[inline] def toSlice (s : ByteSliceT) : ByteSlice := s

-- Helper to construct a ByteSliceT (tail slice) from array and offset
-- The old ByteSliceT had no length field - it went to the end of the array
@[inline] def mk (arr : ByteArray) (off : Nat) : ByteSliceT :=
  arr.toByteSlice off arr.size

end ByteSliceT

-- Old constructors using the public ByteSlice API
@[inline] def ByteArray.toSlice (arr : ByteArray) : ByteSlice :=
  arr.toByteSlice

@[inline] def ByteArray.toSliceT (arr : ByteArray) : ByteSliceT :=
  arr.toByteSlice

-- Helper to construct a ByteSlice from array, offset, and length
-- This mimics the old ⟨arr, off, len⟩ constructor syntax
@[inline] def ByteSlice.mk (arr : ByteArray) (off len : Nat) : ByteSlice :=
  arr.toByteSlice off (off + len)

-- String.toAscii helper (was defined alongside ByteSlice)
def String.toAscii (s : String) : ByteArray :=
  let rec loop (out : ByteArray) (p : Pos) : ByteArray :=
    if h : s.atEnd p then out else
      let c := s.get p
      have := Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (String.lt_next s _)
      loop (out.push c.toUInt8) (s.next p)
  termination_by s.endPos.1 - p.1
  loop ByteArray.empty 0
