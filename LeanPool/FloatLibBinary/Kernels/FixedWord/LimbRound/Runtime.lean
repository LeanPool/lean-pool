/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
Upstream FloatLib code retains its MIT license below. The Lean Pool integration changes are
covered by the standard header above.

MIT License

Copyright (c) 2026 FloatLib

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.FloatLibBinary.Kernels.FixedWord.Product.Runtime

/-!
# Fixed-limb rounding

Two- and four-limb shifts and nearest-even rounding, with guard, sticky, and carry results.
Fixed tuples give these small kernels a statically sized representation. Callers handle exponents
and packing; `LimbRound.Proof` relates the operations to natural-number arithmetic.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

/-- Increment modulo `2^128`, propagating the low-word carry. -/
@[inline] def UInt128.increment (value : UInt128) : UInt128 :=
  let sum := add64 value.lo 1
  ⟨value.hi + sum.carry, sum.value⟩

/-- Set the least-significant bit of a two-limb value. -/
@[inline] def UInt128.setLowBit (value : UInt128) : UInt128 :=
  ⟨value.hi, value.lo ||| 1⟩

namespace UInt128

/-- Shift a two-word value right by one bit. -/
@[inline] def shiftRightOne (value : UInt128) : UInt128 :=
  {
    hi := value.hi >>> 1
    lo := (value.lo >>> 1) ||| ((value.hi &&& 1) <<< 63)
  }

/--
Round a two-word value right by one bit using round-to-nearest, ties-to-even.

For a one-bit shift, incrementing is required exactly when the two low input bits are `11`.
-/
@[inline] def roundShiftRightOneEven (value : UInt128) : UInt128 :=
  let quotient := value.shiftRightOne
  if (value.lo &&& 3) == 3 then
    quotient.increment
  else
    quotient

/-- Low 64 bits of a right shift by an amount strictly between zero and 64. -/
@[inline] def shiftRightLow (value : UInt128) (shift : Nat) : UInt64 :=
  (value.lo >>> UInt64.ofNat shift) |||
    (value.hi <<< UInt64.ofNat (64 - shift))

/--
Round a two-limb value right by `shift`, returning a single native word.

The kernel is meaningful for `0 < shift < 64` with `value.hi < 2^shift`, so that the quotient
fits one word, and callers also keep the incremented quotient below `2^64`.
`roundShiftRightEven_toNat` states these hypotheses.
-/
@[inline] def roundShiftRightEven (value : UInt128) (shift : Nat) : UInt64 :=
  let quotient := shiftRightLow value shift
  let remainder := value.lo &&& ((1 <<< UInt64.ofNat shift) - 1)
  let half := (1 : UInt64) <<< UInt64.ofNat (shift - 1)
  if remainder < half then
    quotient
  else if remainder > half then
    quotient + 1
  else if (quotient &&& 1) == 0 then
    quotient
  else
    quotient + 1

end UInt128

namespace UInt256

/--
Low 128 bits of a four-word right shift.

The operation is total: shifts at and beyond 256 return zero. Callers that need the complete
quotient establish separately that no nonzero bit remains above the returned two-word window.
The explicit limb ranges avoid the modulo reduction performed by native machine-word shifts.
-/
@[inline] def shiftRight128 (value : UInt256) (shift : Nat) : UInt128 :=
  if shift == 0 then
    ⟨value.limb1, value.limb0⟩
  else if shift < 64 then
    let complement := 64 - shift
    {
      hi := (value.limb1 >>> UInt64.ofNat shift) |||
        (value.limb2 <<< UInt64.ofNat complement)
      lo := (value.limb0 >>> UInt64.ofNat shift) |||
        (value.limb1 <<< UInt64.ofNat complement)
    }
  else if shift == 64 then
    ⟨value.limb2, value.limb1⟩
  else if shift < 128 then
    let inner := shift - 64
    let complement := 64 - inner
    {
      hi := (value.limb2 >>> UInt64.ofNat inner) |||
        (value.limb3 <<< UInt64.ofNat complement)
      lo := (value.limb1 >>> UInt64.ofNat inner) |||
        (value.limb2 <<< UInt64.ofNat complement)
    }
  else if shift == 128 then
    ⟨value.limb3, value.limb2⟩
  else if shift < 192 then
    let inner := shift - 128
    let complement := 64 - inner
    {
      hi := value.limb3 >>> UInt64.ofNat inner
      lo := (value.limb2 >>> UInt64.ofNat inner) |||
        (value.limb3 <<< UInt64.ofNat complement)
    }
  else if shift < 256 then
    ⟨0, value.limb3 >>> UInt64.ofNat (shift - 192)⟩
  else
    ⟨0, 0⟩

/-- Test whether any of the lowest `width` bits of a four-word value is nonzero. -/
@[inline] def hasNonzeroBelow (value : UInt256) (width : Nat) : Bool :=
  if width == 0 then
    false
  else if width < 64 then
    (value.limb0 &&& ((1 <<< UInt64.ofNat width) - 1)) != 0
  else if width == 64 then
    value.limb0 != 0
  else if width < 128 then
    let inner := width - 64
    value.limb0 != 0 ||
      (value.limb1 &&& ((1 <<< UInt64.ofNat inner) - 1)) != 0
  else if width == 128 then
    value.limb0 != 0 || value.limb1 != 0
  else if width < 192 then
    let inner := width - 128
    value.limb0 != 0 || value.limb1 != 0 ||
      (value.limb2 &&& ((1 <<< UInt64.ofNat inner) - 1)) != 0
  else if width == 192 then
    value.limb0 != 0 || value.limb1 != 0 || value.limb2 != 0
  else if width < 256 then
    let inner := width - 192
    value.limb0 != 0 || value.limb1 != 0 || value.limb2 != 0 ||
      (value.limb3 &&& ((1 <<< UInt64.ofNat inner) - 1)) != 0
  else
    value.limb0 != 0 || value.limb1 != 0 ||
      value.limb2 != 0 || value.limb3 != 0

/--
Shift right into two words, setting the low bit if any bit below the shift position is nonzero.

When the shifted quotient fits in two words, this is round-to-odd, or sticky, normalization.
It preserves nearest-even rounding when the final rounder discards at least two more bits.
-/
@[inline] def shiftRightJam128
    (value : UInt256) (shift : Nat) : UInt128 :=
  let shifted := shiftRight128 value shift
  if hasNonzeroBelow value shift then
    shifted.setLowBit
  else
    shifted

/--
Number of low bits discarded when reducing a four-limb value to a normalized two-limb value.

Values already fitting below bit 128 use a zero shift. Wider values retain their leading bit at
position 127, independently of the arithmetic operation that produced them.
-/
@[inline] def normalizationShift128 (value : UInt256) : Nat :=
  value.log2 - 127

/--
Normalize a four-limb value into two limbs while jamming every discarded one bit into bit zero.

The result retains the leading 128-bit window, with its low bit ORed with the sticky bit of the
discarded suffix. This preserves nearest-even rounding when the final rounder discards at least
two more bits.
-/
@[inline] def normalizeJam128 (value : UInt256) : UInt128 :=
  shiftRightJam128 value value.normalizationShift128

/--
Round a four-limb value right by `shift`, returning a two-limb result.

The kernel is only valid for `64 < shift < 128`: the discarded field is read from `limb1` and
`limb0`, and the halfway marker is built inside `limb1`. Callers also keep
`value.limb3 < 2^(shift - 64)` and the incremented quotient below `2^128`, so that
`shiftRight128` returns the complete quotient. `roundShiftRightEven128_toNat` states exactly
these hypotheses. Two-word products call this with shifts `fracWidth` or `fracWidth + 1`, which
is 112 or 113 for binary128.
-/
@[inline] def roundShiftRightEven128 (value : UInt256) (shift : Nat) : UInt128 :=
  let inner := shift - 64
  let quotient := shiftRight128 value shift
  let highRemainder :=
    value.limb1 &&& ((1 <<< UInt64.ofNat inner) - 1)
  let halfHigh := (1 : UInt64) <<< UInt64.ofNat (inner - 1)
  if highRemainder < halfHigh then
    quotient
  else if highRemainder > halfHigh || value.limb0 != 0 then
    quotient.increment
  else if (quotient.lo &&& 1) == 0 then
    quotient
  else
    quotient.increment

end UInt256

end FloatLib.Numerics.FixedWord
