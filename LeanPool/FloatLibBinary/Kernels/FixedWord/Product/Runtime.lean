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

public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Runtime

/-!
# Fixed-limb product runtime

Carry-preserving addition and full products operate over one, two, and four native limbs. The
explicit `UInt256` carrier is large enough for the exact product of two `UInt128` values, so the
product needs no arbitrary-precision conversion.

`Product.Proof` shows that each returned value and carry reconstruct the exact natural-number
sum or product.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

universe u

/-- A fixed-width addition result together with its unsigned carry. -/
structure AddResult (α : Type u) where
  /-- Low fixed-width part of the exact sum. -/
  value : α
  /-- Carry above the payload's highest bit, represented as a native word. -/
  carry : UInt64
  deriving DecidableEq, Repr

/-- Add two native words and retain the unsigned carry. -/
@[inline] def add64 (x y : UInt64) : AddResult UInt64 :=
  let lo := x + y
  ⟨lo, if lo < x then 1 else 0⟩

/-- Add two words and an incoming carry. -/
@[inline] def addCarry64 (x y carry : UInt64) : AddResult UInt64 :=
  let first := add64 x y
  let second := add64 first.value carry
  ⟨second.value, first.carry + second.carry⟩

/-- Add two two-word values. -/
@[inline] def add128 (x y : UInt128) : AddResult UInt128 :=
  let low := addCarry64 x.lo y.lo 0
  let high := addCarry64 x.hi y.hi low.carry
  ⟨⟨high.value, low.value⟩, high.carry⟩

/-- A 256-bit unsigned value represented by four native 64-bit limbs. -/
structure UInt256 where
  /-- Bits 192 through 255. -/
  limb3 : UInt64
  /-- Bits 128 through 191. -/
  limb2 : UInt64
  /-- Bits 64 through 127. -/
  limb1 : UInt64
  /-- Bits 0 through 63. -/
  limb0 : UInt64
  deriving DecidableEq, Repr

namespace UInt256

/-- Embed a two-limb unsigned value in the low half of a four-limb carrier. -/
@[inline] def ofUInt128 (value : UInt128) : UInt256 :=
  ⟨0, 0, value.hi, value.lo⟩

/--
Embed a two-limb value after shifting it left by `shift` bits, for `64 < shift < 128`.

The two-word kernels for formats of at most 128 bits align a `fracWidth + 1`-bit significand by
`fracWidth` or `fracWidth + 1` places, so division, fused multiply-add, and square root share this
one word shuffle. `toNat_ofUInt128ShiftedLeft` gives its value under the stated shift bounds;
outside them the native shift counts wrap and the result is unspecified.
-/
@[inline] def ofUInt128ShiftedLeft (value : UInt128) (shift : Nat) : UInt256 :=
  let inner := shift - 64
  let complement := 64 - inner
  {
    limb3 := value.hi >>> UInt64.ofNat complement
    limb2 := (value.hi <<< UInt64.ofNat inner) ||| (value.lo >>> UInt64.ofNat complement)
    limb1 := value.lo <<< UInt64.ofNat inner
    limb0 := 0
  }

/-- Return the low two limbs of a four-limb unsigned value. -/
@[inline] def low128 (value : UInt256) : UInt128 :=
  ⟨value.limb1, value.limb0⟩

/-- Mathematical value of a four-limb unsigned integer. -/
def toNat (value : UInt256) : Nat :=
  value.limb0.toNat +
    value.limb1.toNat * 2 ^ 64 +
    value.limb2.toNat * 2 ^ 128 +
    value.limb3.toNat * 2 ^ 192

/-- Position of the most significant set bit, with zero mapped to zero. -/
@[inline] def log2 (value : UInt256) : Nat :=
  if value.limb3 != 0 then
    192 + value.limb3.log2.toNat
  else if value.limb2 != 0 then
    128 + value.limb2.log2.toNat
  else if value.limb1 != 0 then
    64 + value.limb1.log2.toNat
  else
    value.limb0.log2.toNat

end UInt256

/-- Add two four-word values. -/
@[inline] def add256 (x y : UInt256) : AddResult UInt256 :=
  let limb0 := addCarry64 x.limb0 y.limb0 0
  let limb1 := addCarry64 x.limb1 y.limb1 limb0.carry
  let limb2 := addCarry64 x.limb2 y.limb2 limb1.carry
  let limb3 := addCarry64 x.limb3 y.limb3 limb2.carry
  ⟨⟨limb3.value, limb2.value, limb1.value, limb0.value⟩, limb3.carry⟩

/--
Exact native multiplication of two two-limb values.

Four `mul64` products form the schoolbook product. Each output column is reduced with `add64`, and
the resulting carry count is passed to the next column.
-/
@[inline] def mul128 (x y : UInt128) : UInt256 :=
  let p00 := mul64 x.lo y.lo
  let p01 := mul64 x.lo y.hi
  let p10 := mul64 x.hi y.lo
  let p11 := mul64 x.hi y.hi
  let first1 := add64 p00.hi p01.lo
  let second1 := add64 first1.value p10.lo
  let carry1 := first1.carry + second1.carry
  let first2 := add64 p01.hi p10.hi
  let second2 := add64 first2.value p11.lo
  let third2 := add64 second2.value carry1
  let carry2 := first2.carry + second2.carry + third2.carry
  ⟨p11.hi + carry2, third2.value, second1.value, p00.lo⟩

end FloatLib.Numerics.FixedWord
