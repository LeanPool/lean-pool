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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Format.Catalog
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Carrier
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Runtime

/-!
# Two-word pair-kernel storage runtime

The structural eligibility predicate and field helpers provide the storage interface shared by
the fixed-limb arithmetic kernels. A value of an eligible format is split into a high and a low
`UInt64`. The low word is entirely fraction; the high word holds the remaining `fracWidth - 64`
fraction bits, then the exponent field, then the sign. Every field position is derived from the
descriptor, so one kernel serves every eligible layout, with 68 to 128 encoded bits and a
fraction wider than one word. The correspondence with the width-generic carrier is proved in
`Core.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

/--
Structural capability required by the two-word kernels.

The conventional IEEE encoding selects the exact binary semantics shared with the generic
kernels, and in particular the default bias. `64 < fracWidth` places the sign, the exponent
field, and the upper fraction bits in the high word and fills the low word with fraction bits.
Only the fraction spans both words; the exponent and sign are contained in the high word. The
fraction-width bound also keeps every four-limb product-rounding shift strictly above one word.
`bitWidth ≤ 128` bounds the storage to two words. Layouts whose fraction has at most 64 bits are
outside this capability.
-/
def Eligible (fmt : FloatFormat) : Prop :=
  fmt.isIEEE = true ∧ 64 < fmt.fracWidth ∧ fmt.bitWidth ≤ 128

/--
Decide eligibility from the descriptor fields.

The explicit conditional and `@[inline]` annotation expose the decision to simplification at
closed-format call sites.
-/
@[inline] instance (fmt : FloatFormat) : Decidable (Eligible fmt) :=
  if h : fmt.isIEEE = true ∧ 64 < fmt.fracWidth ∧ fmt.bitWidth ≤ 128 then isTrue h else isFalse h

/-- Number of fraction bits stored in the high word. -/
@[inline] def fracHighWidth (fmt : FloatFormat) : UInt64 :=
  UInt64.ofNat (fmt.fracWidth - 64)

/-- Mask selecting the fraction bits stored in the high word. -/
@[inline] def fracHighMask (fmt : FloatFormat) : UInt64 :=
  ((1 : UInt64) <<< fracHighWidth fmt) - 1

/-- The all-ones exponent field as a native word. -/
@[inline] def expAllOnes (fmt : FloatFormat) : UInt64 :=
  ((1 : UInt64) <<< UInt64.ofNat fmt.expWidth) - 1

/-- The implicit leading significand bit `2^fracWidth`, in high-word coordinates. -/
@[inline] def implicitBit (fmt : FloatFormat) : UInt64 :=
  (1 : UInt64) <<< fracHighWidth fmt

/-- The sign bit `2^(expWidth + fracWidth)`, in high-word coordinates. -/
@[inline] def signMask (fmt : FloatFormat) : UInt64 :=
  (1 : UInt64) <<< UInt64.ofNat (fmt.expWidth + fmt.fracWidth - 64)

/-- Split a stored value into its high and low native words. -/
@[inline] def toWords {fmt : FloatFormat} (x : Model fmt) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  {
    hi := UInt64.ofBitVec (x.bits.extractLsb' 64 64)
    lo := UInt64.ofBitVec (x.bits.extractLsb' 0 64)
  }

/-- Join two native words into a stored value, keeping the low `bitWidth` bits. -/
@[inline] def ofWords (fmt : FloatFormat)
    (words : FloatLib.Numerics.FixedWord.UInt128) : Model fmt :=
  Model.ofBits ((words.hi.toBitVec ++ words.lo.toBitVec).setWidth fmt.bitWidth)

/-- Extract the sign from the high storage word. -/
@[inline] def signBit (fmt : FloatFormat) (high : UInt64) : Bool :=
  (high &&& signMask fmt) != 0

/-- Extract the biased exponent field from the high storage word. -/
@[inline] def expField (fmt : FloatFormat) (high : UInt64) : UInt64 :=
  (high >>> fracHighWidth fmt) &&& expAllOnes fmt

/-- Extract the fraction bits held in the high storage word. -/
@[inline] def fracHigh (fmt : FloatFormat) (high : UInt64) : UInt64 :=
  high &&& fracHighMask fmt

/-- Add the implicit bit to the two fraction limbs of a normal value. -/
@[inline] def normalMantissa (fmt : FloatFormat) (high low : UInt64) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  ⟨high ||| implicitBit fmt, low⟩

/-- The two-limb significand `2^fracWidth`, the smallest normal significand. -/
@[inline] def implicitMantissa (fmt : FloatFormat) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  ⟨implicitBit fmt, 0⟩

/-- The two-limb value `2^(fracWidth + 1)` produced when nearest-even rounding carries out. -/
@[inline] def carryMantissa (fmt : FloatFormat) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  ⟨implicitBit fmt <<< 1, 0⟩

/-- Whether a rounded two-limb significand carried out to `2^(fracWidth + 1)`. -/
@[inline] def isCarry (fmt : FloatFormat)
    (rounded : FloatLib.Numerics.FixedWord.UInt128) : Bool :=
  rounded.hi == implicitBit fmt <<< 1 && rounded.lo == 0

/-- Replace a carried-out significand by `2^fracWidth`, leaving other significands unchanged. -/
@[inline] def normalizeCarry (fmt : FloatFormat) (carry : Bool)
    (rounded : FloatLib.Numerics.FixedWord.UInt128) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  if carry then implicitMantissa fmt else rounded

/--
Pack a finite normal result directly from its native exponent and significand words.

The exponent is masked to the exponent field, and the significand's implicit bit is discarded by
the high fraction mask. The result is meaningful when the exponent fits the field and the
significand is normal; `Core.Proof.packNormal_eq_ofFields` states that contract.
-/
@[inline] def packNormal (fmt : FloatFormat)
    (sign : Bool) (exponent : UInt64)
    (mantissa : FloatLib.Numerics.FixedWord.UInt128) : Model fmt :=
  let high :=
    (if sign then signMask fmt else 0) |||
      ((exponent &&& expAllOnes fmt) <<< fracHighWidth fmt) |||
      (mantissa.hi &&& fracHighMask fmt)
  ofWords fmt { hi := high, lo := mantissa.lo }

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
