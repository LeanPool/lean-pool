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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Carrier
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Runtime

/-!
# Native storage for one-word floating-point formats

The native storage interface represents formats whose complete encoding fits in `UInt64`. It
deliberately excludes refinement proofs so native kernels can depend on the storage operations
without importing theorem developments.

Field masks, the implicit bit, the conventional bias, and the storage mask use `UInt64` shifts.
This avoids computing these constants with arbitrary-precision powers when a descriptor remains
a runtime argument. `Core.Proof` gives their natural-number values under the one-word capacity
bound.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWord

/--
Capacity contract for native decoding of a complete floating-point storage word.

Unlike `Eligible`, this predicate does not constrain arithmetic intermediates. It is suitable for
operations that only decode fields in `UInt64` before entering an exact shared kernel.
-/
def StorageEligible (fmt : FloatFormat) : Prop :=
  fmt.isIEEE = true ∧ fmt.bitWidth ≤ 64

/--
Storage eligibility is decided from the descriptor fields.

The explicit conditional and inline attribute allow a dispatcher specialized to a closed
descriptor to simplify the eligibility check.
-/
@[inline] instance (fmt : FloatFormat) : Decidable (StorageEligible fmt) :=
  if h : fmt.isIEEE = true ∧ fmt.bitWidth ≤ 64 then isTrue h else isFalse h

/--
Conservative capacity contract shared by one-word native kernels.

The IEEE condition selects the existing exact binary semantics. The width bounds ensure storage,
exponent arithmetic, and normalized significands fit in the flat `UInt64` implementations.
-/
def Eligible (fmt : FloatFormat) : Prop :=
  fmt.isIEEE = true ∧
    fmt.bitWidth ≤ 64 ∧
    fmt.expWidth ≤ 30 ∧
    fmt.fracWidth ≤ 30

/-- Kernel eligibility is decided from the descriptor fields; see `StorageEligible`. -/
@[inline] instance (fmt : FloatFormat) : Decidable (Eligible fmt) :=
  if h : fmt.isIEEE = true ∧ fmt.bitWidth ≤ 64 ∧ fmt.expWidth ≤ 30 ∧ fmt.fracWidth ≤ 30 then
    isTrue h
  else
    isFalse h

/-- Convert the carrier to a native word, preserving its value when `fmt.bitWidth ≤ 64`. -/
@[inline] def toWord {fmt : FloatFormat} (x : Model fmt) : UInt64 :=
  UInt64.ofNat x.toNatBits

/--
Mask of the complete storage word: `2 ^ bitWidth - 1` for formats below 64 bits and all ones at
64 bits or more.
-/
@[inline] def storageMask (fmt : FloatFormat) : UInt64 :=
  if fmt.bitWidth < 64 then
    ((1 : UInt64) <<< UInt64.ofNat fmt.bitWidth) - 1
  else
    0xffffffffffffffff

/--
The storage mask lies below the format's radix.

This bound lets `ofWord` build its exact-width model word with `BitVec.ofNatLT`, so the
conversion performs no modular reduction and no power computation at runtime.
-/
theorem storageMask_toNat_lt (fmt : FloatFormat) :
    (storageMask fmt).toNat < 2 ^ fmt.bitWidth := by
  unfold storageMask
  split
  · rename_i hlt
    have hsize : fmt.bitWidth < 2 ^ 64 := lt_trans hlt (by decide)
    have hpow : 2 ^ fmt.bitWidth < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hlt
    have hshift : ((1 : UInt64) <<< UInt64.ofNat fmt.bitWidth).toNat = 2 ^ fmt.bitWidth := by
      rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', UInt64.toNat_one, Nat.mod_eq_of_lt hsize,
        Nat.mod_eq_of_lt hlt, Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt hpow]
    rw [UInt64.toNat_sub_of_le, hshift, UInt64.toNat_one]
    · exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos
    · rw [UInt64.le_iff_toNat_le, hshift, UInt64.toNat_one]
      exact Nat.one_le_two_pow
  · rename_i hge
    have hbound : (0xffffffffffffffff : UInt64).toNat < 2 ^ 64 := by decide
    exact lt_of_lt_of_le hbound (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hge))

/--
Truncate one native word into an exact-width floating-point carrier.

The low `fmt.bitWidth` bits are kept by `storageMask`, and the model word is built with
`BitVec.ofNatLT` from `storageMask_toNat_lt`. The executable body masks the word and converts it
to `Nat`; the power in its bound belongs to the erased proof. `Core.Proof` shows the value is
`bits.toNat % 2 ^ fmt.bitWidth`.
-/
@[inline] def ofWord {fmt : FloatFormat} (bits : UInt64) : Model fmt :=
  Model.ofBits <|
    BitVec.ofNatLT (bits &&& storageMask fmt).toNat
      (lt_of_le_of_lt
        (by rw [UInt64.toNat_and]; exact Nat.and_le_right)
        (storageMask_toNat_lt fmt))

/--
The conventional IEEE bias `2 ^ (expWidth - 1) - 1` as one machine word.

It is exact for every format that fits one word; `Core.Proof` proves `biasWord_toNat`.
-/
@[inline] def biasWord (fmt : FloatFormat) : UInt64 :=
  ((1 : UInt64) <<< (UInt64.ofNat fmt.expWidth - 1)) - 1

/--
The conventional IEEE bias as an integer, read from `biasWord`.

Division compares its unbiased exponent with `1 - biasInt fmt` and `biasInt fmt`, which are the
conventional IEEE normal exponent bounds `ieeeMinNormalExponent` and `ieeeMaxNormalExponent`, and
adds `biasInt fmt` to encode the result; `Core.Proof` proves `biasInt_eq`.
-/
@[inline] def biasInt (fmt : FloatFormat) : Int :=
  Int.ofNat (biasWord fmt).toNat

/-- One-word mask for the stored exponent field, `2 ^ expWidth - 1`, computed by one shift. -/
@[inline] def exponentMask (fmt : FloatFormat) : UInt64 :=
  ((1 : UInt64) <<< UInt64.ofNat fmt.expWidth) - 1

/-- One-word mask for the stored fraction field, `2 ^ fracWidth - 1`, computed by one shift. -/
@[inline] def fractionMask (fmt : FloatFormat) : UInt64 :=
  ((1 : UInt64) <<< UInt64.ofNat fmt.fracWidth) - 1

/-- Extract the biased exponent using native shifts and masks. -/
@[inline] def exponentField (fmt : FloatFormat) (bits : UInt64) : UInt64 :=
  (bits >>> UInt64.ofNat fmt.fracWidth) &&& exponentMask fmt

/-- Extract the explicit fraction using one native mask. -/
@[inline] def fractionField (fmt : FloatFormat) (bits : UInt64) : UInt64 :=
  bits &&& fractionMask fmt

/-- Read the stored sign bit from a one-word carrier with a machine-word bit test. -/
@[inline] def signField (fmt : FloatFormat) (bits : UInt64) : Bool :=
  FloatLib.Numerics.FixedWord.bitAtWord bits (UInt64.ofNat (fmt.expWidth + fmt.fracWidth))

/-- Pack native sign, exponent, and fraction fields, masking each field to the descriptor width. -/
@[inline] def packFields (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : UInt64) : UInt64 :=
  (if sign then
      (1 : UInt64) <<< UInt64.ofNat (fmt.expWidth + fmt.fracWidth)
    else
      0) |||
    ((exponent &&& exponentMask fmt) <<< UInt64.ofNat fmt.fracWidth) |||
    (fraction &&& fractionMask fmt)

/-- The implicit leading significand bit in one native word. -/
@[inline] def hiddenBit (fmt : FloatFormat) : UInt64 :=
  (1 : UInt64) <<< UInt64.ofNat fmt.fracWidth

/-- Twice the implicit leading significand bit, used to detect rounding carry. -/
@[inline] def carryBit (fmt : FloatFormat) : UInt64 :=
  (1 : UInt64) <<< UInt64.ofNat (fmt.fracWidth + 1)

/--
Decode two normal finite operands and pass their native fields to a multiplicative kernel.

The callback receives the XOR of the operand signs, followed by both biased exponents and both
normalized significands. Zero, subnormal, and exceptional operands return `none`.
-/
@[always_inline, inline] def withNormalPairOption {fmt : FloatFormat} {α : Type}
    (x y : Model fmt)
    (kernel : Bool → UInt64 → UInt64 → UInt64 → UInt64 → Option α) :
    Option α :=
  let xBits := toWord x
  let yBits := toWord y
  let xExponent := exponentField fmt xBits
  let yExponent := exponentField fmt yBits
  let allOnes := exponentMask fmt
  if xExponent == 0 || xExponent == allOnes ||
      yExponent == 0 || yExponent == allOnes then
    none
  else
    kernel
      (Bool.xor (signField fmt xBits) (signField fmt yBits))
      xExponent yExponent
      (fractionField fmt xBits ||| hiddenBit fmt)
      (fractionField fmt yBits ||| hiddenBit fmt)

end Model.NativeSmallWord
end FloatLib.Floats.Formats.BinaryInterchange
