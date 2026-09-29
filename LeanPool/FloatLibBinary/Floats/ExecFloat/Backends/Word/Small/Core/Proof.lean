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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Core.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Fields.Optimized
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.Lean
import Mathlib.Tactic.NormNum

/-!
# Correctness of native storage for one-word floating-point formats

The executable representation boundary lives in `Core.Runtime`. Its word conversions, field
operations, and packing are proved against the exact-width carrier under the actual capacity
requirements. The result therefore applies to every configured binary format that fits one
machine word rather than to a list of familiar IEEE widths.

Later arithmetic proofs reuse this boundary instead of repeating masking and truncation arguments
for each operation. The descriptor constants of `Core.Runtime` are machine words computed by
shifts; `exponentMask_toNat`, `fractionMask_toNat`, `biasWord_toNat`, and the threshold lemmas at
the end of this module give their natural-number values under the one-word capacity bound.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWord

/-- The native word has the same natural-number value as a carrier that fits in one word. -/
@[simp, grind =] theorem toWord_toNat {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64)
    (x : Model fmt) :
    (toWord x).toNat = x.toNatBits := by
  unfold toWord
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
  exact x.bits.toFin.isLt.trans_le <|
    Nat.pow_le_pow_right (by decide) hwidth

/-- Masking with the storage mask reduces a native word modulo the format's radix. -/
theorem and_storageMask_toNat {fmt : FloatFormat} (bits : UInt64) :
    (bits &&& storageMask fmt).toNat = bits.toNat % 2 ^ fmt.bitWidth := by
  rw [UInt64.toNat_and]
  unfold storageMask
  split
  · rename_i hlt
    have hshift := FloatLib.Numerics.FixedWord.uint64_powTwo_toNat fmt.bitWidth hlt
    rw [UInt64.toNat_sub_of_le, hshift, UInt64.toNat_one, Nat.and_two_pow_sub_one_eq_mod]
    rw [UInt64.le_iff_toNat_le, hshift, UInt64.toNat_one]
    exact Nat.one_le_two_pow
  · rename_i hge
    have hmask : (0xffffffffffffffff : UInt64).toNat = 2 ^ 64 - 1 := by decide
    have hbits : bits.toNat < 2 ^ 64 := UInt64.toNat_lt_size bits
    rw [hmask, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hbits, Nat.mod_eq_of_lt]
    exact hbits.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hge))

/-- Truncating a native word has the expected exact-width natural-number value. -/
@[simp, grind =] theorem toNatBits_ofWord {fmt : FloatFormat} (bits : UInt64) :
    (ofWord (fmt := fmt) bits).toNatBits =
      bits.toNat % 2 ^ fmt.bitWidth := by
  change (BitVec.ofNatLT (bits &&& storageMask fmt).toNat _).toNat =
    bits.toNat % 2 ^ fmt.bitWidth
  rw [BitVec.toNat_ofNatLT, and_storageMask_toNat]

/-- Zero-extension followed by exact-width truncation is identity for a one-word format. -/
@[simp] theorem ofWord_toWord {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64)
    (x : Model fmt) :
    ofWord (toWord x) = x := by
  cases x with
  | mk bits =>
      apply congrArg Model.ofBits
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNatLT, and_storageMask_toNat, toWord_toNat hwidth]
      exact Nat.mod_eq_of_lt bits.toFin.isLt

private theorem fracWidth_lt_64 (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64) :
    fmt.fracWidth < 64 := by
  unfold FloatFormat.bitWidth at hwidth
  omega

private theorem fieldWidth_lt_64 (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64) :
    fmt.expWidth + fmt.fracWidth < 64 := by
  unfold FloatFormat.bitWidth at hwidth
  omega

private theorem expMask_lt_field (fmt : FloatFormat) :
    fmt.expAllOnesNat < 2 ^ fmt.expWidth := by
  unfold FloatFormat.expAllOnesNat
  have hpositive : 0 < 2 ^ fmt.expWidth := Nat.two_pow_pos _
  omega

private theorem fracMask_lt_field (fmt : FloatFormat) :
    fmt.fracMaskNat < 2 ^ fmt.fracWidth := by
  unfold FloatFormat.fracMaskNat
  have hpositive : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  omega

/-- Natural-number value of the native exponent mask for a one-word format. -/
theorem exponentMask_toNat {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) :
    (exponentMask fmt).toNat = fmt.expAllOnesNat := by
  have hexp : fmt.expWidth < 64 := by
    unfold FloatFormat.bitWidth at hwidth
    omega
  have hshift := FloatLib.Numerics.FixedWord.uint64_powTwo_toNat fmt.expWidth hexp
  unfold exponentMask FloatFormat.expAllOnesNat
  rw [UInt64.toNat_sub_of_le, hshift, UInt64.toNat_one]
  rw [UInt64.le_iff_toNat_le, hshift, UInt64.toNat_one]
  exact Nat.one_le_two_pow

/-- Natural-number value of the native fraction mask for a one-word format. -/
theorem fractionMask_toNat {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) :
    (fractionMask fmt).toNat = fmt.fracMaskNat := by
  have hfrac : fmt.fracWidth < 64 := fracWidth_lt_64 fmt hwidth
  have hshift := FloatLib.Numerics.FixedWord.uint64_powTwo_toNat fmt.fracWidth hfrac
  unfold fractionMask FloatFormat.fracMaskNat
  rw [UInt64.toNat_sub_of_le, hshift, UInt64.toNat_one]
  rw [UInt64.le_iff_toNat_le, hshift, UInt64.toNat_one]
  exact Nat.one_le_two_pow

/-- The machine-word bias is the conventional bias for every format that fits one word. -/
theorem biasWord_toNat {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) :
    (biasWord fmt).toNat = fmt.bias := by
  have hexp : fmt.expWidth < 64 := by
    unfold FloatFormat.bitWidth at hwidth
    omega
  have hexpTwo : 2 ≤ fmt.expWidth := fmt.expWidth_ge_two
  have hexpWord : (UInt64.ofNat fmt.expWidth).toNat = fmt.expWidth := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (lt_trans hexp (by norm_num))]
  have hone : (1 : UInt64) ≤ UInt64.ofNat fmt.expWidth := by
    rw [UInt64.le_iff_toNat_le, hexpWord, UInt64.toNat_one]
    omega
  have hsub : UInt64.ofNat fmt.expWidth - 1 = UInt64.ofNat (fmt.expWidth - 1) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ hone, hexpWord, UInt64.toNat_one, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (lt_trans (by omega : fmt.expWidth - 1 < 64) (by norm_num))]
  have hshift :=
    FloatLib.Numerics.FixedWord.uint64_powTwo_toNat (fmt.expWidth - 1) (by omega)
  unfold biasWord FloatFormat.bias
  rw [hsub, UInt64.toNat_sub_of_le, hshift, UInt64.toNat_one]
  rw [UInt64.le_iff_toNat_le, hshift, UInt64.toNat_one]
  exact Nat.one_le_two_pow

/-- The integer bias is the conventional bias for every format that fits one word. -/
theorem biasInt_eq {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    biasInt fmt = Int.ofNat fmt.bias := by
  unfold biasInt
  rw [biasWord_toNat hwidth]

/-- Native exponent extraction has the same value as the canonical field decoder. -/
theorem exponentField_toNat {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (x : Model fmt) :
    (exponentField fmt (toWord x)).toNat = Model.expField x := by
  rw [Model.expField_eq_expFieldImpl_apply]
  unfold exponentField Model.expFieldImpl
  rw [UInt64.toNat_and,
    FloatLib.Numerics.FixedWord.shiftRight_toNat _ _ (fracWidth_lt_64 fmt hwidth),
    toWord_toNat hwidth, exponentMask_toNat hwidth]

/--
Bounds for a nonzero exponent extracted through the one-word representation.

Arithmetic kernels commonly establish nonzeroness while rejecting zero and subnormal operands.
This lemma supplies the remaining format-width bound without making each kernel repeat the bridge
from `UInt64` fields to `Model.expField`.
-/
theorem exponentField_bounds_of_ne_zero {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (x : Model fmt)
    (hnonzero : exponentField fmt (toWord x) ≠ 0) :
    0 < (exponentField fmt (toWord x)).toNat ∧
      (exponentField fmt (toWord x)).toNat < 2 ^ fmt.expWidth := by
  constructor
  · apply Nat.pos_of_ne_zero
    intro h
    apply hnonzero
    apply UInt64.toNat_inj.mp
    simpa using h
  · rw [exponentField_toNat hwidth x]
    exact Model.expField_lt_pow2 x

/-- Native fraction extraction has the same value as the canonical field decoder. -/
theorem fractionField_toNat {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (x : Model fmt) :
    (fractionField fmt (toWord x)).toNat = Model.fracField x := by
  rw [Model.fracField_eq_fracFieldImpl_apply]
  unfold fractionField Model.fracFieldImpl
  rw [UInt64.toNat_and, fractionMask_toNat hwidth, toWord_toNat hwidth]

/-- Natural-number value of the implicit leading bit for a small one-word format. -/
theorem hiddenBit_toNat (fmt : FloatFormat) (hfracWidth : fmt.fracWidth ≤ 30) :
    (hiddenBit fmt).toNat = 2 ^ fmt.fracWidth := by
  unfold hiddenBit
  exact FloatLib.Numerics.FixedWord.uint64_powTwo_toNat _ (by omega)

/-- Natural-number value of the implicit bit for any format that fits in one storage word. -/
theorem hiddenBit_toNat_of_width (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64) :
    (hiddenBit fmt).toNat = 2 ^ fmt.fracWidth := by
  unfold hiddenBit
  exact FloatLib.Numerics.FixedWord.uint64_powTwo_toNat _ (fracWidth_lt_64 fmt hwidth)

/-- Natural-number value of the rounding carry bit for a small one-word format. -/
theorem carryBit_toNat (fmt : FloatFormat) (hfracWidth : fmt.fracWidth ≤ 30) :
    (carryBit fmt).toNat = 2 ^ (fmt.fracWidth + 1) := by
  unfold carryBit
  exact FloatLib.Numerics.FixedWord.uint64_powTwo_toNat _ (by omega)

/-- Natural-number value of the rounding carry bit for any format whose carry bit fits one word. -/
theorem carryBit_toNat_of_width (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64) (hfracWidth : fmt.fracWidth ≤ 62) :
    (carryBit fmt).toNat = 2 ^ (fmt.fracWidth + 1) := by
  have _ := fracWidth_lt_64 fmt hwidth
  unfold carryBit
  exact FloatLib.Numerics.FixedWord.uint64_powTwo_toNat _ (by omega)

/-- Natural-number value of a decoded normal significand. -/
theorem normalMantissa_toNat {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (hfracWidth : fmt.fracWidth ≤ 30)
    (x : Model fmt) :
    (fractionField fmt (toWord x) ||| hiddenBit fmt).toNat =
      2 ^ fmt.fracWidth + Model.fracField x := by
  rw [UInt64.toNat_or, fractionField_toNat hwidth,
    hiddenBit_toNat fmt hfracWidth]
  rw [Nat.or_two_pow_eq_add_of_lt (Model.fracField_lt_pow2 x)]
  rw [Nat.add_comm]

/-- Decoded normal significand value for any format that fits in one storage word. -/
theorem normalMantissa_toNat_of_width {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (x : Model fmt) :
    (fractionField fmt (toWord x) ||| hiddenBit fmt).toNat =
      2 ^ fmt.fracWidth + Model.fracField x := by
  rw [UInt64.toNat_or, fractionField_toNat hwidth,
    hiddenBit_toNat_of_width fmt hwidth]
  rw [Nat.or_two_pow_eq_add_of_lt (Model.fracField_lt_pow2 x)]
  rw [Nat.add_comm]

/--
The implicit-bit significand extracted from a one-word value is normalized.

Only the stored fraction-width bound is needed; classification of the source value is handled by
the calling kernel before it treats this word as a normal significand.
-/
theorem normalMantissa_bounds_of_width {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (x : Model fmt) :
    2 ^ fmt.fracWidth ≤
        (fractionField fmt (toWord x) ||| hiddenBit fmt).toNat ∧
      (fractionField fmt (toWord x) ||| hiddenBit fmt).toNat <
        2 ^ (fmt.fracWidth + 1) := by
  rw [normalMantissa_toNat_of_width hwidth x, pow_succ]
  have hfrac := Model.fracField_lt_pow2 x
  omega

/-- Native sign extraction agrees with the canonical storage decoder. -/
theorem signField_eq {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (x : Model fmt) :
    signField fmt (toWord x) = Model.signBit x := by
  have hindex : fmt.expWidth + fmt.fracWidth < 64 := fieldWidth_lt_64 fmt hwidth
  have hindexWord :
      (UInt64.ofNat (fmt.expWidth + fmt.fracWidth)).toNat = fmt.expWidth + fmt.fracWidth := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (lt_trans hindex (by norm_num))]
  have hlast : fmt.bitWidth - 1 = fmt.expWidth + fmt.fracWidth := by
    unfold FloatFormat.bitWidth
    omega
  rw [Model.signBit_eq_msb, BitVec.msb_eq_getLsbD_last, hlast]
  unfold signField
  rw [FloatLib.Numerics.FixedWord.bitAtWord_eq_testBit, toWord_toNat hwidth, hindexWord]
  rfl

/-- Native field packing agrees with the canonical exact-width constructor. -/
theorem ofWord_packFields {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (sign : Bool)
    (exponent fraction : UInt64) :
    ofWord (fmt := fmt) (packFields fmt sign exponent fraction) =
      Model.ofFields fmt sign exponent.toNat fraction.toNat := by
  rw [Model.ofFields_eq_ofFieldsImpl]
  unfold Model.ofFieldsImpl
  apply congrArg Model.ofBits
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNatLT, and_storageMask_toNat]
  unfold packFields Model.mkBitsImpl
  simp only [BitVec.ofNatLT_eq_ofNat, BitVec.toNat_ofNat]
  rw [UInt64.toNat_or, UInt64.toNat_or]
  have hfrac : fmt.fracWidth < 64 := fracWidth_lt_64 fmt hwidth
  have hfracPow : fmt.fracWidth < 2 ^ 64 := lt_trans hfrac (by norm_num)
  have hfield : fmt.expWidth + fmt.fracWidth < 64 :=
    fieldWidth_lt_64 fmt hwidth
  have hfieldPow :
      fmt.expWidth + fmt.fracWidth < 2 ^ 64 :=
    lt_trans hfield (by norm_num)
  have hexponentMask :
      (exponent &&& exponentMask fmt).toNat =
        exponent.toNat &&& fmt.expAllOnesNat := by
    rw [UInt64.toNat_and, exponentMask_toNat hwidth]
  have hfractionMask :
      (fraction &&& fractionMask fmt).toNat =
        fraction.toNat &&& fmt.fracMaskNat := by
    rw [UInt64.toNat_and, fractionMask_toNat hwidth]
  have hexponentBound :
      exponent.toNat &&& fmt.expAllOnesNat < 2 ^ fmt.expWidth :=
    Nat.and_lt_two_pow exponent.toNat (expMask_lt_field fmt)
  have hexponentShift :
      (exponent.toNat &&& fmt.expAllOnesNat) <<< fmt.fracWidth <
        2 ^ 64 := by
    have hshift :=
      Nat.shiftLeft_lt (m := fmt.fracWidth) hexponentBound
    exact hshift.trans_le <|
      Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hfield)
  have hsignShift :
      (1 : Nat) <<< (fmt.expWidth + fmt.fracWidth) < 2 ^ 64 := by
    simpa [Nat.shiftLeft_eq] using
      Nat.pow_lt_pow_right (by decide) hfield
  have hexponentShiftEq :
      Nat.shiftLeft (exponent.toNat &&& fmt.expAllOnesNat) fmt.fracWidth =
        (exponent.toNat &&& fmt.expAllOnesNat) * 2 ^ fmt.fracWidth :=
    Nat.shiftLeft_eq _ _
  have hsignShiftEq :
      Nat.shiftLeft 1 (fmt.expWidth + fmt.fracWidth) =
        2 ^ (fmt.expWidth + fmt.fracWidth) := by
    simpa using Nat.shiftLeft_eq 1 (fmt.expWidth + fmt.fracWidth)
  rw [UInt64.toNat_shiftLeft, hexponentMask, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt hfracPow, Nat.mod_eq_of_lt hfrac,
    Nat.mod_eq_of_lt hexponentShift, hfractionMask]
  cases sign
  · simp only [Bool.false_eq_true, ite_false, UInt64.toNat_zero,
      Nat.zero_or, Nat.shiftLeft_eq]
    rw [hexponentShiftEq]
  · simp only [ite_true]
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt hfieldPow, Nat.mod_eq_of_lt hfield,
      show (1 : UInt64).toNat = 1 by decide,
      Nat.mod_eq_of_lt hsignShift]
    simp only [Nat.shiftLeft_eq]
    rw [hsignShiftEq, hexponentShiftEq]
    simp only [one_mul]

/-- A native packed word uses no bits above the format's exact storage width. -/
theorem packFields_toNat_lt {fmt : FloatFormat}
    (hwidth : fmt.bitWidth ≤ 64) (sign : Bool)
    (exponent fraction : UInt64) :
    (packFields fmt sign exponent fraction).toNat <
      2 ^ fmt.bitWidth := by
  unfold packFields
  rw [UInt64.toNat_or, UInt64.toNat_or]
  have hfrac : fmt.fracWidth < 64 := fracWidth_lt_64 fmt hwidth
  have hfracPow : fmt.fracWidth < 2 ^ 64 := lt_trans hfrac (by norm_num)
  have hfield : fmt.expWidth + fmt.fracWidth < 64 :=
    fieldWidth_lt_64 fmt hwidth
  have hfieldPow :
      fmt.expWidth + fmt.fracWidth < 2 ^ 64 :=
    lt_trans hfield (by norm_num)
  have hexponentMask :
      (exponent &&& exponentMask fmt).toNat =
        exponent.toNat &&& fmt.expAllOnesNat := by
    rw [UInt64.toNat_and, exponentMask_toNat hwidth]
  have hfractionMask :
      (fraction &&& fractionMask fmt).toNat =
        fraction.toNat &&& fmt.fracMaskNat := by
    rw [UInt64.toNat_and, fractionMask_toNat hwidth]
  have hexponentBound :
      exponent.toNat &&& fmt.expAllOnesNat < 2 ^ fmt.expWidth :=
    Nat.and_lt_two_pow exponent.toNat (expMask_lt_field fmt)
  have hfractionBound :
      fraction.toNat &&& fmt.fracMaskNat < 2 ^ fmt.fracWidth :=
    Nat.and_lt_two_pow fraction.toNat (fracMask_lt_field fmt)
  have hexponentShift :
      (exponent.toNat &&& fmt.expAllOnesNat) <<< fmt.fracWidth <
        2 ^ fmt.bitWidth := by
    have hshift :=
      Nat.shiftLeft_lt (m := fmt.fracWidth) hexponentBound
    exact hshift.trans_le <|
      Nat.pow_le_pow_right (by decide) (by
        unfold FloatFormat.bitWidth
        omega)
  have hfractionTarget :
      fraction.toNat &&& fmt.fracMaskNat < 2 ^ fmt.bitWidth :=
    hfractionBound.trans_le <|
      Nat.pow_le_pow_right (by decide) (by
        unfold FloatFormat.bitWidth
        omega)
  have hsignTarget :
      (1 : Nat) <<< (fmt.expWidth + fmt.fracWidth) <
        2 ^ fmt.bitWidth := by
    simp only [Nat.shiftLeft_eq, one_mul]
    unfold FloatFormat.bitWidth
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  rw [UInt64.toNat_shiftLeft, hexponentMask, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt hfracPow, Nat.mod_eq_of_lt hfrac,
    hfractionMask]
  have hexponentShift64 :
      (exponent.toNat &&& fmt.expAllOnesNat) <<< fmt.fracWidth <
        2 ^ 64 :=
    hexponentShift.trans_le <|
      Nat.pow_le_pow_right (by decide) hwidth
  rw [Nat.mod_eq_of_lt hexponentShift64]
  cases sign
  · simp only [Bool.false_eq_true, ite_false, UInt64.toNat_zero,
      Nat.zero_or]
    exact Nat.or_lt_two_pow hexponentShift hfractionTarget
  · simp only [ite_true]
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt hfieldPow, Nat.mod_eq_of_lt hfield,
      show (1 : UInt64).toNat = 1 by decide]
    have hsignShift64 :
        (1 : Nat) <<< (fmt.expWidth + fmt.fracWidth) < 2 ^ 64 :=
      hsignTarget.trans_le <|
        Nat.pow_le_pow_right (by decide) hwidth
    rw [Nat.mod_eq_of_lt hsignShift64]
    exact Nat.or_lt_two_pow
      (Nat.or_lt_two_pow hsignTarget hexponentShift)
      hfractionTarget

/-! ## Rounding thresholds in machine words -/

private theorem fracWidthWord_toNat {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    (UInt64.ofNat fmt.fracWidth).toNat = fmt.fracWidth := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (lt_trans (fracWidth_lt_64 fmt hwidth) (by norm_num))]

private theorem bias_lt_two_pow_62 {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    fmt.bias < 2 ^ 62 := by
  have hfracPos := fmt.fracWidth_pos
  have hexp : fmt.expWidth ≤ 62 := by
    unfold FloatFormat.bitWidth at hwidth
    omega
  exact (FloatFormat.bias_lt_pow_expWidth fmt).trans_le (Nat.pow_le_pow_right (by decide) hexp)

private theorem biasSum_toNat {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth).toNat = fmt.bias + 2 * fmt.fracWidth := by
  have hbias := bias_lt_two_pow_62 hwidth
  have hfrac := fracWidth_lt_64 fmt hwidth
  have htwo : (2 : UInt64).toNat = 2 := by decide
  have hdouble : 2 * fmt.fracWidth < 2 ^ 64 := by
    norm_num
    omega
  have hsum : fmt.bias + 2 * fmt.fracWidth < 2 ^ 64 := by
    norm_num at hbias ⊢
    omega
  rw [UInt64.toNat_add, UInt64.toNat_mul, biasWord_toNat hwidth, fracWidthWord_toNat hwidth, htwo,
    Nat.mod_eq_of_lt hdouble, Nat.mod_eq_of_lt hsum]

private theorem tripleBiasSum_toNat {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    (3 * biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth).toNat =
      3 * fmt.bias + 2 * fmt.fracWidth := by
  have hbias := bias_lt_two_pow_62 hwidth
  have hfrac := fracWidth_lt_64 fmt hwidth
  have htwo : (2 : UInt64).toNat = 2 := by decide
  have hthree : (3 : UInt64).toNat = 3 := by decide
  have hproduct : 3 * fmt.bias < 2 ^ 64 := by
    norm_num at hbias ⊢
    omega
  have hdouble : 2 * fmt.fracWidth < 2 ^ 64 := by
    norm_num
    omega
  have hsum : 3 * fmt.bias + 2 * fmt.fracWidth < 2 ^ 64 := by
    norm_num at hbias ⊢
    omega
  rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mul, biasWord_toNat hwidth,
    fracWidthWord_toNat hwidth, htwo, hthree, Nat.mod_eq_of_lt hproduct, Nat.mod_eq_of_lt hdouble,
    Nat.mod_eq_of_lt hsum]

/-- Value of the machine-word first normal leading-bit position `bias + 2 * fracWidth - 1`. -/
theorem normalThreshold_toNat {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 1).toNat =
      fmt.bias + 2 * fmt.fracWidth - 1 := by
  have hsum := biasSum_toNat hwidth
  have hfracPos := fmt.fracWidth_pos
  rw [UInt64.toNat_sub_of_le, hsum, UInt64.toNat_one]
  rw [UInt64.le_iff_toNat_le, hsum, UInt64.toNat_one]
  omega

/-- Value of the machine-word overflow threshold `3 * bias + 2 * fracWidth - 2`. -/
theorem overflowThreshold_toNat {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    (3 * biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2).toNat =
      3 * fmt.bias + 2 * fmt.fracWidth - 2 := by
  have hsum := tripleBiasSum_toNat hwidth
  have hfracPos := fmt.fracWidth_pos
  rw [UInt64.toNat_sub_of_le, hsum, show (2 : UInt64).toNat = 2 by decide]
  rw [UInt64.le_iff_toNat_le, hsum, show (2 : UInt64).toNat = 2 by decide]
  omega

/-- Value of the machine-word exponent offset `bias + 2 * fracWidth - 2`. -/
theorem exponentOffset_toNat {fmt : FloatFormat} (hwidth : fmt.bitWidth ≤ 64) :
    (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2).toNat =
      fmt.bias + 2 * fmt.fracWidth - 2 := by
  have hsum := biasSum_toNat hwidth
  have hfracPos := fmt.fracWidth_pos
  rw [UInt64.toNat_sub_of_le, hsum, show (2 : UInt64).toNat = 2 by decide]
  rw [UInt64.le_iff_toNat_le, hsum, show (2 : UInt64).toNat = 2 by decide]
  omega

end Model.NativeSmallWord
end FloatLib.Floats.Formats.BinaryInterchange
