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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Model.RealSemantics

/-!
# Packing finite values in Lean's float model

Lean's `Float.Model.UnpackedFloat.pack` assumes that finite inputs have already been normalized for
the selected format. This module proves exact round trips for representable normal and subnormal
values in Lean's width-parameterized IEEE model. Agreement with the descriptor's real decoder
requires `fmt.isIEEE = true`.

Numerical rounding is handled separately by the rounding semantics.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model
open Float.Model.UnpackedFloat

/--
If packing a finite logical value produces a finite executable value, the biased exponent did not
reach the all-ones encoding. This observable side condition keeps overflow handling out of
arithmetic refinement proofs.
-/
theorem noOverflow_of_isFinite_ofModel_finite
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Sign) (mantissa : Nat) (exponent : Int)
    (hm : mantissa ≠ 0)
    (hfin : isFinite
      (ofModel fmt (.finite sign mantissa exponent (Nat.pos_of_ne_zero hm))) = true) :
    (exponent + (FloatFormat.toModel fmt).exponentBias +
        (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat + 1 <
      2 ^ (FloatFormat.toModel fmt).exponentBits := by
  by_contra hnot
  have hoverflow :
      2 ^ (FloatFormat.toModel fmt).exponentBits ≤
        (exponent + (FloatFormat.toModel fmt).exponentBias +
          (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat + 1 :=
    Nat.not_lt.mp hnot
  have hpack :
      Float.Model.UnpackedFloat.pack (FloatFormat.toModel fmt)
          (.finite sign mantissa exponent (Nat.pos_of_ne_zero hm)) =
        packedInfinity (FloatFormat.toModel fmt) sign := by
    simp [Float.Model.UnpackedFloat.pack, hoverflow]
  have hexponent :
      expField
          (ofModel fmt (.finite sign mantissa exponent (Nat.pos_of_ne_zero hm))) =
      FloatFormat.expAllOnesNat fmt := by
    rw [← unpackExponent_toNat]
    unfold ofModel toModelBits ofModelBits
    rw [hpack]
    simp only [packedInfinity, unpackExponent_packComponents]
    exact toNat_neg_one_exponentBits fmt
  have hencoding := (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt |>.1
  have hfinIEEE :
      IEEE.isFinite
          (ofModel fmt (.finite sign mantissa exponent (Nat.pos_of_ne_zero hm))) = true := by
    simpa [isFinite, hencoding] using hfin
  exact (bne_iff_ne.mp hfinIEEE) hexponent

/-- A positive integer whose binary length is `p` lies between `2^(p-1)` and `2^p`. -/
private theorem normalizedMantissa_bounds (mantissa p : Nat) (hm : mantissa ≠ 0)
    (hbits : mantissa.log2 + 1 = p) :
    2 ^ (p - 1) ≤ mantissa ∧ mantissa < 2 ^ p := by
  have hlower : 2 ^ mantissa.log2 ≤ mantissa := Nat.log2_self_le hm
  have hupper : mantissa < 2 ^ (mantissa.log2 + 1) := by
    have hlog : Nat.log2 mantissa = Nat.log 2 mantissa := Nat.log2_eq_log_two
    simpa [hlog, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (b := 2) (hb := Nat.one_lt_two) mantissa
  constructor
  · simpa [← hbits] using hlower
  · simpa [hbits] using hupper

/-- Packing and unpacking a representable normal value preserves the unpacked value exactly. -/
theorem unpack_pack_finite_normal
    (spec : Format) (sign : Sign) (mantissa : Nat) (exponent : Int)
    (hm : mantissa ≠ 0)
    (hbits : mantissa.log2 + 1 = spec.mantissaBits)
    (hbiasedNonneg :
      0 ≤ exponent + spec.exponentBias + spec.mantissaBitsWithoutImplicit)
    (hbiasedPos :
      0 < exponent + spec.exponentBias + spec.mantissaBitsWithoutImplicit)
    (hnoOverflow :
      (exponent + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat + 1 <
        2 ^ spec.exponentBits) :
    unpack spec (pack spec (.finite sign mantissa exponent (Nat.pos_of_ne_zero hm))) =
      .finite sign mantissa exponent (Nat.pos_of_ne_zero hm) := by
  obtain ⟨biased, hbiased⟩ : ∃ biased : Nat,
      biased = (exponent + spec.exponentBias + spec.mantissaBitsWithoutImplicit).toNat :=
    ⟨_, rfl⟩
  have hbiasedInt :
      (biased : Int) = exponent + spec.exponentBias + spec.mantissaBitsWithoutImplicit := by
    rw [hbiased]
    exact Int.toNat_of_nonneg hbiasedNonneg
  rw [← hbiased] at hnoOverflow
  have hbiasedLt : biased < 2 ^ spec.exponentBits := by omega
  have hbiasedNeAllOnes : BitVec.ofNat spec.exponentBits biased ≠ -1#spec.exponentBits := by
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.neg_one_eq_allOnes, BitVec.toNat_ofNat, BitVec.toNat_allOnes,
      Nat.mod_eq_of_lt hbiasedLt] at this
    omega
  have hbiasedNeZero : BitVec.ofNat spec.exponentBits biased ≠ 0#_ := by
    intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mod_eq_of_lt hbiasedLt] at this
    omega
  have hb := normalizedMantissa_bounds mantissa spec.mantissaBits hm hbits
  have hlower : 2 ^ spec.mantissaBitsWithoutImplicit ≤ mantissa := by
    simpa [Format.mantissaBits] using hb.1
  have hmantissaMod :
      mantissa % 2 ^ spec.mantissaBitsWithoutImplicit =
        mantissa - 2 ^ spec.mantissaBitsWithoutImplicit := by
    rw [Nat.mod_eq_sub_mod hlower, Nat.mod_eq_of_lt]
    have hupper := hb.2
    rw [show spec.mantissaBits = spec.mantissaBitsWithoutImplicit + 1 by
      simp [Format.mantissaBits, Nat.add_comm], Nat.pow_succ] at hupper
    omega
  have hmantissaDecode :
      (1#1 ++ BitVec.ofNat spec.mantissaBitsWithoutImplicit mantissa).toNat = mantissa := by
    rw [BitVec.toNat_append,
      ← Nat.shiftLeft_add_eq_or_of_lt
        (BitVec.ofNat spec.mantissaBitsWithoutImplicit mantissa).isLt]
    simp only [BitVec.toNat_ofNat]
    rw [hmantissaMod]
    simp [Nat.shiftLeft_eq]
    omega
  have hexponentDecode :
      (Int.ofNat (BitVec.ofNat spec.exponentBits biased).toNat -
          ((spec.exponentBias : Int) + spec.mantissaBitsWithoutImplicit)) = exponent := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbiasedLt]
    change (biased : Int) - ((spec.exponentBias : Int) + spec.mantissaBitsWithoutImplicit) =
      exponent
    rw [hbiasedInt]
    ring
  have hsign : Sign.ofBitVec sign.toBitVec = sign := by
    cases sign <;> rfl
  unfold Float.Model.UnpackedFloat.pack
  rw [← hbiased]
  simp only [not_le.mpr (Nat.lt_of_lt_of_le hnoOverflow le_rfl), ite_false, hbits, ite_true]
  unfold Float.Model.UnpackedFloat.unpack
  simp only [unpackExponent_packComponents, unpackMantissa_packComponents,
    unpackSign_packComponents, hbiasedNeAllOnes, hbiasedNeZero, ite_false, hmantissaDecode, hsign]
  congr

/-- Packing a representable normal model value preserves its exact real value. -/
theorem toReal_ofModel_finite_normal
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Sign) (mantissa : Nat) (exponent : Int)
    (hm : mantissa ≠ 0)
    (hbits : mantissa.log2 + 1 = (FloatFormat.toModel fmt).mantissaBits)
    (hbiasedNonneg :
      0 ≤ exponent + (FloatFormat.toModel fmt).exponentBias +
        (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit)
    (hbiasedPos :
      0 < exponent + (FloatFormat.toModel fmt).exponentBias +
        (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit)
    (hnoOverflow :
      (exponent + (FloatFormat.toModel fmt).exponentBias +
          (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat + 1 <
        2 ^ (FloatFormat.toModel fmt).exponentBits) :
    toReal (ofModel fmt (.finite sign mantissa exponent (Nat.pos_of_ne_zero hm))) =
      (if modelSignBit sign then (-1 : ℝ) else 1) * (mantissa : ℝ) *
        FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix exponent := by
  rw [toReal_eq_unpackedToReal_toModel hfmt]
  unfold toModel ofModel toModelBits ofModelBits
  rw [unpack_pack_finite_normal (FloatFormat.toModel fmt) sign mantissa exponent hm
    hbits hbiasedNonneg hbiasedPos hnoOverflow]
  exact unpackedToReal_finite sign mantissa exponent (Nat.pos_of_ne_zero hm)

/-- Packing and unpacking a nonzero subnormal preserves its sign, mantissa, and exponent. -/
theorem unpack_pack_finite_subnormal
    (fmt : FloatFormat) (sign : Sign) (mantissa : Nat)
    (hm : mantissa ≠ 0) (hfit : mantissa < 2 ^ fmt.fracWidth) :
    unpack (FloatFormat.toModel fmt)
        (pack (FloatFormat.toModel fmt)
          (.finite sign mantissa (FloatFormat.ieeeMinSubnormalExponent fmt)
            (Nat.pos_of_ne_zero hm))) =
      .finite sign mantissa (FloatFormat.ieeeMinSubnormalExponent fmt)
        (Nat.pos_of_ne_zero hm) := by
  let spec := FloatFormat.toModel fmt
  have hbiased :
      (FloatFormat.ieeeMinSubnormalExponent fmt + spec.exponentBias +
        spec.mantissaBitsWithoutImplicit).toNat = 1 := by
    change ((1 : Int) - fmt.bias - fmt.fracWidth + fmt.bias + fmt.fracWidth).toNat = 1
    omega
  have hpowFour : 4 ≤ 2 ^ fmt.expWidth := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) fmt.expWidth_ge_two
  have hnotInf : ¬2 ^ spec.exponentBits ≤
      (FloatFormat.ieeeMinSubnormalExponent fmt + spec.exponentBias +
        spec.mantissaBitsWithoutImplicit).toNat + 1 := by
    rw [hbiased]
    change ¬2 ^ fmt.expWidth ≤ 2
    omega
  have hlogLt : mantissa.log2 < fmt.fracWidth := by
    exact (Nat.log2_lt hm).2 hfit
  have hnotNormal :
      ¬mantissa.log2 + 1 = spec.mantissaBits := by
    simp only [spec, FloatFormat.toModel, Format.mantissaBits]
    omega
  have hnotInfRaw :
      ¬2 ^ (FloatFormat.toModel fmt).exponentBits ≤
        (FloatFormat.ieeeMinSubnormalExponent fmt +
          (FloatFormat.toModel fmt).exponentBias +
          (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat + 1 := by
    simpa [spec] using hnotInf
  have hnotNormalRaw :
      ¬mantissa.log2 + 1 = (FloatFormat.toModel fmt).mantissaBits := by
    simpa [spec] using hnotNormal
  have hmantissaVecNe :
      BitVec.ofNat fmt.fracWidth mantissa ≠ 0#fmt.fracWidth := by
    intro h
    have hnat := congrArg BitVec.toNat h
    change mantissa % 2 ^ fmt.fracWidth = 0 at hnat
    rw [Nat.mod_eq_of_lt hfit] at hnat
    exact hm hnat
  have hmantissaDecode :
      (BitVec.ofNat fmt.fracWidth mantissa).toNat = mantissa := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
  have hzeroExponentNeAllOnes :
      (0#(FloatFormat.toModel fmt).exponentBits) ≠
        (-1#(FloatFormat.toModel fmt).exponentBits) := by
    change (0#fmt.expWidth) ≠ (-1#fmt.expWidth)
    rw [ne_eq, BitVec.zero_eq_neg_one_iff]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 2) fmt.expWidth_ge_two)
  have hmantissaVecNeRaw :
      BitVec.ofNat (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit mantissa ≠
        0#(FloatFormat.toModel fmt).mantissaBitsWithoutImplicit := by
    simpa [FloatFormat.toModel] using hmantissaVecNe
  have hmantissaDecodeRaw :
      (BitVec.ofNat (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit mantissa).toNat =
        mantissa := by
    simpa [FloatFormat.toModel] using hmantissaDecode
  unfold Float.Model.UnpackedFloat.pack
  simp only [hnotInfRaw, ite_false, hnotNormalRaw]
  unfold Float.Model.UnpackedFloat.unpack
  simp only [unpackExponent_packComponents, unpackMantissa_packComponents,
    unpackSign_packComponents]
  have hsign : Sign.ofBitVec sign.toBitVec = sign := by
    cases sign <;> rfl
  simp only [hzeroExponentNeAllOnes, ↓reduceIte, hmantissaVecNeRaw, ↓reduceDIte, hsign,
    hmantissaDecodeRaw,
    BitVec.toNat_ofNat, Nat.zero_mod, CharP.cast_eq_zero, zero_sub, neg_add_rev, finite.injEq,
      true_and]
  change -(fmt.fracWidth : Int) + -(fmt.bias : Int) + 1 =
    FloatFormat.ieeeMinSubnormalExponent fmt
  simp only [FloatFormat.ieeeMinSubnormalExponent, Int.ofNat_eq_natCast]
  abel

/--
Packing and unpacking any nonzero value on the minimum-exponent grid is exact up to and including
the smallest normal value. The endpoint `2^p` changes encoding class, but not its unpacked logical
value.
-/
theorem unpack_pack_finite_at_minSubnormal
    (fmt : FloatFormat) (sign : Sign) (mantissa : Nat)
    (hm : mantissa ≠ 0) (hfit : mantissa ≤ 2 ^ fmt.fracWidth) :
    unpack (FloatFormat.toModel fmt)
        (pack (FloatFormat.toModel fmt)
          (.finite sign mantissa (FloatFormat.ieeeMinSubnormalExponent fmt)
            (Nat.pos_of_ne_zero hm))) =
      .finite sign mantissa (FloatFormat.ieeeMinSubnormalExponent fmt)
        (Nat.pos_of_ne_zero hm) := by
  rcases hfit.lt_or_eq with hlt | heq
  · exact unpack_pack_finite_subnormal fmt sign mantissa hm hlt
  · subst mantissa
    apply unpack_pack_finite_normal
    · simp
    · simp only [Nat.log2_two_pow, FloatFormat.toModel, Format.mantissaBits]
      omega
    · change 0 ≤ FloatFormat.ieeeMinSubnormalExponent fmt + fmt.bias + fmt.fracWidth
      unfold FloatFormat.ieeeMinSubnormalExponent
      simp only [Int.ofNat_eq_natCast]
      omega
    · change 0 < FloatFormat.ieeeMinSubnormalExponent fmt + fmt.bias + fmt.fracWidth
      unfold FloatFormat.ieeeMinSubnormalExponent
      simp only [Int.ofNat_eq_natCast]
      omega
    · change
        (FloatFormat.ieeeMinSubnormalExponent fmt + fmt.bias + fmt.fracWidth).toNat + 1 <
          2 ^ fmt.expWidth
      have hfour : 4 ≤ 2 ^ fmt.expWidth := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) fmt.expWidth_ge_two
      simp only [FloatFormat.ieeeMinSubnormalExponent, Int.ofNat_eq_natCast]
      omega

/-- Packing a representable nonzero subnormal preserves its exact real value. -/
theorem toReal_ofModel_finite_subnormal
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Sign) (mantissa : Nat)
    (hm : mantissa ≠ 0) (hfit : mantissa < 2 ^ fmt.fracWidth) :
    toReal (ofModel fmt
        (.finite sign mantissa (FloatFormat.ieeeMinSubnormalExponent fmt)
          (Nat.pos_of_ne_zero hm))) =
      (if modelSignBit sign then (-1 : ℝ) else 1) * (mantissa : ℝ) *
        FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
          (FloatFormat.ieeeMinSubnormalExponent fmt) := by
  rw [toReal_eq_unpackedToReal_toModel hfmt]
  unfold toModel ofModel toModelBits ofModelBits
  rw [unpack_pack_finite_subnormal fmt sign mantissa hm hfit]
  exact unpackedToReal_finite sign mantissa (FloatFormat.ieeeMinSubnormalExponent fmt)
    (Nat.pos_of_ne_zero hm)

/-- Every nonzero value on the minimum-exponent grid up to the smallest normal value
keeps its exact real value when packed. -/
theorem toReal_ofModel_finite_at_minSubnormal
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Sign) (mantissa : Nat)
    (hm : mantissa ≠ 0) (hfit : mantissa ≤ 2 ^ fmt.fracWidth) :
    toReal (ofModel fmt
        (.finite sign mantissa (FloatFormat.ieeeMinSubnormalExponent fmt)
          (Nat.pos_of_ne_zero hm))) =
      (if modelSignBit sign then (-1 : ℝ) else 1) * (mantissa : ℝ) *
        FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
          (FloatFormat.ieeeMinSubnormalExponent fmt) := by
  rw [toReal_eq_unpackedToReal_toModel hfmt]
  unfold toModel ofModel toModelBits ofModelBits
  rw [unpack_pack_finite_at_minSubnormal fmt sign mantissa hm hfit]
  exact unpackedToReal_finite sign mantissa (FloatFormat.ieeeMinSubnormalExponent fmt)
    (Nat.pos_of_ne_zero hm)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
