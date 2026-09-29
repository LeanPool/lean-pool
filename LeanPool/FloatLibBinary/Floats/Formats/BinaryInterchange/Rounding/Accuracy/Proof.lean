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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.Accuracy.Model
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.Proof

/-!
# Rounded-real meaning of Lean accuracy certificates

Lean's unpacked-float model represents a positive real by a truncated natural mantissa, an
exponent, and an `Accuracy` certificate. This module proves that `roundWithAccuracy` rounds that
real exactly as the independent Flocq-style `roundAt` model whenever normalization only shifts
right and the packed output remains finite. Agreement with `roundAt` requires a conventional
IEEE descriptor. This bridge is used by square root and other non-dyadic kernels.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model.UnpackedFloat
open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

/-- The model and rounded-real semantics choose the same exponent for a valid certificate. -/
theorem cexp_accuracy_mul_bpow_eq_targetExponent
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) (value : Real) (hfmt : fmt.isIEEE = true)
    (hmantissa : mantissa ≠ 0)
    (haccuracy : accuracyRepresents mantissa accuracy value) :
    cexp Numerics.binaryRadix (fexpOf fmt)
        (value * bpow Numerics.binaryRadix exponent) =
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent) := by
  have hvaluePos : 0 < value := by
    have hbounds := accuracyRepresents_bounds haccuracy
    have hmantissaPos : (0 : Real) < mantissa := by
      exact_mod_cast Nat.pos_of_ne_zero hmantissa
    exact hmantissaPos.trans_le hbounds.1
  have hmagnitude :
      magnitude Numerics.binaryRadix
          (value * bpow Numerics.binaryRadix exponent) =
        Int.ofNat mantissa.log2 + 1 + exponent := by
    rw [magnitude_mul_bpow _ _ _ hvaluePos.ne']
    rw [magnitude_of_accuracyRepresents hmantissa haccuracy]
  rw [cexp, hmagnitude]
  simp [fexpOf, fltExp, Float.Model.Format.targetExponent,
    Float.Model.totalExponent, Float.Model.Format.mantissaBits,
    Float.Model.Format.minExponent, FloatFormat.toModel,
    FloatFormat.minSubnormalExponent_eq_ieee fmt hfmt,
    FloatFormat.ieeeMinSubnormalExponent, FloatFormat.bias]
  congr 1 <;> omega

/-- The certificate value at the model exponent is the canonical scaled mantissa. -/
theorem scaledMantissa_accuracy_mul_bpow
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) (value : Real) (hfmt : fmt.isIEEE = true)
    (hmantissa : mantissa ≠ 0)
    (haccuracy : accuracyRepresents mantissa accuracy value) :
    scaledMantissa Numerics.binaryRadix (fexpOf fmt)
        (value * bpow Numerics.binaryRadix exponent) =
      value * bpow Numerics.binaryRadix
        (exponent -
          (FloatFormat.toModel fmt).targetExponent
            (Float.Model.totalExponent mantissa exponent)) := by
  rw [scaledMantissa,
    cexp_accuracy_mul_bpow_eq_targetExponent fmt mantissa exponent
      accuracy value hfmt hmantissa haccuracy]
  rw [show exponent -
      (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent mantissa exponent) =
    exponent + -
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent) by ring]
  rw [bpow.add_exp]
  ring

/--
When no left shift is needed, the first stage of `roundWithAccuracy` shifts the extended mantissa
right to the target exponent and reports that exponent unchanged.
-/
theorem shiftToTargetExponent_eq_of_le_targetExponent
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy)
    (hle : exponent ≤
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent)) :
    Float.Model.UnpackedFloat.shiftToTargetExponent
        (FloatFormat.toModel fmt) mantissa exponent accuracy =
      (ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy >>>
          ((FloatFormat.toModel fmt).targetExponent
            (Float.Model.totalExponent mantissa exponent) - exponent).toNat,
        (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent mantissa exponent)) := by
  unfold Float.Model.UnpackedFloat.shiftToTargetExponent
    Float.Model.UnpackedFloat.shiftToExponent
  apply Prod.ext
  · rfl
  · dsimp only
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
    omega

/--
When no left shift is needed, the rounded mantissa produced by the first stage of
`roundWithAccuracy` is the nearest-even integer of the represented real scaled to the target
exponent.
-/
theorem roundedMantissa_shiftToTargetExponent_eq_nearestEven
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) (value : Real)
    (haccuracy : accuracyRepresents mantissa accuracy value)
    (hle : exponent ≤
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent)) :
    Int.ofNat
        (Float.Model.UnpackedFloat.shiftToTargetExponent
          (FloatFormat.toModel fmt) mantissa exponent accuracy).1.roundedMantissa =
      nearestEven
        (value * bpow Numerics.binaryRadix
          (exponent -
            (FloatFormat.toModel fmt).targetExponent
              (Float.Model.totalExponent mantissa exponent))) := by
  rw [shiftToTargetExponent_eq_of_le_targetExponent fmt mantissa exponent accuracy hle]
  dsimp only [Prod.fst]
  obtain ⟨shift, hshift⟩ : ∃ shift : Nat,
      shift = ((FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent) - exponent).toNat := ⟨_, rfl⟩
  have hshiftInt :
      (shift : Int) =
        (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent mantissa exponent) - exponent := by
    rw [hshift]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hle)
  rw [← hshift, roundedMantissa_eq_nearestEven mantissa accuracy value shift haccuracy]
  congr 1
  rw [show exponent -
      (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent mantissa exponent) =
    -(shift : Int) by omega]
  simp [bpow, Numerics.binaryRadix, Numerics.Radix.toReal, div_eq_mul_inv]

/--
Lean's signed `roundWithAccuracy` result has the same real value as independent nearest-even
rounding of the represented signed real. The exponent premise is the documented precondition of
`roundWithAccuracy`: normalization may discard low bits, but must not require a preliminary left
shift. The finiteness premise excludes IEEE overflow, which has no value in `Real`.
-/
theorem toReal_ofModel_roundWithAccuracy_eq_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Sign) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) (value : Real)
    (hmantissa : mantissa ≠ 0)
    (haccuracy : accuracyRepresents mantissa accuracy value)
    (hle : exponent ≤
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent))
    (hfinite :
      isFinite
        (ofModel fmt
          (Float.Model.UnpackedFloat.roundWithAccuracy
            (FloatFormat.toModel fmt) sign mantissa exponent accuracy)) = true) :
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.roundWithAccuracy
            (FloatFormat.toModel fmt) sign mantissa exponent accuracy)) =
      roundAt fmt
        ((if modelSignBit sign then (-1 : Real) else 1) *
          (value * bpow Numerics.binaryRadix exponent)) := by
  obtain ⟨k, hk⟩ : ∃ k : Int, k = (mantissa.log2 : Int) + exponent := ⟨_, rfl⟩
  obtain ⟨rounded, hrounded⟩ : ∃ rounded : Nat, rounded =
      (Float.Model.UnpackedFloat.shiftToTargetExponent
        (FloatFormat.toModel fmt) mantissa exponent accuracy).1.roundedMantissa := ⟨_, rfl⟩
  have hvaluePos : 0 < value := by
    have hbounds := accuracyRepresents_bounds haccuracy
    have hmantissaPos : (0 : Real) < mantissa := by
      exact_mod_cast Nat.pos_of_ne_zero hmantissa
    exact hmantissaPos.trans_le hbounds.1
  have hexactPos : 0 < value * bpow Numerics.binaryRadix exponent :=
    mul_pos hvaluePos (bpow.pos _ _)
  have hmagnitude :
      magnitude Numerics.binaryRadix (value * bpow Numerics.binaryRadix exponent) = k + 1 := by
    rw [magnitude_mul_bpow _ _ _ hvaluePos.ne',
      magnitude_of_accuracyRepresents hmantissa haccuracy, hk]
    simp only [Int.ofNat_eq_natCast]
    ring
  have hnearest :
      Int.ofNat rounded =
        nearestEven (value * bpow Numerics.binaryRadix
          (exponent - (FloatFormat.toModel fmt).targetExponent
            (Float.Model.totalExponent mantissa exponent))) := by
    rw [hrounded]
    exact roundedMantissa_shiftToTargetExponent_eq_nearestEven
      fmt mantissa exponent accuracy value haccuracy hle
  have hroundAt :
      roundAt fmt
          ((if modelSignBit sign then (-1 : Real) else 1) *
            (value * bpow Numerics.binaryRadix exponent)) =
        (if modelSignBit sign then (-1 : Real) else 1) *
          ((rounded : Real) * bpow Numerics.binaryRadix
            ((FloatFormat.toModel fmt).targetExponent
              (Float.Model.totalExponent mantissa exponent))) := by
    have hpositive :
        roundAt fmt (value * bpow Numerics.binaryRadix exponent) =
          (rounded : Real) * bpow Numerics.binaryRadix
            ((FloatFormat.toModel fmt).targetExponent
              (Float.Model.totalExponent mantissa exponent)) := by
      unfold roundAt FloatLib.Floats.Formats.Flocq.round FloatLib.Floats.Formats.Flocq.toReal
      rw [cexp_accuracy_mul_bpow_eq_targetExponent fmt mantissa exponent accuracy value hfmt
          hmantissa haccuracy,
        scaledMantissa_accuracy_mul_bpow fmt mantissa exponent accuracy value hfmt hmantissa
          haccuracy, ← hnearest]
      norm_num
    cases sign <;> simp [modelSignBit, hpositive, roundAt_neg]
  rw [hroundAt]
  rw [roundWithAccuracy_eq_finishRoundedMantissa,
    shiftToTargetExponent_eq_of_le_targetExponent fmt mantissa exponent accuracy hle]
    at hfinite ⊢
  rw [shiftToTargetExponent_eq_of_le_targetExponent fmt mantissa exponent accuracy hle]
    at hrounded
  dsimp only at hrounded hfinite ⊢
  rw [← hrounded] at hfinite ⊢
  /- Bounds on the scaled real transfer to the rounded mantissa by monotonicity of
  nearest-even rounding. -/
  have hscaledMul : ∀ target : Int,
      value * bpow Numerics.binaryRadix (exponent - target) * bpow Numerics.binaryRadix target =
        value * bpow Numerics.binaryRadix exponent := by
    intro target
    rw [mul_assoc, ← bpow.add_exp, sub_add_cancel]
  have hlowerExact : bpow Numerics.binaryRadix k ≤ value * bpow Numerics.binaryRadix exponent := by
    simpa [abs_of_pos hexactPos, hmagnitude] using
      bpow_magnitude_sub_one_le Numerics.binaryRadix _ hexactPos.ne'
  have hupperExact :
      value * bpow Numerics.binaryRadix exponent < bpow Numerics.binaryRadix (k + 1) := by
    simpa [abs_of_pos hexactPos, hmagnitude] using
      abs_lt_bpow_magnitude Numerics.binaryRadix _ hexactPos.ne'
  by_cases hsub : k < FloatFormat.ieeeMinNormalExponent fmt
  · rw [targetExponent_eq_minSubnormal_of_lt_minNormal fmt mantissa exponent (hk ▸ hsub)]
      at hnearest hfinite ⊢
    have hscaledLe :
        value * bpow Numerics.binaryRadix
            (exponent - FloatFormat.ieeeMinSubnormalExponent fmt) ≤
          (pow2 fmt.fracWidth : Real) := by
      refine le_of_mul_le_mul_right ?_ (bpow.pos Numerics.binaryRadix
        (FloatFormat.ieeeMinSubnormalExponent fmt))
      rw [hscaledMul, natCast_pow2_eq_bpow, ← bpow.add_exp]
      refine hupperExact.le.trans ((bpow_le_bpow_iff Numerics.binaryRadix _ _).2 ?_)
      unfold FloatFormat.ieeeMinSubnormalExponent
      unfold FloatFormat.ieeeMinNormalExponent at hsub
      simp only [Int.ofNat_eq_natCast] at hsub ⊢
      omega
    rw [toReal_ofModel_finishRoundedMantissa_minSubnormal fmt hfmt sign rounded
      (Int.ofNat_le.mp (hnearest.trans_le (nearestEven_le_natCast_of_le hscaledLe)))]
  · have hnormal : FloatFormat.ieeeMinNormalExponent fmt ≤ k := le_of_not_gt hsub
    rw [targetExponent_eq_normal fmt mantissa exponent (hk ▸ hnormal), ← hk]
      at hnearest hfinite ⊢
    have hdenPos : 0 < bpow Numerics.binaryRadix (k - fmt.fracWidth) := bpow.pos _ _
    have hscaledLower :
        (pow2 fmt.fracWidth : Real) ≤
          value * bpow Numerics.binaryRadix (exponent - (k - fmt.fracWidth)) := by
      refine le_of_mul_le_mul_right ?_ hdenPos
      rw [hscaledMul, natCast_pow2_eq_bpow, ← bpow.add_exp, add_sub_cancel]
      exact hlowerExact
    have hscaledUpper :
        value * bpow Numerics.binaryRadix (exponent - (k - fmt.fracWidth)) ≤
          (pow2 (fmt.fracWidth + 1) : Real) := by
      refine le_of_mul_le_mul_right ?_ hdenPos
      rw [hscaledMul, natCast_pow2_eq_bpow, ← bpow.add_exp]
      refine hupperExact.le.trans_eq (congrArg _ ?_)
      push_cast
      ring
    rw [toReal_ofModel_finishRoundedMantissa_normal fmt hfmt sign rounded k
      (Int.ofNat_le.mp ((natCast_le_nearestEven_of_le hscaledLower).trans hnearest.symm.le))
      (Int.ofNat_le.mp (hnearest.trans_le (nearestEven_le_natCast_of_le hscaledUpper)))
      hnormal hfinite]

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
