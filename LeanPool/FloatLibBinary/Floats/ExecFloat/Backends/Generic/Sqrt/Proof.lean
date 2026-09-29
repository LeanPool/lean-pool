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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Sqrt.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.ModelSqrt.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Classification

/-!
# Correctness of compact finite square root

The executable descriptor-aware square-root kernels live in `Sqrt.Runtime`. This module proves
their agreement with the exact dyadic and unpacked-model specifications and installs the verified
compiler substitution.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteSqrt

/--
For a conventional IEEE descriptor, exact-dyadic square root agrees with the established unpacked
model applied to the original encoded value.
-/
theorem sqrtPositiveDyadic_eq_model_of_ieee
    {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (x : Model fmt) (value : Numerics.Dyadic)
    (hdecode : toDyadicOption x = some value)
    (hsign : value.negative = false) (hmantissa : value.significand ≠ 0) :
    sqrtPositiveDyadic fmt value.significand value.exponent =
      ofModel fmt
        (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt) (toModel x)) := by
  have hieeeDecode : ieeeToDyadicOption x = some value := by
    simpa [toDyadicOption, hfmt] using hdecode
  have hmodel :=
    toModel_eq_finite_of_ieeeToDyadicOption_eq_some
      x value.negative value.significand value.exponent hmantissa hieeeDecode
  simp [sqrtPositiveDyadic, hfmt, hmantissa, hmodel, hsign,
    NativeModelSqrt.sqrt_eq]

/-- Compact positive square root preserves the exact-dyadic specification. -/
theorem sqrtPositive_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    sqrtPositiveOption x =
      match toDyadicOption x with
      | none => none
      | some value =>
          if value.negative then
            none
          else if value.significand == 0 then
            none
          else
            some <| sqrtPositiveDyadic fmt value.significand value.exponent := by
  rw [FiniteKernel.toDyadic_eq_decode]
  cases hdecode : FiniteKernel.decodeOption x with
  | none => simp [sqrtPositiveOption, hdecode]
  | some value =>
      by_cases hsign : value.sign = true
      · by_cases hzero : value.mantissa = 0 <;>
          simp [sqrtPositiveOption, sqrtComponentsOption, hdecode, hsign,
            FiniteKernel.Components.toDyadic, hzero]
      · have hsignFalse : value.sign = false :=
          Bool.eq_false_of_not_eq_true hsign
        by_cases hzero : value.mantissa = 0
        · simp [sqrtPositiveOption, sqrtComponentsOption, hdecode, hsignFalse,
            FiniteKernel.Components.toDyadic, hzero]
        · simp [sqrtPositiveOption, sqrtComponentsOption, hdecode, hsignFalse,
            FiniteKernel.Components.toDyadic, hzero]

/-- The scalar-field square-root entry point preserves `sqrtPositiveOption`. -/
theorem sqrtPositiveRuntime_eq {fmt : FloatFormat} (x : Model fmt) :
    sqrtPositiveRuntimeOption x = sqrtPositiveOption x := by
  simp only [sqrtPositiveRuntimeOption, FiniteKernel.withFinite_eq]
  unfold sqrtPositiveOption sqrtFieldsOption sqrtComponentsOption
  cases FiniteKernel.decodeOption x <;>
    rfl

/--
On its positive finite contract, the optional scalar decoder returns the direct runtime result.
-/
theorem sqrtPositiveRuntime_eq_some {fmt : FloatFormat}
    (x : Model fmt)
    (hfinite : isFinite x = true)
    (hnonzero : isZero x = false)
    (hpositive : signBit x = false) :
    sqrtPositiveRuntimeOption x =
      some (sqrtPositiveRuntime x hfinite hnonzero hpositive) := by
  unfold sqrtPositiveRuntimeOption FiniteKernel.withFiniteOption sqrtPositiveRuntime
  by_cases hieee : fmt.isIEEE = true
  · simp only [hieee, ite_true]
    change
      (if expFieldImpl x == FloatFormat.expAllOnesNat fmt then
          none
        else
          sqrtFieldsOption fmt (signBitImpl x) (expFieldImpl x)
            (FiniteKernel.decodeMantissa fmt (expFieldImpl x) (fracFieldImpl x))) =
        some
          (sqrtPositiveDyadic fmt
            (FiniteKernel.decodeMantissa fmt (expFieldImpl x) (fracFieldImpl x))
            (FiniteKernel.dyadicExponent fmt (expFieldImpl x)))
    have hencoding : fmt.encoding = .ieee :=
      ((FloatFormat.isIEEE_eq_true_iff fmt).mp hieee).1
    have hexponent :
        expFieldImpl x ≠ FloatFormat.expAllOnesNat fmt := by
      rw [← expField_eq_expFieldImpl_apply]
      simpa [isFinite, hencoding, IEEE.isFinite] using hfinite
    split
    · rename_i heq
      exact (hexponent ((beq_iff_eq).1 heq)).elim
    · rw [signBit_eq_signBitImpl_apply] at hpositive
      rw [← expField_eq_expFieldImpl_apply x]
      rw [← fracField_eq_fracFieldImpl_apply x]
      unfold sqrtFieldsOption
      simp only [hpositive, Bool.false_eq_true, ite_false]
      by_cases hexponentZero : expField x = 0
      · have hfraction : fracField x ≠ 0 := by
          intro hfraction
          have hzero : isZero x = true := by
            simp [isZero, hencoding, IEEE.isZero, hexponentZero, hfraction]
          simp [hzero] at hnonzero
        simp [FiniteKernel.decodeMantissa, hexponentZero, hfraction]
      · have hmantissa : pow2 fmt.fracWidth + fracField x ≠ 0 := by
          have hpow : 0 < pow2 fmt.fracWidth := by
            simp [pow2_eq_two_pow]
          omega
        have hpowne : pow2 fmt.fracWidth ≠ 0 := by
          simp [pow2_eq_two_pow]
        simp [FiniteKernel.decodeMantissa, hexponentZero, hpowne]
  · simp only [hieee]
    unfold FiniteKernel.decodeOption
    simp only [hfinite, Bool.not_true, Bool.false_eq_true, ite_false]
    unfold sqrtFieldsOption
    simp only [hpositive, Bool.false_eq_true, ite_false]
    by_cases hexponentZero : expField x = 0
    · have hfraction : fracField x ≠ 0 := by
        intro hfraction
        have hzero : isZero x = true := by
          have hreconstruct := ofFields_signBit_expField_fracField x
          have hreconstructZero :
              ofFields fmt false 0 0 = x := by
            simpa [hpositive, hexponentZero, hfraction] using hreconstruct
          cases hencoding : fmt.encoding with
          | ieee | finiteMaxNaN | finite =>
              simp [isZero, hencoding, IEEE.isZero, hexponentZero, hfraction]
          | finiteUnsignedZero =>
              have hbits : x.bits = 0 := by
                simpa [posZero, ofNatBits, ofBits, FloatFormat.ofWordNat] using
                  (congrArg (fun value : Model fmt => value.bits)
                    hreconstructZero).symm
              simp [isZero, hencoding, hbits]
        simp [hzero] at hnonzero
      simp [FiniteKernel.decodeMantissa, hexponentZero, hfraction]
    · have hmantissa : pow2 fmt.fracWidth + fracField x ≠ 0 := by
        have hpow : 0 < pow2 fmt.fracWidth := by
          simp [pow2_eq_two_pow]
        omega
      have hpowne : pow2 fmt.fracWidth ≠ 0 := by
        simp [pow2_eq_two_pow]
      simp [FiniteKernel.decodeMantissa, hexponentZero, hpowne]

/--
The proof-guided runtime entry point computes square root from the exact dyadic represented by its
finite input.
-/
theorem sqrtPositiveRuntime_eq_finiteDyadic {fmt : FloatFormat}
    (x : Model fmt)
    (hfinite : isFinite x = true)
    (hnonzero : isZero x = false)
    (hpositive : signBit x = false) :
    sqrtPositiveRuntime x hfinite hnonzero hpositive =
      let value := finiteDyadic x hfinite
      sqrtPositiveDyadic fmt value.significand value.exponent := by
  obtain ⟨value, hdecode⟩ := exists_toDyadicOption_of_isFinite hfinite
  have hvalue : finiteDyadic x hfinite = value :=
    finiteDyadic_eq_of_toDyadic hfinite hdecode
  have hsign : value.negative = false :=
    (sign_eq_signBit_of_toDyadicOption_some hdecode).trans hpositive
  have hmantissa : value.significand ≠ 0 := by
    intro hzero
    have hzeroSource :=
      isZero_eq_true_of_toDyadicOption_some_of_mant_eq_zero hdecode hzero
    rw [hnonzero] at hzeroSource
    contradiction
  have hruntime :
      sqrtPositiveRuntimeOption x =
        some (sqrtPositiveDyadic fmt value.significand value.exponent) := by
    rw [sqrtPositiveRuntime_eq, sqrtPositive_eq_spec, hdecode]
    simp [hsign, hmantissa]
  rw [sqrtPositiveRuntime_eq_some x hfinite hnonzero hpositive] at hruntime
  have hresult :
      sqrtPositiveRuntime x hfinite hnonzero hpositive =
        sqrtPositiveDyadic fmt value.significand value.exponent :=
    Option.some.inj hruntime
  simpa [hvalue] using hresult

/-- Compile positive square root through the scalar decoder. -/
@[csimp] theorem sqrtPositive_eq_sqrtPositiveRuntime :
    @sqrtPositiveOption = @sqrtPositiveRuntimeOption := by
  funext fmt x
  exact (sqrtPositiveRuntime_eq x).symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteSqrt
