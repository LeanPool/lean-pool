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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Finite.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Core.Proof

import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Proof
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Sqrt.Proof

/-!
# Correctness of native finite decoding for one-word formats

The executable decoder and arithmetic entry points live in `Finite.Runtime`. Their extracted sign,
significand, and stored exponent agree with the format-generic decoder. Addition, fused
multiply-add, and positive square root then reuse the corresponding component kernels.

Keeping the bridge here avoids coupling every operation to storage masks and field shifts. Runtime
imports remain small, and later refinements reason about exact dyadics rather than raw words.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordFinite

open NativeSmallWord

/-- Native one-word decoding equals the width-generic compact decoder. -/
theorem decode_eq {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt) (x : Model fmt) :
    decodeOption x = FiniteKernel.decodeOption x := by
  rcases heligible with ⟨hieee, hwidth⟩
  let bits := NativeSmallWord.toWord x
  let exponent := NativeSmallWord.exponentField fmt bits
  let fraction := NativeSmallWord.fractionField fmt bits
  let allOnes := NativeSmallWord.exponentMask fmt
  have hexponent :
      exponent.toNat = Model.expField x := by
    simpa [exponent, bits] using
      NativeSmallWord.exponentField_toNat hwidth x
  have hfraction :
      fraction.toNat = Model.fracField x := by
    simpa [fraction, bits] using
      NativeSmallWord.fractionField_toNat hwidth x
  have hallOnes :
      allOnes.toNat = fmt.expAllOnesNat := by
    simpa [allOnes] using
      NativeSmallWord.exponentMask_toNat (fmt := fmt) hwidth
  have hsign :
      NativeSmallWord.signField fmt bits = Model.signBit x := by
    simpa [bits] using NativeSmallWord.signField_eq hwidth x
  have hencoding : fmt.encoding = .ieee :=
    ((FloatFormat.isIEEE_eq_true_iff fmt).mp hieee).1
  have hnonfinite :
      (!Model.isFinite x) =
        (Model.expField x == fmt.expAllOnesNat) := by
    simp [Model.isFinite, hencoding, Model.IEEE.isFinite, bne]
  unfold decodeOption FiniteKernel.decodeOption
  dsimp only
  rw [hnonfinite]
  change
    (if exponent == allOnes then
        (none : Option FiniteKernel.Components)
      else
        some {
          sign := NativeSmallWord.signField fmt bits
          exponent := exponent.toNat
          mantissa := (finiteMantissa fmt exponent fraction).toNat }) =
      if Model.expField x == fmt.expAllOnesNat then
        (none : Option FiniteKernel.Components)
      else
        some {
          sign := Model.signBit x
          exponent := Model.expField x
          mantissa :=
            if Model.expField x == 0 then
              Model.fracField x
            else
              Model.pow2 fmt.fracWidth + Model.fracField x }
  by_cases hexceptional : exponent = allOnes
  · have hgenericExceptional :
        Model.expField x = fmt.expAllOnesNat := by
      rw [← hexponent, ← hallOnes, hexceptional]
    simp [hexceptional, hgenericExceptional]
  · have hgenericFinite :
        Model.expField x ≠ fmt.expAllOnesNat := by
      intro h
      apply hexceptional
      apply UInt64.toNat_inj.mp
      rw [hexponent, hallOnes]
      exact h
    have hgenericAllOnesPositive : 0 < fmt.expAllOnesNat := by
      unfold FloatFormat.expAllOnesNat
      have hpow : 1 < 2 ^ fmt.expWidth :=
        Nat.one_lt_two_pow (by
          have hwidth := fmt.expWidth_ge_two
          omega)
      omega
    have hallOnesNonzero : allOnes ≠ 0 := by
      intro h
      have hnat := congrArg UInt64.toNat h
      rw [hallOnes] at hnat
      simp at hnat
      omega
    by_cases hexponentZero : exponent = 0
    · have hgenericZero :
          Model.expField x = 0 := by
        rw [← hexponent, hexponentZero]
        rfl
      have hzeroAllOnes : (0 : UInt64) ≠ allOnes :=
        Ne.symm hallOnesNonzero
      have hzeroGenericAllOnes : 0 ≠ fmt.expAllOnesNat :=
        (Nat.ne_of_gt hgenericAllOnesPositive).symm
      simp [hexponentZero, hgenericZero, hzeroAllOnes,
        hzeroGenericAllOnes, hfraction, hsign, finiteMantissa]
    · have hgenericNonzero :
          Model.expField x ≠ 0 := by
        intro h
        apply hexponentZero
        apply UInt64.toNat_inj.mp
        rw [hexponent]
        exact h
      have hmantissa :
          (finiteMantissa fmt exponent fraction).toNat =
            2 ^ fmt.fracWidth + Model.fracField x := by
        simpa [finiteMantissa, hexponentZero, exponent, fraction, bits] using
          NativeSmallWord.normalMantissa_toNat_of_width hwidth x
      rw [hsign, hexponent, hmantissa]
      simp [hexceptional, hgenericFinite, hgenericNonzero,
        Model.pow2_eq_two_pow]

/--
Native-storage finite addition equals the generic compact finite kernel.

The runtime names the compiled `addComponentsImpl`; `addComponentsImpl_eq` identifies it with the
exact `addComponents` used by `FiniteKernel.addOption`.
-/
theorem addFinite_eq {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt) (x y : Model fmt) :
    addFiniteOption x y = FiniteKernel.addOption x y := by
  unfold addFiniteOption FiniteKernel.addOption
  rw [decode_eq heligible x, decode_eq heligible y]
  cases FiniteKernel.decodeOption x <;> cases FiniteKernel.decodeOption y <;>
    simp [FiniteKernel.addComponentsImpl_eq]

/--
Native-storage finite FMA equals the generic compact finite kernel.

The runtime names the compiled `fmaComponentsImpl`; `fmaComponentsImpl_eq` identifies it with the
exact `fmaComponents` used by `FiniteKernel.fmaOption`.
-/
theorem fmaFinite_eq {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt)
    (x y z : Model fmt) :
    fmaFiniteOption x y z = FiniteKernel.fmaOption x y z := by
  unfold fmaFiniteOption FiniteKernel.fmaOption
  rw [decode_eq heligible x, decode_eq heligible y, decode_eq heligible z]
  cases FiniteKernel.decodeOption x <;> cases FiniteKernel.decodeOption y <;>
    cases FiniteKernel.decodeOption z <;> simp [FiniteKernel.fmaComponentsImpl_eq]

/-- Native-storage positive square root equals the generic compact finite kernel. -/
theorem sqrtPositive_eq {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt) (x : Model fmt) :
    sqrtPositiveOption x = FiniteSqrt.sqrtPositiveOption x := by
  unfold sqrtPositiveOption FiniteSqrt.sqrtPositiveOption
  rw [decode_eq heligible x]
  rfl

/--
The unchecked one-word positive square-root kernel agrees with the proof-guided generic kernel.
-/
theorem sqrtPositive_eq_runtime {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt)
    (x : Model fmt)
    (hfinite : isFinite x = true)
    (hnonzero : isZero x = false)
    (hpositive : signBit x = false) :
    sqrtPositive heligible x hfinite hnonzero hpositive =
      FiniteSqrt.sqrtPositiveRuntime x hfinite hnonzero hpositive := by
  rcases heligible with ⟨hieee, hwidth⟩
  let bits := NativeSmallWord.toWord x
  let exponent := NativeSmallWord.exponentField fmt bits
  let fraction := NativeSmallWord.fractionField fmt bits
  let mantissa := finiteMantissa fmt exponent fraction
  let components : FiniteKernel.Components := {
    sign := NativeSmallWord.signField fmt bits
    exponent := exponent.toNat
    mantissa := mantissa.toNat }
  have hencoding : fmt.encoding = .ieee :=
    ((FloatFormat.isIEEE_eq_true_iff fmt).mp hieee).1
  have hfieldFinite :
      expField x ≠ FloatFormat.expAllOnesNat fmt := by
    simpa [isFinite, hencoding, IEEE.isFinite] using hfinite
  have hexponent :
      exponent.toNat = expField x := by
    simpa [exponent, bits] using
      NativeSmallWord.exponentField_toNat hwidth x
  have hallOnes :
      (NativeSmallWord.exponentMask fmt).toNat =
        FloatFormat.expAllOnesNat fmt :=
    NativeSmallWord.exponentMask_toNat hwidth
  have hexceptional :
      exponent ≠ NativeSmallWord.exponentMask fmt := by
    intro heq
    apply hfieldFinite
    rw [← hexponent, ← hallOnes, heq]
  have hnativeDecode :
      decodeOption x = some components := by
    unfold decodeOption
    dsimp only
    rw [ite_eq_right (by simpa only [beq_iff_eq] using hexceptional)]
  have hgenericDecode :
      FiniteKernel.decodeOption x = some components :=
    (decode_eq ⟨hieee, hwidth⟩ x).symm.trans hnativeDecode
  have hdyadic :
      toDyadicOption x = some (components.toDyadic fmt) := by
    rw [FiniteKernel.toDyadic_eq_decode, hgenericDecode]
    rfl
  have hmantissa : components.mantissa ≠ 0 := by
    intro hzero
    have hzeroSource :=
      isZero_eq_true_of_toDyadicOption_some_of_mant_eq_zero hdyadic (by
        simpa using hzero)
    rw [hnonzero] at hzeroSource
    contradiction
  have hvalue :
      finiteDyadic x hfinite = components.toDyadic fmt :=
    finiteDyadic_eq_of_toDyadic hfinite hdyadic
  rw [FiniteSqrt.sqrtPositiveRuntime_eq_finiteDyadic]
  unfold sqrtPositive
  simp only
  rw [hvalue]
  simp [components, mantissa, exponent, fraction, bits, hmantissa,
    FiniteKernel.Components.toDyadic_exp_of_mantissa_ne_zero]

end Model.NativeSmallWordFinite
end FloatLib.Floats.Formats.BinaryInterchange
