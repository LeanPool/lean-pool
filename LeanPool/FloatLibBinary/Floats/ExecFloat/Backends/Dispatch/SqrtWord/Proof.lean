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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Dispatch.SqrtWord.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Sqrt.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Finite.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Spec.SquareRoot
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Sqrt.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Sqrt.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Packing
/-!
# Correctness of word-specialized square-root dispatch

Binary32 and binary64 have direct word kernels. Other descriptors use native one-word decoding
when eligible, or the generic square-root kernel. `word_eq_spec` proves that all these routes
agree with `Model.Spec.sqrt` for every input.

The fixed-format theorems include the NaN, infinity, signed-zero, and negative-input cases. The
positive finite cases reuse the corresponding kernel refinements. Runtime clients can import
`SqrtWord.Runtime` separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-! ## Direct binary32 kernel -/

namespace NativeBinary32

/-- The direct binary32 square root preserves the exact specification. -/
theorem sqrt_eq_spec (x : Value) :
    sqrt x = Model.Spec.sqrt x := by
  have hcanonical :
      ofUInt32 0x7fc00000 = Model.canonicalNaN FloatFormat.binary32 := by
    decide
  have hpositiveInfinity :
      ofUInt32 0x7f800000 = Model.posInf FloatFormat.binary32 := by
    decide
  have hexpAll :
      FloatFormat.expAllOnesNat FloatFormat.binary32 = 255 := by
    decide
  unfold NativeBinary32.sqrt
  dsimp only
  rw [expField_beq_allOnes, expField_beq_zero, fracField_beq_zero, signBit_eq]
  by_cases hexponentAllOnes : Model.expField x = 255
  · by_cases hfractionZero : Model.fracField x = 0
    · by_cases hsign : Model.signBit x = true
      · have hnan : Model.isNaN x = false := by
          change Model.IEEE.isNaN x = false
          simp [Model.IEEE.isNaN, hexpAll, hexponentAllOnes, hfractionZero]
        have hinf : Model.isInf x = true := by
          change Model.IEEE.isInf x = true
          simp [Model.IEEE.isInf, hexpAll, hexponentAllOnes, hfractionZero]
        simp [hexponentAllOnes, hfractionZero, hsign, Model.Spec.sqrt,
          Model.chooseNaN1, hnan, hinf, hcanonical]
      · have hsignFalse : Model.signBit x = false :=
          Bool.eq_false_of_not_eq_true hsign
        have hnan : Model.isNaN x = false := by
          change Model.IEEE.isNaN x = false
          simp [Model.IEEE.isNaN, hexpAll, hexponentAllOnes, hfractionZero]
        have hinf : Model.isInf x = true := by
          change Model.IEEE.isInf x = true
          simp [Model.IEEE.isInf, hexpAll, hexponentAllOnes, hfractionZero]
        simp only [hexponentAllOnes, hfractionZero, hsignFalse,
          beq_self_eq_true, ite_true]
        simp only [Bool.false_eq_true, ↓reduceIte, Spec.sqrt, chooseNaN1, hnan, hinf, hsignFalse,
          FloatFormat.isIEEE_binary32, nativeOverflow_eq_signedInf_of_isIEEE]
        rw [← ofUInt32_toUInt32 x, ← mkBits_fields (toUInt32 x)]
        rw [signBit_eq, expField_toNat, fracField_toNat, hsignFalse,
          hexponentAllOnes, hfractionZero]
        decide
    · have hnanIEEE : Model.IEEE.isNaN x = true := by
        simp [Model.IEEE.isNaN, hexpAll, hexponentAllOnes, hfractionZero]
      have hnan : Model.isNaN x = true := by
        change Model.IEEE.isNaN x = true
        exact hnanIEEE
      have hencoding :
          FloatFormat.binary32.encoding = .ieee := by
        rfl
      simp [hexponentAllOnes, hfractionZero, Model.Spec.sqrt,
        Model.chooseNaN1, Model.quietNaN, hnan, hnanIEEE,
        ofUInt32_or_quietBit, hencoding]
  · have hexponentNotAllOnes :
        Model.expField x ≠
          FloatFormat.expAllOnesNat FloatFormat.binary32 := by
      change Model.expField x ≠ 255
      exact hexponentAllOnes
    have hnan : Model.isNaN x = false := by
      change Model.IEEE.isNaN x = false
      simp [Model.IEEE.isNaN, hexpAll, hexponentAllOnes]
    have hinf : Model.isInf x = false := by
      change Model.IEEE.isInf x = false
      simp [Model.IEEE.isInf, hexpAll, hexponentAllOnes]
    by_cases hexponentZero : Model.expField x = 0
    · by_cases hfractionZero : Model.fracField x = 0
      · have hzero : Model.isZero x = true := by
          change Model.IEEE.isZero x = true
          simp [Model.IEEE.isZero, hexponentZero, hfractionZero]
        simp [hexponentZero, hfractionZero,
          Model.Spec.sqrt, Model.chooseNaN1, hnan, hinf, hzero]
      · by_cases hsign : Model.signBit x = true
        · have hzero : Model.isZero x = false := by
            change Model.IEEE.isZero x = false
            simp [Model.IEEE.isZero, hfractionZero]
          simp [hexponentZero, hfractionZero, hsign,
            Model.Spec.sqrt, Model.chooseNaN1, hnan, hinf, hzero,
            hcanonical]
        · have hsignFalse : Model.signBit x = false :=
            Bool.eq_false_of_not_eq_true hsign
          have hnonzero : Model.isZero x = false := by
            change Model.IEEE.isZero x = false
            simp [Model.IEEE.isZero, hfractionZero]
          have hfinitePolicy : Model.isFinite x = true := by
            change Model.IEEE.isFinite x = true
            exact (bne_iff_ne).2 hexponentNotAllOnes
          have hnative :=
            NativeBinary32.sqrt_eq_generic_of_positive_finite
              x hexponentNotAllOnes hnonzero hsignFalse
          have hpublic :=
            Model.Spec.sqrt_eq_model
              (fmt := FloatFormat.binary32) (by decide) x
              hfinitePolicy hnonzero hsignFalse
          calc
            _ = ofModel FloatFormat.binary32
                (Float.Model.UnpackedFloat.sqrt
                  (FloatFormat.toModel FloatFormat.binary32) (toModel x)) := by
              simpa [hexponentAllOnes, hexponentZero, hfractionZero, hsignFalse]
                using hnative
            _ = Model.Spec.sqrt x := hpublic.symm
    · by_cases hsign : Model.signBit x = true
      · have hzero : Model.isZero x = false := by
          change Model.IEEE.isZero x = false
          simp [Model.IEEE.isZero, hexponentZero]
        simp [hexponentAllOnes, hexponentZero, hsign, Model.Spec.sqrt,
          Model.chooseNaN1, hnan, hinf, hzero, hcanonical]
      · have hsignFalse : Model.signBit x = false :=
          Bool.eq_false_of_not_eq_true hsign
        have hnonzero : Model.isZero x = false := by
          change Model.IEEE.isZero x = false
          simp [Model.IEEE.isZero, hexponentZero]
        have hfinitePolicy : Model.isFinite x = true := by
          change Model.IEEE.isFinite x = true
          exact (bne_iff_ne).2 hexponentNotAllOnes
        have hnative :=
          NativeBinary32.sqrt_eq_generic_of_positive_finite
            x hexponentNotAllOnes hnonzero hsignFalse
        have hpublic :=
          Model.Spec.sqrt_eq_model
            (fmt := FloatFormat.binary32) (by decide) x
            hfinitePolicy hnonzero hsignFalse
        calc
          _ = ofModel FloatFormat.binary32
              (Float.Model.UnpackedFloat.sqrt
                (FloatFormat.toModel FloatFormat.binary32) (toModel x)) := by
            simpa [hexponentAllOnes, hexponentZero, hsignFalse] using hnative
          _ = Model.Spec.sqrt x := hpublic.symm

end NativeBinary32

/-! ## Direct binary64 kernel -/

namespace NativeBinary64

/-- The direct binary64 square root preserves the exact specification. -/
theorem sqrt_eq_spec (x : Value) :
    sqrt x = Model.Spec.sqrt x := by
  unfold sqrt Model.Spec.sqrt
  cases hnan : Model.chooseNaN1 x with
  | some nan =>
      simp
  | none =>
      have hnanFalse : Model.isNaN x = false := by
        unfold Model.chooseNaN1 at hnan
        cases h : Model.isNaN x <;> simp [h] at hnan ⊢
      cases hinf : Model.isInf x with
      | true =>
          simp
      | false =>
          simp only [Bool.false_eq_true, ite_false]
          cases hzero : Model.isZero x with
          | true =>
              simp
          | false =>
              simp only [Bool.false_eq_true, ite_false]
              cases hsign : Model.signBit x with
              | true =>
                  simp
              | false =>
                  simp only [Bool.false_eq_true, ite_false]
                  have hfinite :
                      Model.expField x ≠
                        FloatFormat.expAllOnesNat FloatFormat.binary64 := by
                    intro hexponent
                    by_cases hfraction : Model.fracField x = 0
                    · have hInfTrue : Model.IEEE.isInf x = true := by
                        simp [Model.IEEE.isInf, hexponent, hfraction]
                      have hInfPolicy : Model.isInf x = true := by
                        simpa [Model.isInf, FloatFormat.binary64] using hInfTrue
                      rw [hInfPolicy] at hinf
                      contradiction
                    · have hNaNTrue : Model.IEEE.isNaN x = true := by
                        simp [Model.IEEE.isNaN, hexponent, hfraction]
                      have hNaNPolicy : Model.isNaN x = true := by
                        simpa [Model.isNaN, FloatFormat.binary64] using hNaNTrue
                      rw [hNaNPolicy] at hnanFalse
                      contradiction
                  have hfinitePolicy : Model.isFinite x = true := by
                    change Model.IEEE.isFinite x = true
                    exact (bne_iff_ne).2 hfinite
                  have hnative :=
                    sqrt_eq_generic_of_positive_finite
                      x hfinite hzero hsign
                  have hpublic :=
                    Model.Spec.sqrt_eq_model
                      (fmt := FloatFormat.binary64) (by decide) x
                      hfinitePolicy hzero hsign
                  simp only [Model.Spec.sqrt, Model.chooseNaN1, hnanFalse,
                    Bool.false_eq_true, ite_false, hinf, hzero, hsign] at hpublic
                  rw [hnative, ← hpublic]

end NativeBinary64

/-! ## Descriptor-driven backend dispatch -/

namespace SqrtBackend

/-- The generic square-root dispatcher agrees with `Spec.sqrt` on every input. -/
theorem generic_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    generic x = Spec.sqrt x := by
  unfold generic
  by_cases hnan : chooseNaN1 x = none
  · rw [withNaNSelection_of_none _ _ hnan]
    unfold Spec.sqrt
    rw [hnan]
    simp only
    by_cases hinf : isInf x = true
    · simp [hinf]
    · have hinfFalse : isInf x = false :=
        Bool.eq_false_of_not_eq_true hinf
      rw [dite_eq_right hinf, ite_eq_right hinf]
      by_cases hzero : isZero x = true
      · simp [hzero]
      · have hzeroFalse : isZero x = false :=
          Bool.eq_false_of_not_eq_true hzero
        rw [dite_eq_right hzero, ite_eq_right hzero]
        by_cases hsignBit : signBit x = true
        · simp [hsignBit]
        · have hsignFalse : signBit x = false :=
            Bool.eq_false_of_not_eq_true hsignBit
          rw [dite_eq_right hsignBit, ite_eq_right hsignBit]
          have hnotNaN := (chooseNaN1_eq_none_iff x).1 hnan
          have hfinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false
              x hnotNaN hinfFalse
          obtain ⟨value, hdecode⟩ :=
            exists_toDyadicOption_of_isFinite hfinite
          have hvalue : finiteDyadic x hfinite = value :=
            finiteDyadic_eq_of_toDyadic hfinite hdecode
          rw [hdecode,
            FiniteSqrt.sqrtPositiveRuntime_eq_finiteDyadic]
          simp [hvalue]
  · have hselected : ∃ nan, chooseNaN1 x = some nan := by
      cases hchoose : chooseNaN1 x with
      | none => exact (hnan hchoose).elim
      | some nan => exact ⟨nan, rfl⟩
    obtain ⟨nan, hchoose⟩ := hselected
    rw [withNaNSelection_of_some _ _ nan hchoose]
    simp [Spec.sqrt, hchoose]

/-- Native one-word decoding preserves the compact generic square-root implementation. -/
theorem smallWord_eq_generic {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt) (x : Model fmt) :
    smallWord heligible x = generic x := by
  unfold smallWord generic
  apply congrArg (withNaNSelection (chooseNaN1 x))
  funext hnan
  dsimp only
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rw [NativeSmallWordFinite.sqrtPositive_eq_runtime]

/-- The width-specialized dispatcher preserves the logical format-generic square root. -/
theorem word_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    word x = Spec.sqrt x := by
  by_cases h32 : FloatFormat.IsBinary32 fmt
  · have hfmt := FloatFormat.eq_binary32_of_isBinary32 h32
    subst fmt
    unfold word
    split
    · rename_i h
      have heq :
          FloatFormat.eq_binary32_of_isBinary32 h =
            (rfl : FloatFormat.binary32 = FloatFormat.binary32) :=
        Subsingleton.elim _ _
      rw [heq]
      exact NativeBinary32.sqrt_eq_spec x
    · rename_i h
      exact (h FloatFormat.isBinary32_binary32).elim
  · by_cases h64 : FloatFormat.IsBinary64 fmt
    · have hfmt := FloatFormat.eq_binary64_of_isBinary64 h64
      subst fmt
      rw [show word x = NativeBinary64.sqrt x by
        simp [word, h32]]
      exact NativeBinary64.sqrt_eq_spec x
    · by_cases heligible : NativeSmallWord.StorageEligible fmt
      · rw [show word x = smallWord heligible x by
          simp [word, h32, h64, heligible]]
        exact (smallWord_eq_generic heligible x).trans (generic_eq_spec x)
      · simp [word, h32, h64, heligible, generic_eq_spec]

end SqrtBackend
end Model

end FloatLib.Floats.Formats.BinaryInterchange
