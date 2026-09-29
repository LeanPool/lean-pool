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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Small.Div.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Quotient.Proof
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.NormalPair.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.QuotientRound.Proof

/-!
# Correctness of native one-word finite division

The one-word quotient kernel computes only cases whose normalized quotient and rounding evidence
fit its fixed-width budget. Every IEEE descriptor stored in one word meets this budget:
the sign and at least two exponent bits leave at most 61 fraction bits. The refinement relates its
logarithms, restoring quotient, guard/sticky information, and packed result to the complete
format-generic quotient rounder.

Under `NativeSmallWord.StorageEligible`, `divNormal_refines_of_storage` identifies every accepted
result with `FiniteKernel.divOption`. Declined inputs use the dispatcher's exact generic fallback.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordDiv

open FloatLib.Numerics.FixedWord.RestoringQuotient

private theorem encodedExponent_fit
    (fmt : FloatFormat) (hwidth : fmt.bitWidth ≤ 64)
    (exponent : Int)
    (hmin : fmt.ieeeMinNormalExponent ≤ exponent)
    (hmax : exponent ≤ Int.ofNat fmt.ieeeMaxNormalExponent) :
    Int.toNat (exponent + Int.ofNat fmt.bias) < 2 ^ 64 := by
  unfold FloatFormat.ieeeMinNormalExponent at hmin
  unfold FloatFormat.ieeeMaxNormalExponent at hmax
  have hexpWidth : fmt.expWidth ≤ 62 := by
    have hfracPos := fmt.fracWidth_pos
    unfold FloatFormat.bitWidth at hwidth
    omega
  have hpow :
      2 ^ fmt.expWidth ≤ 2 ^ 62 :=
    Nat.pow_le_pow_right (by decide) hexpWidth
  have hbias : fmt.bias < 2 ^ 62 :=
    (FloatFormat.bias_lt_pow_expWidth fmt).trans_le hpow
  have hnonnegative : 0 ≤ exponent + Int.ofNat fmt.bias := by
    omega
  have hbiasInt :
      Int.ofNat fmt.bias < Int.ofNat (2 ^ 62) :=
    Int.ofNat_lt.mpr hbias
  have hupper :
      exponent + Int.ofNat fmt.bias < Int.ofNat (2 ^ 63) := by
    calc
      exponent + Int.ofNat fmt.bias
          ≤ Int.ofNat fmt.bias + Int.ofNat fmt.bias :=
        by
          simpa [add_comm] using
            add_le_add_right hmax (Int.ofNat fmt.bias)
      _ < Int.ofNat (2 ^ 62) + Int.ofNat (2 ^ 62) :=
        add_lt_add hbiasInt hbiasInt
      _ = Int.ofNat (2 ^ 63) := by norm_num
  have htoNat :
      Int.toNat (exponent + Int.ofNat fmt.bias) < 2 ^ 63 := by
    rw [← Int.ofNat_lt]
    rw [Int.toNat_of_nonneg hnonnegative]
    exact hupper
  exact htoNat.trans (by norm_num)

/--
The one-word quotient rounder with the format's named normal exponent bounds in place of the
machine-word bias.

`roundNormalNativeOption` reads its bounds from `NativeSmallWord.biasInt` so that compiled code
performs no `Nat` shift per call; this proof-facing twin is the same computation stated with
`ieeeMinNormalExponent`, `ieeeMaxNormalExponent`, and `bias`, and `roundNormalNative_eq_bounds`
identifies the two for every one-word format.
-/
def roundNormalNativeBoundsOption (fmt : FloatFormat) (sign : Bool)
    (num den : UInt64) (exponent : Int) : Option (Model fmt) :=
  let rationalExponent :=
    floorLog2RatWord num den
  let totalExponent := rationalExponent + exponent
  if totalExponent < fmt.ieeeMinNormalExponent ||
      Int.ofNat fmt.ieeeMaxNormalExponent < totalExponent then
    none
  else
    let shift :=
      Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
    let roundedMantissa :=
      roundScaledQuotient num den shift
    let carry :=
      roundedMantissa == NativeSmallWord.carryBit fmt
    let normalizedExponent :=
      if carry then totalExponent + 1 else totalExponent
    if Int.ofNat fmt.ieeeMaxNormalExponent < normalizedExponent then
      none
    else
      let normalizedMantissa :=
        if carry then NativeSmallWord.hiddenBit fmt else roundedMantissa
      let encodedExponent :=
        UInt64.ofNat
          (Int.toNat (normalizedExponent + Int.ofNat fmt.bias))
      let fraction :=
        normalizedMantissa - NativeSmallWord.hiddenBit fmt
      some <| NativeSmallWord.ofWord <|
        NativeSmallWord.packFields fmt sign encodedExponent fraction

/-- The machine-word bias rounder is the rounder with the format's named exponent bounds. -/
theorem roundNormalNative_eq_bounds
    (fmt : FloatFormat) (hwidth : fmt.bitWidth ≤ 64)
    (sign : Bool) (num den : UInt64) (exponent : Int) :
    roundNormalNativeOption fmt sign num den exponent =
      roundNormalNativeBoundsOption fmt sign num den exponent := by
  unfold roundNormalNativeOption roundNormalNativeBoundsOption
  rw [NativeSmallWord.biasInt_eq hwidth]
  rfl

private theorem carryExponentFitsWord (fmt : FloatFormat) (hwidth : fmt.bitWidth ≤ 64)
    (exponent : Int) (hmin : fmt.ieeeMinNormalExponent ≤ exponent)
    (hmax : exponent < Int.ofNat fmt.ieeeMaxNormalExponent) :
    (exponent + 1 + Int.ofNat fmt.bias).toNat < 2 ^ 64 := by
  exact encodedExponent_fit fmt hwidth (exponent + 1) (by omega) (by omega)

private theorem quotientNativeCarryCases (fmt : FloatFormat) (hwidth : fmt.bitWidth ≤ 64)
  (hfracWidth : fmt.fracWidth ≤ 61) (sign : Bool) (num den : UInt64) (exponent : ℤ)
  (hnumZero : (num.toNat == 0) = false)
  (hdenZero : (den.toNat == 0) = false)
  (htotalMin : fmt.ieeeMinNormalExponent ≤ floorLog2RatWord num den + exponent)
  (htotalMax : floorLog2RatWord num den + exponent ≤ Int.ofNat fmt.ieeeMaxNormalExponent) :
  let shift := (Int.ofNat fmt.fracWidth - floorLog2RatWord num den).toNat;
  let nativeMantissa := roundScaledQuotient num den shift;
  let genericMantissa := Numerics.roundQuotientEven (num.toNat <<< shift) den.toNat;
  nativeMantissa.toNat = genericMantissa →
    (nativeMantissa = NativeSmallWord.carryBit fmt ↔ genericMantissa = pow2 (fmt.fracWidth + 1)) →
      2 ^ fmt.fracWidth ≤ genericMantissa ∧ genericMantissa ≤ 2 ^ (fmt.fracWidth + 1) →
        roundNormalNativeBoundsOption fmt sign num den exponent =
          FiniteQuotientRound.normalSpecOption fmt sign num.toNat den.toNat exponent := by
  intro shift nativeMantissa genericMantissa hmantissa hcarry hbounds
  have hnum : num ≠ 0 := by simpa [← UInt64.toNat_inj] using hnumZero
  have hden : den ≠ 0 := by simpa [← UInt64.toNat_inj] using hdenZero
  have hlow := not_lt_of_ge htotalMin
  have hhigh := not_lt_of_ge htotalMax
  unfold roundNormalNativeBoundsOption FiniteQuotientRound.normalSpecOption
  rw [← floorLog2RatWord_eq num den hnum hden]
  simp only [hlow, hhigh, decide_false, Bool.false_or]
  by_cases hnativeCarry :
      nativeMantissa = NativeSmallWord.carryBit fmt
  · have hgenericCarry := hcarry.mp hnativeCarry
    have hnativeCarryBool :
        (nativeMantissa == NativeSmallWord.carryBit fmt) = true := by
      simpa using hnativeCarry
    have hgenericCarryBool :
        (genericMantissa ==
          Model.pow2 (fmt.fracWidth + 1)) = true := by
      simpa using hgenericCarry
    simp only [shift, nativeMantissa, genericMantissa,
      hnativeCarryBool, hgenericCarryBool]
    simp only [Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_natCast, Order.lt_add_one_iff,
      UInt64.sub_self,
      hdenZero, hnumZero, Bool.or_self, pow2_eq_two_pow, tsub_self]
    split
    · rfl
    · have hencodedFit :
          Int.toNat
              (floorLog2RatWord num den + exponent +
                1 + Int.ofNat fmt.bias) < 2 ^ 64 := by
        exact carryExponentFitsWord fmt hwidth
          (floorLog2RatWord num den + exponent) (by omega)
          (by simpa only [Int.ofNat_eq_natCast] using
            lt_of_not_ge ‹¬(fmt.ieeeMaxNormalExponent : Int) ≤ floorLog2RatWord num den + exponent›)
      have hencodedWord : (UInt64.ofNat _).toNat = _ :=
        UInt64.toNat_ofNat_of_lt hencodedFit
      rw [NativeSmallWord.ofWord_packFields hwidth]
      change
        some
            (Model.ofFields fmt sign
              (UInt64.ofNat
                (Int.toNat
                  (floorLog2RatWord num den + exponent +
                    1 + Int.ofNat fmt.bias))).toNat
              (0 : UInt64).toNat) =
          some
            (Model.ofFields fmt sign
              (Int.toNat
                (floorLog2RatWord num den + exponent +
                  1 + Int.ofNat fmt.bias))
              0)
      simp only [hencodedWord, UInt64.toNat_zero]
  · have hgenericCarry :
        genericMantissa ≠ Model.pow2 (fmt.fracWidth + 1) :=
      (not_congr hcarry).mp hnativeCarry
    have hnativeCarryBool :
        (nativeMantissa == NativeSmallWord.carryBit fmt) = false := by
      simpa using hnativeCarry
    have hgenericCarryBool :
        (genericMantissa ==
          Model.pow2 (fmt.fracWidth + 1)) = false := by
      simpa using hgenericCarry
    have hbaseLe :
        NativeSmallWord.hiddenBit fmt ≤ nativeMantissa := by
      apply UInt64.le_iff_toNat_le.mpr
      rw [NativeSmallWord.hiddenBit_toNat_of_width fmt hwidth, hmantissa]
      exact hbounds.1
    have hfractionFit :
        genericMantissa - 2 ^ fmt.fracWidth < 2 ^ 64 := by
      have hupper : genericMantissa ≤ 2 ^ (fmt.fracWidth + 1) :=
        hbounds.2
      have hpow :
          2 ^ (fmt.fracWidth + 1) ≤ 2 ^ 63 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hfraction :
        nativeMantissa - NativeSmallWord.hiddenBit fmt =
          UInt64.ofNat
            (genericMantissa - 2 ^ fmt.fracWidth) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ hbaseLe,
        NativeSmallWord.hiddenBit_toNat_of_width fmt hwidth, hmantissa]
      exact (UInt64.toNat_ofNat_of_lt hfractionFit).symm
    simp only [shift, nativeMantissa, genericMantissa,
      hnativeCarryBool, hgenericCarryBool]
    simp only [Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_natCast, hdenZero, hnumZero,
      Bool.or_self,
      pow2_eq_two_pow]
    split
    · rfl
    · have hencodedFit :
          Int.toNat
              (floorLog2RatWord num den + exponent +
                Int.ofNat fmt.bias) < 2 ^ 64 := by
        exact encodedExponent_fit fmt hwidth
          (floorLog2RatWord num den + exponent)
          htotalMin htotalMax
      have hencodedWord : (UInt64.ofNat _).toNat = _ :=
        UInt64.toNat_ofNat_of_lt hencodedFit
      change
        some
            (NativeSmallWord.ofWord
              (NativeSmallWord.packFields fmt sign
                (UInt64.ofNat
                  (Int.toNat
                    (floorLog2RatWord num den + exponent +
                      Int.ofNat fmt.bias)))
                (nativeMantissa - NativeSmallWord.hiddenBit fmt))) =
          some
            (Model.ofFields fmt sign
              (Int.toNat
                (floorLog2RatWord num den + exponent +
                  Int.ofNat fmt.bias))
              (genericMantissa - 2 ^ fmt.fracWidth))
      rw [hfraction, NativeSmallWord.ofWord_packFields hwidth]
      rw [hencodedWord]
      congr 3
      exact UInt64.toNat_ofNat_of_lt hfractionFit

private theorem roundNormalNative_eq_spec
    (fmt : FloatFormat)
    (hwidth : fmt.bitWidth ≤ 64)
    (hfracWidth : fmt.fracWidth ≤ 61)
    (sign : Bool) (num den : UInt64) (exponent : Int)
    (hnum : num ≠ 0) (hden : den ≠ 0)
    (hnumFit : num.toNat < 2 ^ (fmt.fracWidth + 1))
    (hdenFit : den.toNat < 2 ^ (fmt.fracWidth + 1)) :
    roundNormalNativeOption fmt sign num den exponent =
      FiniteQuotientRound.normalSpecOption fmt sign
        num.toNat den.toNat exponent := by
  have hnumNat : num.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hnum
  have hdenNat : den.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hden
  have hnumZero : (num.toNat == 0) = false := by
    simp [hnumNat]
  have hdenZero : (den.toNat == 0) = false := by
    simp [hdenNat]
  have hfloor :=
    floorLog2RatWord_eq num den hnum hden
  have hshift :=
    NativeWordQuotient.normalShift_eq
      fmt num den hnum hnumFit
  have hdenFit63 : den.toNat < 2 ^ 63 := by
    have hpow :
        2 ^ (fmt.fracWidth + 1) ≤ 2 ^ 63 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    exact hdenFit.trans_le (hpow.trans (by norm_num))
  have hquotient :=
    roundScaledQuotient_toNat num den
      (Int.toNat
        (Int.ofNat fmt.fracWidth -
          floorLog2RatWord num den))
      hden hdenFit63
      (NativeWordQuotient.quotient_lt_two_pow_63
        fmt num den hnum hden hnumFit (by omega))
  rw [roundNormalNative_eq_bounds fmt hwidth]
  unfold roundNormalNativeBoundsOption FiniteQuotientRound.normalSpecOption
  rw [← hfloor]
  by_cases hlow :
      floorLog2RatWord num den + exponent <
        fmt.ieeeMinNormalExponent
  · by_cases hhigh :
        Int.ofNat fmt.ieeeMaxNormalExponent <
          floorLog2RatWord num den + exponent
    · simp [hlow, hnumZero, hdenZero]
    · simp [hlow, hnumZero, hdenZero]
  by_cases hhigh :
      Int.ofNat fmt.ieeeMaxNormalExponent <
        floorLog2RatWord num den + exponent
  · simp only [hnumZero, hdenZero]
    simp only [hlow, hhigh, decide_false, decide_true, Bool.false_or,
      Bool.or_true, ite_true]
    rfl
  simp only [hlow, hhigh, decide_false, Bool.false_or]
  have htotalMin :
      fmt.ieeeMinNormalExponent ≤
        floorLog2RatWord num den + exponent := by
    omega
  have htotalMax :
      floorLog2RatWord num den + exponent ≤
        Int.ofNat fmt.ieeeMaxNormalExponent := by
    omega
  let shift :=
    Int.toNat
      (Int.ofNat fmt.fracWidth -
        floorLog2RatWord num den)
  let nativeMantissa :=
    roundScaledQuotient num den shift
  let genericMantissa :=
    Numerics.roundQuotientEven
      (num.toNat <<< shift) den.toNat
  have hmantissa :
      nativeMantissa.toNat = genericMantissa := by
    simpa only [shift, nativeMantissa, genericMantissa] using hquotient
  have hcarry :
      nativeMantissa = NativeSmallWord.carryBit fmt ↔
        genericMantissa = Model.pow2 (fmt.fracWidth + 1) := by
    rw [← UInt64.toNat_inj, hmantissa,
      NativeSmallWord.carryBit_toNat_of_width fmt hwidth (by omega)]
    simp only [Model.pow2_eq_two_pow]
  have hbounds :
      2 ^ fmt.fracWidth ≤ genericMantissa ∧
        genericMantissa ≤ 2 ^ (fmt.fracWidth + 1) := by
    simpa only [shift, genericMantissa] using
      (NativeWordQuotient.roundedMantissa_bounds
        fmt num den hnum hden hnumFit)
  simpa only [roundNormalNativeBoundsOption, FiniteQuotientRound.normalSpecOption,
    ← hfloor, hlow, hhigh, decide_false, Bool.false_or] using
    quotientNativeCarryCases (fmt := fmt) (hwidth := hwidth) (hfracWidth := hfracWidth)
    (sign := sign) (num := num) (den := den) (exponent := exponent)
    (hnumZero := hnumZero) (hdenZero := hdenZero)
    (htotalMin := htotalMin) (htotalMax := htotalMax) hmantissa hcarry hbounds

/-- Restoring division refines the finite kernel for every descriptor within its word capacity. -/
theorem divNormal_refines_of_storage {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt)
    (x y result : Model fmt)
    (hresult : divNormalOption x y = some result) :
    FiniteKernel.divOption x y = some result := by
  rcases heligible with ⟨hieee, hwidth⟩
  have hfracWidth : fmt.fracWidth ≤ 61 := by
    have hexp := fmt.expWidth_ge_two
    unfold FloatFormat.bitWidth at hwidth
    omega
  rcases NativeNormalPair.view_of_success hieee hwidth x y
      (fun sign xExponent yExponent xMantissa yMantissa =>
        roundNormalNativeOption fmt sign xMantissa yMantissa
          (Int.ofNat (xExponent - 1).toNat -
            Int.ofNat (yExponent - 1).toNat))
      result (by simpa [divNormalOption] using hresult) with
    ⟨view, hround⟩
  let exponent :=
    Int.ofNat (view.xExponent - 1).toNat -
      Int.ofNat (view.yExponent - 1).toNat
  have hround' :
      roundNormalNativeOption fmt view.sign view.xMantissa
          view.yMantissa exponent =
        some result := by
    simpa [exponent] using hround
  have hxMantissaNatNe : view.xMantissa.toNat ≠ 0 := by
    exact Nat.ne_of_gt <|
      (Nat.two_pow_pos fmt.fracWidth).trans_le
        view.xMantissaBounds.1
  have hyMantissaNatNe : view.yMantissa.toNat ≠ 0 := by
    exact Nat.ne_of_gt <|
      (Nat.two_pow_pos fmt.fracWidth).trans_le
        view.yMantissaBounds.1
  have hxMantissaNe : view.xMantissa ≠ 0 := by
    intro h
    apply hxMantissaNatNe
    simp [h]
  have hyMantissaNe : view.yMantissa ≠ 0 := by
    intro h
    apply hyMantissaNatNe
    simp [h]
  have hspec :
      FiniteQuotientRound.normalSpecOption fmt view.sign
          view.xMantissa.toNat view.yMantissa.toNat exponent =
        some result := by
    rw [← roundNormalNative_eq_spec fmt hwidth hfracWidth
      view.sign view.xMantissa view.yMantissa exponent
      hxMantissaNe hyMantissaNe
      view.xMantissaBounds.2 view.yMantissaBounds.2]
    exact hround'
  have hfloor :=
    floorLog2RatWord_eq
      view.xMantissa view.yMantissa hxMantissaNe hyMantissaNe
  have hshift :=
    NativeWordQuotient.normalShift_eq
      fmt view.xMantissa view.yMantissa
      hxMantissaNe view.xMantissaBounds.2
  have hshiftNonnegative :
      0 ≤ Int.ofNat fmt.fracWidth -
        Numerics.RationalBinary.floorLog2
          view.xMantissa.toNat view.yMantissa.toNat := by
    rw [← hfloor, ← hshift]
    exact Int.natCast_nonneg _
  have hrounded :=
    FiniteQuotientRound.normalSpec_eq_roundRatScaled_of_some
      fmt hieee view.sign view.xMantissa.toNat
      view.yMantissa.toNat exponent result
      hshiftNonnegative hspec
  unfold FiniteKernel.divOption
  rw [view.xDecode, view.yDecode]
  unfold FiniteKernel.divComponents
  simp only [beq_iff_eq, hxMantissaNatNe, hyMantissaNatNe, ite_false]
  have hxOne : (1 : UInt64) ≤ view.xExponent :=
    UInt64.le_iff_toNat_le.mpr view.xExponentBounds.1
  have hyOne : (1 : UInt64) ≤ view.yExponent :=
    UInt64.le_iff_toNat_le.mpr view.yExponentBounds.1
  have hxScale :
      FiniteKernel.scale view.xExponent.toNat =
        (view.xExponent - 1).toNat := by
    unfold FiniteKernel.scale
    simp only [beq_iff_eq, view.xExponentBounds.1.ne', ite_false]
    exact (UInt64.toNat_sub_of_le view.xExponent 1 hxOne).symm
  have hyScale :
      FiniteKernel.scale view.yExponent.toNat =
        (view.yExponent - 1).toNat := by
    unfold FiniteKernel.scale
    simp only [beq_iff_eq, view.yExponentBounds.1.ne', ite_false]
    exact (UInt64.toNat_sub_of_le view.yExponent 1 hyOne).symm
  rw [hxScale, hyScale]
  rw [← view.sign_eq]
  change some (Model.roundRatScaled fmt view.sign
    view.xMantissa.toNat view.yMantissa.toNat exponent) = some result
  exact congrArg some hrounded.symm

/-- The shared small-word capacity is sufficient for native normal division. -/
theorem divNormal_refines {fmt : FloatFormat}
    (heligible : NativeSmallWord.Eligible fmt)
    (x y result : Model fmt)
    (hresult : divNormalOption x y = some result) :
    FiniteKernel.divOption x y = some result := by
  exact divNormal_refines_of_storage
    ⟨heligible.1, heligible.2.1⟩
    x y result hresult

end Model.NativeSmallWordDiv
end FloatLib.Floats.Formats.BinaryInterchange
