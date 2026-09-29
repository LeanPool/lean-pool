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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Correctness of normal finite quotient rounding

Optimized finite-division backends share `normalSpecOption` as their natural-number normal-result
specification. For conventional IEEE descriptors, `normalSpec_eq_roundRatScaled_of_some` proves
agreement with exact
nearest-even rational rounding when scaling the numerator requires a nonnegative left shift.
That shift bound is a caller obligation, not a check made by `normalSpecOption`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteQuotientRound

/--
Candidate specification for a normal finite quotient.

Zero inputs and exponents outside the supported normal range return `none`. Agreement with exact
rational rounding requires `fmt.isIEEE = true` and
`RationalBinary.floorLog2 num den ≤ Int.ofNat fmt.fracWidth`; the latter ensures that the numerator
scaling is a left shift. Dispatchers use the complete rational implementation when a candidate
declines.
-/
def normalSpecOption (fmt : FloatFormat) (sign : Bool)
    (num den : Nat) (exponent : Int) : Option (Model fmt) :=
  if den == 0 || num == 0 then
    none
  else
    let rationalExponent := Numerics.RationalBinary.floorLog2 num den
    let totalExponent := rationalExponent + exponent
    if totalExponent < fmt.ieeeMinNormalExponent ||
        Int.ofNat fmt.ieeeMaxNormalExponent < totalExponent then
      none
    else
      let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
      let roundedMantissa :=
        Numerics.roundQuotientEven (num <<< shift) den
      let carry := roundedMantissa == Model.pow2 (fmt.fracWidth + 1)
      let normalizedExponent :=
        if carry then totalExponent + 1 else totalExponent
      if Int.ofNat fmt.ieeeMaxNormalExponent < normalizedExponent then
        none
      else
        let normalizedMantissa :=
          if carry then Model.pow2 fmt.fracWidth else roundedMantissa
        some <| Model.ofFields fmt sign
          (Int.toNat (normalizedExponent + Int.ofNat fmt.bias))
          (normalizedMantissa - Model.pow2 fmt.fracWidth)

private theorem quotientRoundingCarryCases (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign :
  Bool)
  (num den : ℕ) (exponent : ℤ) (result : Model fmt)
  (hresult :
    (if (den == 0 || num == 0) = true then none
      else
        have rationalExponent := Numerics.RationalBinary.floorLog2 num den;
        have totalExponent := rationalExponent + exponent;
        if
            (decide (totalExponent < fmt.ieeeMinNormalExponent) ||
                decide (Int.ofNat fmt.ieeeMaxNormalExponent < totalExponent)) =
              true then
          none
        else
          have shift := (Int.ofNat fmt.fracWidth - rationalExponent).toNat;
          have roundedMantissa := Numerics.roundQuotientEven (num <<< shift) den;
          have carry := roundedMantissa == pow2 (fmt.fracWidth + 1);
          have normalizedExponent := if carry = true then totalExponent + 1 else totalExponent;
          if Int.ofNat fmt.ieeeMaxNormalExponent < normalizedExponent then none
          else
            have normalizedMantissa := if carry = true then pow2 fmt.fracWidth else roundedMantissa;
            some
              (ofFields fmt sign (normalizedExponent + Int.ofNat fmt.bias).toNat
                (normalizedMantissa - pow2 fmt.fracWidth))) =
      some result)
  :
  let rationalExponent := Numerics.RationalBinary.floorLog2 num den;
  let totalExponent := rationalExponent + exponent;
  ¬totalExponent < fmt.ieeeMinNormalExponent →
    ¬Int.ofNat fmt.ieeeMaxNormalExponent < totalExponent →
      Numerics.RationalBinary.scaleByPowerOfTwo num den
            (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 num den) =
          (num <<< (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 num den).toNat,
            den) →
        ¬Int.ofNat fmt.ieeeMaxNormalExponent < Numerics.RationalBinary.floorLog2 num den +
          exponent →
          ¬Numerics.RationalBinary.floorLog2 num den + exponent < -Int.ofNat
            fmt.normalMantissaExpOffset →
            ¬Numerics.RationalBinary.floorLog2 num den + exponent < fmt.ieeeMinNormalExponent →
              (den == 0) = false → (num == 0) = false → result = roundRatScaled fmt sign num den
                exponent := by
  intro rationalExponent totalExponent hlow hhigh
    hscaleRaw hhigh' hnotUnder' hnotSub' hdenBool hnumBool
  dsimp only [rationalExponent, totalExponent] at hlow hhigh
  simp only [hdenBool, hnumBool, Bool.false_or, Bool.false_eq_true, ite_false,
    hlow, hhigh, decide_false] at hresult
  simp only [Option.ite_none_left_eq_some, not_lt, Option.some.injEq] at hresult
  rw [Model.roundRatScaled, dite_eq_left hfmt]
  unfold Model.ieeeRoundRatScaled
  simp only [hdenBool, hnumBool, Bool.false_eq_true, ite_false, hhigh',
    hnotUnder', hnotSub']
  rw [hscaleRaw]
  rw [ite_eq_right (not_lt_of_ge hresult.1)]
  exact hresult.2.symm

/--
When numerator scaling is a nonnegative left shift, a successful normal quotient agrees with
conventional IEEE nearest-even rational rounding.
-/
theorem normalSpec_eq_roundRatScaled_of_some
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Bool) (num den : Nat) (exponent : Int) (result : Model fmt)
    (hshiftNonnegative :
      0 ≤ Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 num den)
    (hresult :
      normalSpecOption fmt sign num den exponent = some result) :
    result = Model.roundRatScaled fmt sign num den exponent := by
  unfold normalSpecOption at hresult
  by_cases hden : den = 0
  · simp [hden] at hresult
  by_cases hnum : num = 0
  · simp [hnum] at hresult
  let rationalExponent := Numerics.RationalBinary.floorLog2 num den
  let totalExponent := rationalExponent + exponent
  by_cases hlow : totalExponent < fmt.ieeeMinNormalExponent
  · simp [hden, hnum, rationalExponent, totalExponent, hlow] at hresult
  by_cases hhigh :
      Int.ofNat fmt.ieeeMaxNormalExponent < totalExponent
  · have hresult' := hresult
    simp only [Bool.or_eq_true, beq_iff_eq, hden, hnum, or_self, ↓reduceIte, hlow, decide_false,
      Int.ofNat_eq_natCast, Bool.false_or, decide_eq_true_eq, Option.ite_none_left_eq_some,
        not_lt, Option.some.injEq,
      totalExponent, rationalExponent] at hresult'
    exact (not_lt_of_ge hresult'.1 hhigh).elim
  have hbias := (fmt.isIEEE_eq_true_iff.mp hfmt).2
  have hnotUnder :
      ¬totalExponent < -Int.ofNat fmt.normalMantissaExpOffset := by
    have hoffset :
        Int.ofNat fmt.normalMantissaExpOffset =
          Int.ofNat fmt.bias + Int.ofNat fmt.fracWidth := by
      simp [FloatFormat.normalMantissaExpOffset, hbias]
    have hmin :
        fmt.ieeeMinNormalExponent = 1 - Int.ofNat fmt.bias := rfl
    have hfrac : 0 < Int.ofNat fmt.fracWidth := by
      simpa only [Int.ofNat_eq_natCast] using
        Int.natCast_pos.mpr fmt.fracWidth_pos
    intro hunder
    apply hlow
    rw [hmin]
    rw [hoffset] at hunder
    omega
  have hnotSub :
      ¬totalExponent < fmt.ieeeMinNormalExponent := hlow
  let shift :=
    Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
  let roundedMantissa :=
    Numerics.roundQuotientEven (num <<< shift) den
  let carry :=
    roundedMantissa == Model.pow2 (fmt.fracWidth + 1)
  let normalizedExponent :=
    if carry then totalExponent + 1 else totalExponent
  have hscale :
      Numerics.RationalBinary.scaleByPowerOfTwo num den
          (Int.ofNat fmt.fracWidth - rationalExponent) =
        (num <<< shift, den) := by
    have hshift :
        Int.ofNat shift =
          Int.ofNat fmt.fracWidth - rationalExponent := by
      apply Int.toNat_of_nonneg
      simpa only [rationalExponent] using hshiftNonnegative
    rw [← hshift]
    rfl
  have hscaleRaw :
      Numerics.RationalBinary.scaleByPowerOfTwo num den
          (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 num den) =
        (num <<< (Int.ofNat fmt.fracWidth -
          Numerics.RationalBinary.floorLog2 num den).toNat, den) := by
    simpa only [shift, rationalExponent] using hscale
  have hhigh' :
      ¬Int.ofNat fmt.ieeeMaxNormalExponent <
        Numerics.RationalBinary.floorLog2 num den + exponent := by
    simpa only [totalExponent, rationalExponent] using hhigh
  have hnotUnder' :
      ¬Numerics.RationalBinary.floorLog2 num den + exponent <
        -Int.ofNat fmt.normalMantissaExpOffset := by
    simpa only [totalExponent, rationalExponent] using hnotUnder
  have hnotSub' :
      ¬Numerics.RationalBinary.floorLog2 num den + exponent <
        fmt.ieeeMinNormalExponent := by
    simpa only [totalExponent, rationalExponent] using hnotSub
  have hdenBool : (den == 0) = false := by
    simp [hden]
  have hnumBool : (num == 0) = false := by
    simp [hnum]
  exact quotientRoundingCarryCases (fmt := fmt) (hfmt := hfmt) (sign := sign) (num := num)
    (den := den) (exponent := exponent) (result := result) (hresult := hresult)
    hlow hhigh hscaleRaw hhigh' hnotUnder' hnotSub' hdenBool hnumBool

end FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteQuotientRound
