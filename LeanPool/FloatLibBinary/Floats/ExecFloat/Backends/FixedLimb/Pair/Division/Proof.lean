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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Division.Runtime
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.QuotientRound.Proof
import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Proof
import LeanPool.FloatLibBinary.Kernels.FixedWord.CertifiedDivision.Proof
import LeanPool.FloatLibBinary.Kernels.FixedWord.Difference.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Runtime

/-!
# Certified two-word normal division

The radix-`2^32` loop generates the first quotient candidate. A failed certificate selects the
proved
two-limb restoring result. The selected quotient is certified for every normalized input of an
eligible layout, so this backend has no candidate-failure branch. Exceptional values, subnormal
operands and results, and overflow boundaries retain the generic exact-rational backend. Start with
`divNormal_refines`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

open FloatLib.Numerics.FixedWord
open FloatLib.Numerics.FixedWord.CertifiedDivision

variable {fmt : FloatFormat}

private def roundNormalSpecOption (fmt : FloatFormat)
    (sign : Bool) (num den : Nat)
    (xExponent yExponent : Nat) : Option (Model fmt) :=
  if den == 0 || num == 0 then
    none
  else
    let shift := if den ≤ num then fmt.fracWidth else fmt.fracWidth + 1
    let rounded := Numerics.roundQuotientEven (num * 2 ^ shift) den
    let carry := rounded == pow2 (fmt.fracWidth + 1)
    let resultExponent : Int :=
      Int.ofNat xExponent - Int.ofNat yExponent +
        Int.ofNat (fmt.bias + fmt.fracWidth) - Int.ofNat shift + if carry then 1 else 0
    if resultExponent ≤ 0 || Int.ofNat fmt.expAllOnesNat ≤ resultExponent then
      none
    else
      let normalized := if carry then pow2 fmt.fracWidth else rounded
      some <| ofFields fmt sign resultExponent.toNat (normalized - pow2 fmt.fracWidth)

/-- The precision of an eligible descriptor is within the certified division range. -/
theorem Eligible.precision_bounds (h : Eligible fmt) :
    64 < fmt.fracWidth ∧ fmt.fracWidth ≤ 126 := by
  have := h.frac_le
  exact ⟨h.frac_gt, by omega⟩

private theorem certifiedQuotient_bounds (precision : Nat)
    (num den quotient remainder : UInt128)
    (shift : Nat)
    (hnum : 2 ^ precision ≤ num.toNat ∧ num.toNat < 2 ^ (precision + 1))
    (hden : 2 ^ precision ≤ den.toNat ∧ den.toNat < 2 ^ (precision + 1))
    (hshift :
      shift = if den.toNat ≤ num.toNat then precision else precision + 1)
    (hcertified :
      quotient.toNat * den.toNat + remainder.toNat =
          num.toNat * 2 ^ shift ∧
        remainder.toNat < den.toNat) :
    2 ^ precision ≤ quotient.toNat ∧ quotient.toNat < 2 ^ (precision + 1) := by
  have hpowDouble : 2 ^ (2 * precision + 1) = 2 ^ (precision + 1) * 2 ^ precision := by
    rw [← pow_add]
    congr 1
    omega
  have hproductLeScaled :
      quotient.toNat * den.toNat ≤ num.toNat * 2 ^ shift := by
    rw [← hcertified.1]
    exact Nat.le_add_right _ _
  have hsumUpperOf (hquotientLt : quotient.toNat < 2 ^ precision) :
      quotient.toNat * den.toNat + remainder.toNat < 2 ^ precision * den.toNat := by
    calc
      quotient.toNat * den.toNat + remainder.toNat <
          quotient.toNat * den.toNat + den.toNat :=
        Nat.add_lt_add_left hcertified.2 _
      _ = (quotient.toNat + 1) * den.toNat := by ring
      _ ≤ 2 ^ precision * den.toNat :=
        Nat.mul_le_mul_right den.toNat (Nat.succ_le_of_lt hquotientLt)
  by_cases hle : den.toNat ≤ num.toNat
  · have hshift' : shift = precision := by simp [hshift, hle]
    constructor
    · by_contra hnot
      have hsumUpper := hsumUpperOf (Nat.lt_of_not_ge hnot)
      have hscaledLower :
          2 ^ precision * den.toNat ≤ num.toNat * 2 ^ precision := by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_right (2 ^ precision) hle
      rw [hcertified.1, hshift'] at hsumUpper
      exact absurd (lt_of_lt_of_le hsumUpper hscaledLower) (lt_irrefl _)
    · by_contra hnot
      have hquotientLower : 2 ^ (precision + 1) ≤ quotient.toNat :=
        Nat.le_of_not_gt hnot
      have hproductLower :
          2 ^ (2 * precision + 1) ≤ quotient.toNat * den.toNat := by
        rw [hpowDouble]
        exact Nat.mul_le_mul hquotientLower hden.1
      have hscaledUpper : num.toNat * 2 ^ precision < 2 ^ (2 * precision + 1) := by
        rw [hpowDouble]
        exact Nat.mul_lt_mul_of_pos_right hnum.2 (Nat.two_pow_pos _)
      rw [hshift'] at hproductLeScaled
      exact absurd (lt_of_le_of_lt (hproductLower.trans hproductLeScaled) hscaledUpper)
        (lt_irrefl _)
  · have hnumLt : num.toNat < den.toNat := Nat.lt_of_not_ge hle
    have hshift' : shift = precision + 1 := by simp [hshift, hle]
    constructor
    · by_contra hnot
      have hsumUpper := hsumUpperOf (Nat.lt_of_not_ge hnot)
      have hdenUpper : 2 ^ precision * den.toNat < 2 ^ (2 * precision + 1) := by
        rw [hpowDouble, Nat.mul_comm (2 ^ (precision + 1))]
        exact Nat.mul_lt_mul_of_pos_left hden.2 (Nat.two_pow_pos _)
      have hscaledLower : 2 ^ (2 * precision + 1) ≤ num.toNat * 2 ^ (precision + 1) := by
        rw [hpowDouble, Nat.mul_comm (2 ^ (precision + 1))]
        exact Nat.mul_le_mul_right (2 ^ (precision + 1)) hnum.1
      rw [hcertified.1, hshift'] at hsumUpper
      exact absurd (lt_of_le_of_lt hscaledLower (hsumUpper.trans hdenUpper)) (lt_irrefl _)
    · by_contra hnot
      have hquotientLower : 2 ^ (precision + 1) ≤ quotient.toNat :=
        Nat.le_of_not_gt hnot
      have hproductLower :
          2 ^ (precision + 1) * den.toNat ≤ quotient.toNat * den.toNat :=
        Nat.mul_le_mul_right den.toNat hquotientLower
      have hscaledUpper :
          num.toNat * 2 ^ (precision + 1) < 2 ^ (precision + 1) * den.toNat := by
        rw [Nat.mul_comm (2 ^ (precision + 1))]
        exact Nat.mul_lt_mul_of_pos_right hnumLt (Nat.two_pow_pos _)
      rw [hshift'] at hproductLeScaled
      exact absurd (lt_of_le_of_lt (hproductLower.trans hproductLeScaled) hscaledUpper)
        (lt_irrefl _)

private theorem candidateShift_eq (num den : UInt128) :
    (if UInt128.less num den then CandidateShift.extra else CandidateShift.exact) =
      if den.toNat ≤ num.toNat then CandidateShift.exact else CandidateShift.extra := by
  by_cases hle : den.toNat ≤ num.toNat
  · have hless : UInt128.less num den = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact (Nat.not_lt_of_ge hle) ((UInt128.less_eq_true_iff num den).1 htrue)
    simp [hless, hle]
  · have hless : UInt128.less num den = true :=
      (UInt128.less_eq_true_iff num den).2 (Nat.lt_of_not_ge hle)
    simp [hless, hle]

private theorem checkedRound_facts (h : Eligible fmt)
    (num den : UInt128) (candidateShift : CandidateShift)
    (shift : Nat) (rounded : UInt128)
    (hnum : 2 ^ fmt.fracWidth ≤ num.toNat ∧ num.toNat < 2 ^ (fmt.fracWidth + 1))
    (hden : 2 ^ fmt.fracWidth ≤ den.toNat ∧ den.toNat < 2 ^ (fmt.fracWidth + 1))
    (hcandidateShift :
      candidateShift =
        if den.toNat ≤ num.toNat then CandidateShift.exact else CandidateShift.extra)
    (hshift : shift = if den.toNat ≤ num.toNat then fmt.fracWidth else fmt.fracWidth + 1)
    (hshiftCandidate : shift = candidateShift.toNat fmt.fracWidth)
    (hroundedDef :
      rounded =
        roundQuotient den
          (checkedCandidate fmt.fracWidth num den candidateShift).quotient
          (checkedCandidate fmt.fracWidth num den candidateShift).remainder) :
    rounded.toNat =
        Numerics.roundQuotientEven (num.toNat * 2 ^ shift) den.toNat ∧
      2 ^ fmt.fracWidth ≤ rounded.toNat ∧ rounded.toNat ≤ 2 ^ (fmt.fracWidth + 1) := by
  have hfracLe := h.frac_le
  let checked := checkedCandidate fmt.fracWidth num den candidateShift
  let quotient := checked.quotient
  let remainder := checked.remainder
  have hroundedDef' : rounded = roundQuotient den quotient remainder := by
    simpa only [quotient, remainder, checked] using hroundedDef
  have hcertifiedRaw :=
    checkedCandidate_sound fmt.fracWidth h.precision_bounds num den candidateShift
      hnum hden hcandidateShift
  have hcertified :
      quotient.toNat * den.toNat + remainder.toNat = num.toNat * 2 ^ shift ∧
        remainder.toNat < den.toNat := by
    simpa only [quotient, remainder, checked, ← hshiftCandidate] using hcertifiedRaw
  have hquotientBounds :=
    certifiedQuotient_bounds fmt.fracWidth num den quotient remainder shift
      hnum hden hshift hcertified
  have hpowSucc : 2 ^ (fmt.fracWidth + 1) ≤ 2 ^ 126 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hdenFit : den.toNat < 2 ^ 127 :=
    lt_of_lt_of_le hden.2 (hpowSucc.trans (by norm_num))
  have hquotientFit : quotient.toNat + 1 < 2 ^ 128 := by
    have hcapacity : 2 ^ 126 + 1 < 2 ^ 128 := by norm_num
    omega
  have hrounded :
      rounded.toNat = Numerics.roundQuotientEven (num.toNat * 2 ^ shift) den.toNat := by
    rw [hroundedDef']
    exact roundQuotient_toNat den quotient remainder (num.toNat * 2 ^ shift)
      hdenFit hcertified.1 hcertified.2 hquotientFit
  have hroundedCases :
      rounded.toNat = quotient.toNat ∨ rounded.toNat = quotient.toNat + 1 := by
    rw [hroundedDef']
    exact roundQuotient_toNat_eq_or den quotient remainder hquotientFit
  refine ⟨hrounded, ?_⟩
  rcases hroundedCases with hroundedEq | hroundedEq <;>
    rw [hroundedEq] <;> omega

private theorem roundNormalSpec_eq_some_of_packed (h : Eligible fmt)
    (sign : Bool) (num den xExponent yExponent shift : Nat)
    (rounded : UInt128)
    (carry : Bool) (resultExponent : Int) (result : Model fmt)
    (hnum : 2 ^ fmt.fracWidth ≤ num)
    (hden : 2 ^ fmt.fracWidth ≤ den)
    (hshift : shift = if den ≤ num then fmt.fracWidth else fmt.fracWidth + 1)
    (hrounded :
      rounded.toNat = Numerics.roundQuotientEven (num * 2 ^ shift) den)
    (hroundedBounds :
      2 ^ fmt.fracWidth ≤ rounded.toNat ∧ rounded.toNat ≤ 2 ^ (fmt.fracWidth + 1))
    (hcarry :
      carry = true ↔
        Numerics.roundQuotientEven (num * 2 ^ shift) den = pow2 (fmt.fracWidth + 1))
    (hresultExponent :
      resultExponent =
        Int.ofNat xExponent - Int.ofNat yExponent +
          Int.ofNat (fmt.bias + fmt.fracWidth) - Int.ofNat shift + if carry then 1 else 0)
    (hresultRange : 0 < resultExponent ∧ resultExponent < Int.ofNat fmt.expAllOnesNat)
    (hpack :
      packNormal fmt sign (UInt64.ofNat resultExponent.toNat)
          (normalizeCarry fmt carry rounded) =
        result) :
    roundNormalSpecOption fmt sign num den xExponent yExponent = some result := by
  have hallOnes := fmt.expAllOnesNat_eq_two_mul_bias_add_one
  have hbias := h.bias_lt
  have hexpWidth := fmt.two_pow_expWidth_eq_two_mul_bias_add_two
  have hresultExponentCast : ((resultExponent.toNat : Nat) : Int) = resultExponent :=
    Int.toNat_of_nonneg (le_of_lt hresultRange.1)
  have hresultExponentNatUpper : resultExponent.toNat < 2 ^ fmt.expWidth := by
    rw [hexpWidth]
    have hlt := hresultRange.2
    rw [hallOnes] at hlt
    simp only [Int.ofNat_eq_natCast] at hlt
    push_cast at hlt
    omega
  have hresultLt : resultExponent < (fmt.expAllOnesNat : Int) := by
    simpa [Int.ofNat_eq_natCast] using hresultRange.2
  have hresultExponentToNat :
      (UInt64.ofNat resultExponent.toNat).toNat = resultExponent.toNat := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    have hpow : 2 ^ fmt.expWidth ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) h.exp_le
    calc
      resultExponent.toNat < 2 ^ fmt.expWidth := hresultExponentNatUpper
      _ ≤ 2 ^ 62 := hpow
      _ < 2 ^ 64 := by norm_num
  have hresultExponentWordUpper :
      (UInt64.ofNat resultExponent.toNat).toNat < 2 ^ fmt.expWidth := by
    rw [hresultExponentToNat]
    exact hresultExponentNatUpper
  unfold roundNormalSpecOption
  have hnumZero : num ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hnum)
  have hdenZero : den ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hden)
  simp only [beq_iff_eq]
  rw [← hshift]
  rw [← hrounded]
  have hresultExponentPositive : ¬resultExponent ≤ 0 := by omega
  have hresultExponentBelowAll : ¬Int.ofNat fmt.expAllOnesNat ≤ resultExponent := by
    intro hle
    exact absurd (lt_of_le_of_lt hle hresultRange.2) (lt_irrefl _)
  by_cases hcarryTrue : carry = true
  · have hroundedCarry : rounded.toNat = pow2 (fmt.fracWidth + 1) :=
      hrounded.trans (hcarry.mp hcarryTrue)
    have hresultPack :
        packNormal fmt sign (UInt64.ofNat resultExponent.toNat) (implicitMantissa fmt) =
          result := by
      simpa only [normalizeCarry, hcarryTrue, ite_true] using hpack
    simp only [hroundedCarry, ite_true]
    have hresultExponentCarry :
        Int.ofNat xExponent - Int.ofNat yExponent +
            Int.ofNat (fmt.bias + fmt.fracWidth) - Int.ofNat shift + 1 =
          resultExponent := by
      simpa [hcarryTrue] using hresultExponent.symm
    have hpackCanonical :=
      packNormal_eq_ofFields h sign (UInt64.ofNat resultExponent.toNat) (implicitMantissa fmt)
        hresultExponentWordUpper
        (by rw [implicitMantissa_toNat h])
        (by
          rw [implicitMantissa_toNat h]
          exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
    rw [hresultExponentToNat, implicitMantissa_toNat h, pow2_eq_two_pow, Nat.sub_self]
      at hpackCanonical
    have hcanonicalResult :
        ofFields fmt sign resultExponent.toNat 0 = result :=
      hpackCanonical.symm.trans hresultPack
    rw [hresultExponentCarry]
    simpa [hnumZero, hdenZero, hresultExponentPositive, hresultLt,
      pow2_eq_two_pow] using congrArg some hcanonicalResult
  · have hcarryFalse : carry = false := Bool.eq_false_iff.mpr hcarryTrue
    have hspecNe :
        Numerics.roundQuotientEven (num * 2 ^ shift) den ≠ pow2 (fmt.fracWidth + 1) :=
      (not_congr hcarry).mp hcarryTrue
    have hroundedNe : rounded.toNat ≠ pow2 (fmt.fracWidth + 1) := by
      simpa only [hrounded] using hspecNe
    have hresultPack :
        packNormal fmt sign (UInt64.ofNat resultExponent.toNat) rounded = result := by
      simpa [normalizeCarry, hcarryFalse] using hpack
    simp only [hroundedNe, ite_false]
    have hroundedUpper : rounded.toNat < 2 ^ (fmt.fracWidth + 1) := by
      rw [pow2_eq_two_pow] at hroundedNe
      exact lt_of_le_of_ne hroundedBounds.2 hroundedNe
    have hresultExponentNoCarry :
        Int.ofNat xExponent - Int.ofNat yExponent +
            Int.ofNat (fmt.bias + fmt.fracWidth) - Int.ofNat shift + 0 =
          resultExponent := by
      simpa [hcarryFalse] using hresultExponent.symm
    have hpackCanonical :=
      packNormal_eq_ofFields h sign (UInt64.ofNat resultExponent.toNat) rounded
        hresultExponentWordUpper hroundedBounds.1 hroundedUpper
    rw [hresultExponentToNat] at hpackCanonical
    have hcanonicalResult :
        ofFields fmt sign resultExponent.toNat (rounded.toNat - pow2 fmt.fracWidth) =
          result :=
      hpackCanonical.symm.trans hresultPack
    rw [hresultExponentNoCarry]
    simpa [hnumZero, hdenZero, hresultExponentPositive, hresultLt] using
      congrArg some hcanonicalResult

private structure AcceptedNormalDivision (fmt : FloatFormat)
    (xExponent yExponent : UInt64)
    (totalExponent resultExponent : Int)
    (sign : Bool)
    (rounded : UInt128)
    (carry : Bool) (result : Model fmt) : Prop where
  xExponent_ne_zero : xExponent ≠ 0
  xExponent_ne_allOnes : xExponent ≠ expAllOnes fmt
  yExponent_ne_zero : yExponent ≠ 0
  yExponent_ne_allOnes : yExponent ≠ expAllOnes fmt
  minimumExponent : ¬totalExponent < fmt.ieeeMinNormalExponent
  resultExponent_inRange : 0 < resultExponent ∧ resultExponent < Int.ofNat fmt.expAllOnesNat
  packed_eq :
    packNormal fmt sign (UInt64.ofNat resultExponent.toNat)
        (normalizeCarry fmt carry rounded) =
      result

private theorem divNormal_accepted
    (x y result : Model fmt)
    (hresult : divNormalOption x y = some result) :
    let xWords := toWords x
    let yWords := toWords y
    let xExponent := expField fmt xWords.hi
    let yExponent := expField fmt yWords.hi
    let num := normalMantissa fmt (fracHigh fmt xWords.hi) xWords.lo
    let den := normalMantissa fmt (fracHigh fmt yWords.hi) yWords.lo
    let less := UInt128.less num den
    let rationalExponent : Int := if less then -1 else 0
    let totalExponent :=
      rationalExponent + (Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat)
    let candidateShift : CandidateShift := if less then .extra else .exact
    let shift := candidateShift.toNat fmt.fracWidth
    let checked := checkedCandidate fmt.fracWidth num den candidateShift
    let rounded := roundQuotient den checked.quotient checked.remainder
    let carry := isCarry fmt rounded
    let resultExponent : Int :=
      Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat +
        Int.ofNat (fmt.bias + fmt.fracWidth) - Int.ofNat shift + if carry then 1 else 0
    AcceptedNormalDivision fmt xExponent yExponent totalExponent resultExponent
      (Bool.xor (signBit fmt xWords.hi) (signBit fmt yWords.hi))
      rounded carry result := by
  let xWords := toWords x
  let yWords := toWords y
  let xExponent := expField fmt xWords.hi
  let yExponent := expField fmt yWords.hi
  let num := normalMantissa fmt (fracHigh fmt xWords.hi) xWords.lo
  let den := normalMantissa fmt (fracHigh fmt yWords.hi) yWords.lo
  let less := UInt128.less num den
  let rationalExponent : Int := if less then -1 else 0
  let totalExponent :=
    rationalExponent + (Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat)
  let candidateShift : CandidateShift := if less then .extra else .exact
  let shift := candidateShift.toNat fmt.fracWidth
  let checked := checkedCandidate fmt.fracWidth num den candidateShift
  let rounded := roundQuotient den checked.quotient checked.remainder
  let carry := isCarry fmt rounded
  let resultExponent : Int :=
    Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat +
      Int.ofNat (fmt.bias + fmt.fracWidth) - Int.ofNat shift + if carry then 1 else 0
  change
    AcceptedNormalDivision fmt xExponent yExponent totalExponent resultExponent
      (Bool.xor (signBit fmt xWords.hi) (signBit fmt yWords.hi))
      rounded carry result
  by_cases hxZero : xExponent = 0
  · simp [divNormalOption, xWords, xExponent, hxZero] at hresult
  by_cases hxAll : xExponent = expAllOnes fmt
  · simp [divNormalOption, xWords, xExponent, hxAll] at hresult
  by_cases hyZero : yExponent = 0
  · simp [divNormalOption, yWords, yExponent, hyZero] at hresult
  by_cases hyAll : yExponent = expAllOnes fmt
  · simp [divNormalOption, yWords, yExponent, hyAll] at hresult
  have hroute :
      ¬totalExponent < fmt.ieeeMinNormalExponent ∧
        ((0 < resultExponent ∧ resultExponent < Int.ofNat fmt.expAllOnesNat) ∧
          packNormal fmt
              (Bool.xor (signBit fmt xWords.hi) (signBit fmt yWords.hi))
              (UInt64.ofNat resultExponent.toNat)
              (normalizeCarry fmt carry rounded) =
            result) := by
    simpa [divNormalOption, xWords, yWords, xExponent, yExponent,
      num, den, less, rationalExponent, totalExponent, candidateShift, shift,
      checked, rounded, carry, resultExponent,
      hxZero, hxAll, hyZero, hyAll, Bool.not_eq_true] using hresult
  exact
    { xExponent_ne_zero := hxZero
      xExponent_ne_allOnes := hxAll
      yExponent_ne_zero := hyZero
      yExponent_ne_allOnes := hyAll
      minimumExponent := hroute.1
      resultExponent_inRange := hroute.2.1
      packed_eq := hroute.2.2 }

private structure CertifiedNormalRound (fmt : FloatFormat)
    (num den : UInt128)
    (shift : Nat) (rounded : UInt128)
    (carry : Bool) : Prop where
  shift_eq : shift = if den.toNat ≤ num.toNat then fmt.fracWidth else fmt.fracWidth + 1
  rounded_eq :
    rounded.toNat = Numerics.roundQuotientEven (num.toNat * 2 ^ shift) den.toNat
  rounded_bounds :
    2 ^ fmt.fracWidth ≤ rounded.toNat ∧ rounded.toNat ≤ 2 ^ (fmt.fracWidth + 1)
  carry_eq :
    carry = true ↔
      Numerics.roundQuotientEven (num.toNat * 2 ^ shift) den.toNat = pow2 (fmt.fracWidth + 1)

private theorem candidateShift_toNat_eq (fmt : FloatFormat)
    (num den : UInt128) (candidateShift : CandidateShift) (shift : Nat)
    (hcandidateShift :
      candidateShift =
        if den.toNat ≤ num.toNat then CandidateShift.exact else CandidateShift.extra)
    (hshiftCandidate : shift = candidateShift.toNat fmt.fracWidth) :
    shift = if den.toNat ≤ num.toNat then fmt.fracWidth else fmt.fracWidth + 1 := by
  by_cases hle : den.toNat ≤ num.toNat
  · have hc : candidateShift = CandidateShift.exact := by
      simpa only [hle, ite_true] using hcandidateShift
    rw [hshiftCandidate, hc, ite_eq_left hle]
    rfl
  · have hc : candidateShift = CandidateShift.extra := by
      simpa only [hle, ite_false] using hcandidateShift
    rw [hshiftCandidate, hc, ite_eq_right hle]
    rfl

private theorem carry_eq_of_rounded_eq (h : Eligible fmt)
    (num den : UInt128) (shift : Nat) (rounded : UInt128) (carry : Bool)
    (hrounded :
      rounded.toNat = Numerics.roundQuotientEven (num.toNat * 2 ^ shift) den.toNat)
    (hcarryDef : carry = isCarry fmt rounded) :
    carry = true ↔
      Numerics.roundQuotientEven (num.toNat * 2 ^ shift) den.toNat =
        pow2 (fmt.fracWidth + 1) := by
  rw [hcarryDef, isCarry_iff h rounded, hrounded]

private theorem certifiedNormalRound_of_candidate (h : Eligible fmt)
    (num den : UInt128) (candidateShift : CandidateShift)
    (shift : Nat) (rounded : UInt128) (carry : Bool)
    (hnum : 2 ^ fmt.fracWidth ≤ num.toNat ∧ num.toNat < 2 ^ (fmt.fracWidth + 1))
    (hden : 2 ^ fmt.fracWidth ≤ den.toNat ∧ den.toNat < 2 ^ (fmt.fracWidth + 1))
    (hcandidateShift :
      candidateShift =
        if den.toNat ≤ num.toNat then CandidateShift.exact else CandidateShift.extra)
    (hshiftCandidate : shift = candidateShift.toNat fmt.fracWidth)
    (hroundedDef :
      rounded =
        roundQuotient den
          (checkedCandidate fmt.fracWidth num den candidateShift).quotient
          (checkedCandidate fmt.fracWidth num den candidateShift).remainder)
    (hcarryDef : carry = isCarry fmt rounded) :
    CertifiedNormalRound fmt num den shift rounded carry := by
  have hshift :=
    candidateShift_toNat_eq fmt num den candidateShift shift hcandidateShift hshiftCandidate
  have hroundFacts :=
    checkedRound_facts h num den candidateShift shift rounded hnum hden
      hcandidateShift hshift hshiftCandidate hroundedDef
  exact
    { shift_eq := hshift
      rounded_eq := hroundFacts.1
      rounded_bounds := hroundFacts.2
      carry_eq :=
        carry_eq_of_rounded_eq h num den shift rounded carry hroundFacts.1 hcarryDef }

private theorem roundNormalSpec_of_accepted (h : Eligible fmt)
    (num den : UInt128) (xExponent yExponent : UInt64)
    (shift : Nat) (rounded : UInt128)
    (carry : Bool) (totalExponent resultExponent : Int)
    (sign : Bool) (result : Model fmt)
    (hnum : 2 ^ fmt.fracWidth ≤ num.toNat)
    (hden : 2 ^ fmt.fracWidth ≤ den.toNat)
    (hround : CertifiedNormalRound fmt num den shift rounded carry)
    (hresultExponentDef :
      resultExponent =
        Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat +
          Int.ofNat (fmt.bias + fmt.fracWidth) - Int.ofNat shift + if carry then 1 else 0)
    (haccepted :
      AcceptedNormalDivision fmt xExponent yExponent totalExponent resultExponent
        sign rounded carry result) :
    roundNormalSpecOption fmt sign num.toNat den.toNat xExponent.toNat yExponent.toNat =
      some result :=
  roundNormalSpec_eq_some_of_packed h sign num.toNat den.toNat
    xExponent.toNat yExponent.toNat shift rounded carry resultExponent
    result hnum hden hround.shift_eq hround.rounded_eq
    hround.rounded_bounds hround.carry_eq hresultExponentDef
    haccepted.resultExponent_inRange haccepted.packed_eq

private theorem divNormal_eq_roundNormalSpec_of_some (h : Eligible fmt)
    (x y result : Model fmt)
    (hresult : divNormalOption x y = some result) :
    roundNormalSpecOption fmt
        (Bool.xor (signBit fmt (toWords x).hi) (signBit fmt (toWords y).hi))
        (normalMantissa fmt (fracHigh fmt (toWords x).hi) (toWords x).lo).toNat
        (normalMantissa fmt (fracHigh fmt (toWords y).hi) (toWords y).lo).toNat
        (expField fmt (toWords x).hi).toNat
        (expField fmt (toWords y).hi).toNat =
      some result := by
  let xWords := toWords x
  let yWords := toWords y
  let xExponent := expField fmt xWords.hi
  let yExponent := expField fmt yWords.hi
  let num := normalMantissa fmt (fracHigh fmt xWords.hi) xWords.lo
  let den := normalMantissa fmt (fracHigh fmt yWords.hi) yWords.lo
  let less := UInt128.less num den
  let rationalExponent : Int := if less then -1 else 0
  let totalExponent :=
    rationalExponent + (Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat)
  let candidateShift : CandidateShift := if less then .extra else .exact
  let shift := candidateShift.toNat fmt.fracWidth
  let checked := checkedCandidate fmt.fracWidth num den candidateShift
  let rounded := roundQuotient den checked.quotient checked.remainder
  let carry := isCarry fmt rounded
  let resultExponent : Int :=
    Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat +
      Int.ofNat (fmt.bias + fmt.fracWidth) - Int.ofNat shift + if carry then 1 else 0
  have haccepted := divNormal_accepted x y result hresult
  change
    AcceptedNormalDivision fmt xExponent yExponent totalExponent resultExponent
      (Bool.xor (signBit fmt xWords.hi) (signBit fmt yWords.hi))
      rounded carry result at haccepted
  have hnumBounds :
      2 ^ fmt.fracWidth ≤ num.toNat ∧ num.toNat < 2 ^ (fmt.fracWidth + 1) :=
    normalMantissa_bounds h (fracHigh fmt (toWords x).hi) (toWords x).lo
      (fracHigh_lt h (toWords x).hi)
  have hdenBounds :
      2 ^ fmt.fracWidth ≤ den.toNat ∧ den.toNat < 2 ^ (fmt.fracWidth + 1) :=
    normalMantissa_bounds h (fracHigh fmt (toWords y).hi) (toWords y).lo
      (fracHigh_lt h (toWords y).hi)
  have hcandidateShiftEq :
      candidateShift =
        if den.toNat ≤ num.toNat then CandidateShift.exact else CandidateShift.extra := by
    simpa only [candidateShift, less] using candidateShift_eq num den
  have hround :=
    certifiedNormalRound_of_candidate h num den candidateShift shift rounded carry
      hnumBounds hdenBounds hcandidateShiftEq rfl rfl rfl
  change
    roundNormalSpecOption fmt
        (Bool.xor (signBit fmt xWords.hi) (signBit fmt yWords.hi))
        num.toNat den.toNat xExponent.toNat yExponent.toNat =
      some result
  exact
    roundNormalSpec_of_accepted h num den xExponent yExponent
      shift rounded carry totalExponent resultExponent
      (Bool.xor (signBit fmt xWords.hi) (signBit fmt yWords.hi))
      result hnumBounds.1 hdenBounds.1 hround rfl haccepted

private theorem rationalFloorLog2_normal (precision : Nat)
    (num den : Nat)
    (hnum : 2 ^ precision ≤ num ∧ num < 2 ^ (precision + 1))
    (hden : 2 ^ precision ≤ den ∧ den < 2 ^ (precision + 1)) :
    Numerics.RationalBinary.floorLog2 num den = if den ≤ num then 0 else -1 := by
  have hnumNe : num ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hnum.1)
  have hdenNe : den ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hden.1)
  have hnumLog : Nat.log2 num = precision :=
    (Nat.log2_eq_iff hnumNe).2 hnum
  have hdenLog : Nat.log2 den = precision :=
    (Nat.log2_eq_iff hdenNe).2 hden
  unfold Numerics.RationalBinary.floorLog2
  rw [hnumLog, hdenLog, sub_self]
  norm_num
  by_cases hle : den ≤ num
  · have hltTwice : num < den * 2 := by
      calc
        num < 2 ^ (precision + 1) := hnum.2
        _ = 2 ^ precision * 2 := pow_succ 2 precision
        _ ≤ den * 2 := Nat.mul_le_mul_right 2 hden.1
    have hnotLt : ¬num < den := Nat.not_lt_of_ge hle
    have hnotTwice : ¬den * 2 ≤ num := by omega
    simp [Numerics.RationalBinary.lessThanPowerOfTwo,
      Numerics.RationalBinary.atLeastPowerOfTwo,
      hle, hnotLt, hnotTwice, Nat.shiftLeft_eq]
  · have hlt : num < den := Nat.lt_of_not_ge hle
    simp [Numerics.RationalBinary.lessThanPowerOfTwo,
      Numerics.RationalBinary.atLeastPowerOfTwo,
      hle, hlt, Nat.shiftLeft_eq]

private theorem roundNormalSpec_eq_roundRatScaled_of_some (h : Eligible fmt)
    (sign : Bool) (num den xExponent yExponent : Nat) (result : Model fmt)
    (hnum : 2 ^ fmt.fracWidth ≤ num ∧ num < 2 ^ (fmt.fracWidth + 1))
    (hden : 2 ^ fmt.fracWidth ≤ den ∧ den < 2 ^ (fmt.fracWidth + 1))
    (hlow :
      ¬(if den ≤ num then
          Int.ofNat xExponent - Int.ofNat yExponent
        else
          Int.ofNat xExponent - Int.ofNat yExponent - 1) < fmt.ieeeMinNormalExponent)
    (hresult :
      roundNormalSpecOption fmt sign num den xExponent yExponent = some result) :
    result =
      roundRatScaled fmt sign num den (Int.ofNat xExponent - Int.ofNat yExponent) := by
  have hfloor := rationalFloorLog2_normal fmt.fracWidth num den hnum hden
  have hnumNe : num ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hnum.1)
  have hdenNe : den ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hden.1)
  have hallOnes := fmt.expAllOnesNat_eq_two_mul_bias_add_one
  have hmin : fmt.ieeeMinNormalExponent = 1 - Int.ofNat fmt.bias := rfl
  have hmax : fmt.ieeeMaxNormalExponent = fmt.bias := rfl
  have hshiftNonnegative :
      0 ≤ Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 num den := by
    rw [hfloor]
    by_cases hle : den ≤ num <;> simp [hle]
    all_goals omega
  apply FiniteQuotientRound.normalSpec_eq_roundRatScaled_of_some
    fmt h.isIEEE sign num den (Int.ofNat xExponent - Int.ofNat yExponent) result
    hshiftNonnegative
  rw [hmin] at hlow
  unfold FiniteQuotientRound.normalSpecOption
  rw [hfloor, hmin, hmax]
  have hresult' := hresult
  by_cases hle : den ≤ num
  · have hlow' : ¬Int.ofNat xExponent - Int.ofNat yExponent < 1 - Int.ofNat fmt.bias := by
      simpa [hle] using hlow
    simp only [Int.ofNat_eq_natCast] at hlow'
    by_cases hcarry :
        Numerics.roundQuotientEven (num * 2 ^ fmt.fracWidth) den = pow2 (fmt.fracWidth + 1)
    all_goals
      simp only [roundNormalSpecOption, Bool.or_eq_true, beq_iff_eq, hdenNe, hnumNe, or_self,
        ↓reduceIte, Int.ofNat_eq_natCast, Nat.cast_add, hle, hcarry, BEq.rfl,
        Order.add_one_le_iff, sub_neg, decide_eq_true_eq, tsub_self,
        Option.ite_none_left_eq_some, not_or, not_lt, not_le, Option.some.injEq, add_zero,
        tsub_le_iff_right, zero_add, Int.toNat_sub'] at hresult'
      obtain ⟨hrange, hpacked⟩ := hresult'
      try simp only [not_or] at hrange
      try push_cast at hrange hpacked
      simp only [Bool.or_eq_true, beq_iff_eq, hdenNe, hnumNe, or_self, ↓reduceIte, hle,
        Int.ofNat_eq_natCast, zero_add, decide_eq_true_eq, sub_zero, Int.toNat_natCast,
        Nat.shiftLeft_eq, hcarry, BEq.rfl, Order.lt_add_one_iff, tsub_self,
        Option.ite_none_left_eq_some, not_or, not_lt, tsub_le_iff_right, not_le, Option.some.injEq]
      try simp only [Int.ofNat_eq_natCast]
      try push_cast
      constructorm* _ ∧ _
      all_goals first | omega | (convert hpacked using 2; omega)
  · have hlow' :
        ¬Int.ofNat xExponent - Int.ofNat yExponent - 1 < 1 - Int.ofNat fmt.bias := by
      simpa [hle] using hlow
    simp only [Int.ofNat_eq_natCast] at hlow'
    by_cases hcarry :
        Numerics.roundQuotientEven (num * 2 ^ (fmt.fracWidth + 1)) den =
          pow2 (fmt.fracWidth + 1)
    all_goals
      simp only [roundNormalSpecOption, Bool.or_eq_true, beq_iff_eq, hdenNe, hnumNe, or_self,
        ↓reduceIte, Int.ofNat_eq_natCast, Nat.cast_add, hle, Nat.cast_one, hcarry, BEq.rfl,
        Order.add_one_le_iff, sub_neg, Order.lt_add_one_iff, decide_eq_true_eq, tsub_self,
        Option.ite_none_left_eq_some, not_or, not_le, Option.some.injEq, add_zero,
        tsub_le_iff_right, zero_add] at hresult'
      obtain ⟨hrange, hpacked⟩ := hresult'
      try simp only [not_or] at hrange
      try push_cast at hrange hpacked
      simp only [Bool.or_eq_true, beq_iff_eq, hdenNe, hnumNe, or_self, ↓reduceIte, hle,
        Int.reduceNeg, Int.ofNat_eq_natCast, neg_add_lt_iff_lt_add, lt_neg_add_iff_add_lt,
        decide_eq_true_eq, sub_neg_eq_add, Int.toNat_natCast_add_one, Nat.shiftLeft_eq, hcarry,
        BEq.rfl, neg_add_cancel_comm, tsub_self, Option.ite_none_left_eq_some, not_or, not_lt,
        tsub_le_iff_right, Option.some.injEq]
      try simp only [Int.ofNat_eq_natCast]
      try push_cast
      constructorm* _ ∧ _
      all_goals first | omega | (convert hpacked using 2; omega)

/-- Every accepted certified quotient agrees with the exact finite division kernel. -/
theorem divNormal_refines (h : Eligible fmt)
    (x y result : Model fmt)
    (hresult : divNormalOption x y = some result) :
    FiniteKernel.divOption x y = some result := by
  let xWords := toWords x
  let yWords := toWords y
  let xExponent := expField fmt xWords.hi
  let yExponent := expField fmt yWords.hi
  let num := normalMantissa fmt (fracHigh fmt xWords.hi) xWords.lo
  let den := normalMantissa fmt (fracHigh fmt yWords.hi) yWords.lo
  let less := UInt128.less num den
  let rationalExponent : Int := if less then -1 else 0
  let totalExponent :=
    rationalExponent + (Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat)
  by_cases hxZero : xExponent = 0
  · simp [divNormalOption, xWords, xExponent, hxZero] at hresult
  by_cases hxAll : xExponent = expAllOnes fmt
  · simp [divNormalOption, xWords, xExponent, hxAll] at hresult
  by_cases hyZero : yExponent = 0
  · simp [divNormalOption, yWords, yExponent, hyZero] at hresult
  by_cases hyAll : yExponent = expAllOnes fmt
  · simp [divNormalOption, yWords, yExponent, hyAll] at hresult
  have hnumBounds :
      2 ^ fmt.fracWidth ≤ num.toNat ∧ num.toNat < 2 ^ (fmt.fracWidth + 1) :=
    normalMantissa_bounds h (fracHigh fmt (toWords x).hi) (toWords x).lo
      (fracHigh_lt h (toWords x).hi)
  have hdenBounds :
      2 ^ fmt.fracWidth ≤ den.toNat ∧ den.toNat < 2 ^ (fmt.fracWidth + 1) :=
    normalMantissa_bounds h (fracHigh fmt (toWords y).hi) (toWords y).lo
      (fracHigh_lt h (toWords y).hi)
  have hlowNative : ¬totalExponent < fmt.ieeeMinNormalExponent := by
    have hroute := hresult
    simp [divNormalOption, xWords, yWords, xExponent, yExponent,
      hxZero, hxAll, hyZero, hyAll] at hroute
    apply not_lt.mpr
    simpa [totalExponent, rationalExponent, less, num, den,
      xExponent, yExponent, xWords, yWords] using hroute.1
  have hlow :
      ¬(if den.toNat ≤ num.toNat then
          Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat
        else
          Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat - 1) <
        fmt.ieeeMinNormalExponent := by
    by_cases hle : den.toNat ≤ num.toNat
    · have hless : less = false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        exact (Nat.not_lt_of_ge hle) ((UInt128.less_eq_true_iff num den).1 htrue)
      have hlowNative' := hlowNative
      simp [totalExponent, rationalExponent, hless] at hlowNative'
      simpa [hle] using hlowNative'
    · have hless : less = true :=
        (UInt128.less_eq_true_iff num den).2 (Nat.lt_of_not_ge hle)
      have hlowNative' := hlowNative
      simp [totalExponent, rationalExponent, hless] at hlowNative'
      rw [ite_eq_right hle]
      simp only [Int.ofNat_eq_natCast] at hlowNative' ⊢
      omega
  have hnormal := divNormal_eq_roundNormalSpec_of_some h x y result hresult
  have hrounded :
      result =
        roundRatScaled fmt
          (Bool.xor (signBit fmt xWords.hi) (signBit fmt yWords.hi))
          num.toNat den.toNat
          (Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat) :=
    roundNormalSpec_eq_roundRatScaled_of_some h
      (Bool.xor (signBit fmt xWords.hi) (signBit fmt yWords.hi))
      num.toNat den.toNat xExponent.toNat yExponent.toNat result
      hnumBounds hdenBounds hlow hnormal
  have hxExponentBounds : 0 < xExponent.toNat ∧ xExponent.toNat < fmt.expAllOnesNat :=
    normalExponent_bounds h x hxZero hxAll
  have hyExponentBounds : 0 < yExponent.toNat ∧ yExponent.toNat < fmt.expAllOnesNat :=
    normalExponent_bounds h y hyZero hyAll
  have hscale :
      Int.ofNat (FiniteKernel.scale xExponent.toNat) -
          Int.ofNat (FiniteKernel.scale yExponent.toNat) =
        Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat := by
    unfold FiniteKernel.scale
    simp only [beq_iff_eq, Nat.ne_of_gt hxExponentBounds.1,
      Nat.ne_of_gt hyExponentBounds.1, ite_false]
    simp only [Int.ofNat_eq_natCast, Nat.cast_sub hxExponentBounds.1,
      Nat.cast_sub hyExponentBounds.1]
    omega
  unfold FiniteKernel.divOption
  rw [decode_of_normalExponent h x hxZero hxAll, decode_of_normalExponent h y hyZero hyAll]
  simp only [Option.some.injEq]
  change
    FiniteKernel.divComponents fmt
      { sign := signBit fmt xWords.hi
        exponent := xExponent.toNat
        mantissa := num.toNat }
      { sign := signBit fmt yWords.hi
        exponent := yExponent.toNat
        mantissa := den.toNat } =
      result
  unfold FiniteKernel.divComponents
  have hnumNe : num.toNat ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hnumBounds.1)
  have hdenNe : den.toNat ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hdenBounds.1)
  simp only [hnumNe, hdenNe, beq_iff_eq, ite_false]
  rw [hscale]
  exact hrounded.symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
