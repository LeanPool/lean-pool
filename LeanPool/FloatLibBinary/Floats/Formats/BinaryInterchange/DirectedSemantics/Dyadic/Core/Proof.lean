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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Dyadic.Core.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Signed

/-!
# Core directed rounding of exact dyadics

Floor and ceiling normalization bounds characterize the executable underflow, subnormal, normal,
and overflow branches. The lemmas include the one-bit carry that upward rounding can produce and
connect exponent alignment to real rounding before field packing.

All results are uniform in `FloatFormat`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats

section

/-! ## Leading-bit normalization -/

/-- Downward leading-bit normalization never exceeds upward normalization. -/
theorem roundMantissaToLeadingBitDown_le_up (mantissa leadingBit : Nat) :
    roundMantissaToLeadingBitDown mantissa leadingBit ≤
      roundMantissaToLeadingBitUp mantissa leadingBit := by
  by_cases hle : leadingBit ≤ mantissa.log2
  · simp only [roundMantissaToLeadingBitDown, roundMantissaToLeadingBitUp,
      ite_eq_left hle]
    exact shiftRight_le_shiftRightCeilPow2 _ _
  · simp [roundMantissaToLeadingBitDown, roundMantissaToLeadingBitUp, hle]

/-- A nonzero mantissa normalized downward to leading position `p` is at least `2^p`. -/
theorem pow2_le_roundMantissaToLeadingBitDown
    (mantissa leadingBit : Nat) (hm : mantissa ≠ 0) :
    pow2 leadingBit ≤ roundMantissaToLeadingBitDown mantissa leadingBit := by
  unfold roundMantissaToLeadingBitDown
  split <;> rename_i hle
  · have hdiv :
        2 ^ leadingBit ≤ mantissa / 2 ^ (mantissa.log2 - leadingBit) := by
      rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))]
      rw [show 2 ^ leadingBit * 2 ^ (mantissa.log2 - leadingBit) =
          2 ^ mantissa.log2 by
        rw [Nat.mul_comm, Nat.pow_sub_mul_pow 2 hle]]
      exact Nat.log2_self_le hm
    simpa [pow2_eq_two_pow, Nat.shiftRight_eq_div_pow] using hdiv
  · have hlogLe : 2 ^ mantissa.log2 ≤ mantissa := Nat.log2_self_le hm
    have hmul := Nat.mul_le_mul_right (2 ^ (leadingBit - mantissa.log2)) hlogLe
    rw [show 2 ^ mantissa.log2 * 2 ^ (leadingBit - mantissa.log2) =
        2 ^ leadingBit by
      rw [Nat.mul_comm, Nat.pow_sub_mul_pow 2 (Nat.le_of_not_ge hle)]] at hmul
    simpa [pow2_eq_two_pow, Nat.shiftLeft_eq] using hmul

/-- Downward leading-bit normalization remains strictly below `2^(p+1)`. -/
theorem roundMantissaToLeadingBitDown_lt_pow2_succ
    (mantissa leadingBit : Nat) :
    roundMantissaToLeadingBitDown mantissa leadingBit < pow2 (leadingBit + 1) := by
  by_cases hm : mantissa = 0
  · simp [roundMantissaToLeadingBitDown, hm, pow2_pos]
  · unfold roundMantissaToLeadingBitDown
    split <;> rename_i hle
    · have hdiv :
          mantissa / 2 ^ (mantissa.log2 - leadingBit) < 2 ^ (leadingBit + 1) := by
        have hexponent :
            leadingBit + 1 + (mantissa.log2 - leadingBit) =
              mantissa.log2 + 1 := by
          omega
        rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
        rw [show 2 ^ (leadingBit + 1) * 2 ^ (mantissa.log2 - leadingBit) =
            2 ^ (mantissa.log2 + 1) by
          rw [← Nat.pow_add, hexponent]]
        simpa [pow2_eq_two_pow] using lt_pow2_log2_add_one hm
      simpa [pow2_eq_two_pow, Nat.shiftRight_eq_div_pow] using hdiv
    · have hlt : mantissa < 2 ^ (mantissa.log2 + 1) := by
        simpa [pow2_eq_two_pow] using lt_pow2_log2_add_one hm
      have hpowPos : 0 < 2 ^ (leadingBit - mantissa.log2) := Nat.pow_pos (by decide)
      have hmul := Nat.mul_lt_mul_of_pos_right hlt hpowPos
      have hexponent :
          mantissa.log2 + 1 + (leadingBit - mantissa.log2) =
            leadingBit + 1 := by
        omega
      rw [show 2 ^ (mantissa.log2 + 1) * 2 ^ (leadingBit - mantissa.log2) =
          2 ^ (leadingBit + 1) by
        rw [← Nat.pow_add, hexponent]] at hmul
      simpa [pow2_eq_two_pow, Nat.shiftLeft_eq] using hmul

/-- A nonzero mantissa normalized upward to leading position `p` is at least `2^p`. -/
theorem pow2_le_roundMantissaToLeadingBitUp
    (mantissa leadingBit : Nat) (hm : mantissa ≠ 0) :
    pow2 leadingBit ≤ roundMantissaToLeadingBitUp mantissa leadingBit :=
  (pow2_le_roundMantissaToLeadingBitDown mantissa leadingBit hm).trans
    (roundMantissaToLeadingBitDown_le_up mantissa leadingBit)

/-- Upward leading-bit normalization can produce only the one-bit carry `2^(p+1)`. -/
theorem roundMantissaToLeadingBitUp_le_pow2_succ
    (mantissa leadingBit : Nat) :
    roundMantissaToLeadingBitUp mantissa leadingBit ≤ pow2 (leadingBit + 1) := by
  by_cases hle : leadingBit ≤ mantissa.log2
  · have hfloor :=
      roundMantissaToLeadingBitDown_lt_pow2_succ mantissa leadingBit
    have hceil :=
      shiftRightCeilPow2_le_shiftRight_add_one mantissa
        (mantissa.log2 - leadingBit)
    simp only [roundMantissaToLeadingBitDown, roundMantissaToLeadingBitUp, hle,
      ite_true] at hfloor ⊢
    exact hceil.trans (Nat.succ_le_iff.mpr hfloor)
  · have hfloor :=
      roundMantissaToLeadingBitDown_lt_pow2_succ mantissa leadingBit
    simpa [roundMantissaToLeadingBitDown, roundMantissaToLeadingBitUp, hle] using hfloor.le

/-- Upward leading-bit normalization of a nonzero mantissa remains nonzero. -/
theorem roundMantissaToLeadingBitUp_ne_zero
    (mantissa leadingBit : Nat) (hm : mantissa ≠ 0) :
    roundMantissaToLeadingBitUp mantissa leadingBit ≠ 0 := by
  have hlower := pow2_le_roundMantissaToLeadingBitUp mantissa leadingBit hm
  exact Nat.ne_of_gt ((pow2_pos leadingBit).trans_le hlower)

/-! ## Exponent alignment -/

/-- Rounding down at the exponent that places the leading bit at `leadingBit` is direct shift. -/
theorem roundMantissaAtExponentDown_eq_roundMantissaToLeadingBitDown
    (mantissa leadingBit : Nat) (exponent : Int) :
    roundMantissaAtExponentDown mantissa exponent
        ((mantissa.log2 : Int) + exponent - (leadingBit : Int)) =
      roundMantissaToLeadingBitDown mantissa leadingBit := by
  by_cases hle : leadingBit ≤ mantissa.log2
  · have hexponentLe :
        exponent ≤ (mantissa.log2 : Int) + exponent - (leadingBit : Int) := by
      grind
    have hdistance :
        (((mantissa.log2 : Int) + exponent - (leadingBit : Int)) - exponent).toNat =
          mantissa.log2 - leadingBit := by
      rw [show (mantissa.log2 : Int) + exponent - (leadingBit : Int) - exponent =
          ((mantissa.log2 - leadingBit : Nat) : Int) by grind]
      rfl
    simp [roundMantissaAtExponentDown, roundMantissaToLeadingBitDown,
      hexponentLe, hle, hdistance]
  · have hnotExponentLe :
        ¬exponent ≤ (mantissa.log2 : Int) + exponent - (leadingBit : Int) := by
      grind
    have hdistance :
        (exponent - ((mantissa.log2 : Int) + exponent - (leadingBit : Int))).toNat =
          leadingBit - mantissa.log2 := by
      rw [show exponent - ((mantissa.log2 : Int) + exponent - (leadingBit : Int)) =
          ((leadingBit - mantissa.log2 : Nat) : Int) by grind]
      rfl
    simp [roundMantissaAtExponentDown, roundMantissaToLeadingBitDown,
      hnotExponentLe, hle, hdistance]

/-- Rounding up at the exponent that places the leading bit at `leadingBit` is direct shift. -/
theorem roundMantissaAtExponentUp_eq_roundMantissaToLeadingBitUp
    (mantissa leadingBit : Nat) (exponent : Int) :
    roundMantissaAtExponentUp mantissa exponent
        ((mantissa.log2 : Int) + exponent - (leadingBit : Int)) =
      roundMantissaToLeadingBitUp mantissa leadingBit := by
  by_cases hle : leadingBit ≤ mantissa.log2
  · have hexponentLe :
        exponent ≤ (mantissa.log2 : Int) + exponent - (leadingBit : Int) := by
      grind
    have hdistance :
        (((mantissa.log2 : Int) + exponent - (leadingBit : Int)) - exponent).toNat =
          mantissa.log2 - leadingBit := by
      rw [show (mantissa.log2 : Int) + exponent - (leadingBit : Int) - exponent =
          ((mantissa.log2 - leadingBit : Nat) : Int) by grind]
      rfl
    simp [roundMantissaAtExponentUp, roundMantissaToLeadingBitUp,
      hexponentLe, hle, hdistance]
  · have hnotExponentLe :
        ¬exponent ≤ (mantissa.log2 : Int) + exponent - (leadingBit : Int) := by
      grind
    have hdistance :
        (exponent - ((mantissa.log2 : Int) + exponent - (leadingBit : Int))).toNat =
          leadingBit - mantissa.log2 := by
      rw [show exponent - ((mantissa.log2 : Int) + exponent - (leadingBit : Int)) =
          ((leadingBit - mantissa.log2 : Nat) : Int) by grind]
      rfl
    simp [roundMantissaAtExponentUp, roundMantissaToLeadingBitUp,
      hnotExponentLe, hle, hdistance]

/-! ## Executable exponent alignment -/

/-- The branch form used by the executable downward rounder is floor exponent alignment. -/
theorem roundMantissaAtExponentDown_eq_match
    (mantissa : Nat) (exponent targetExponent : Int) :
    roundMantissaAtExponentDown mantissa exponent targetExponent =
      match exponent - targetExponent with
      | .ofNat shift => Nat.shiftLeft mantissa shift
      | .negSucc shift => Nat.shiftRight mantissa (shift + 1) := by
  cases hdiff : exponent - targetExponent with
  | ofNat shift =>
      cases shift with
      | zero =>
          have heq : exponent = targetExponent := by
            norm_num at hdiff
            omega
          simp [roundMantissaAtExponentDown, heq]
      | succ shift =>
          have hnot : ¬exponent ≤ targetExponent := by
            norm_num at hdiff
            omega
          simp [roundMantissaAtExponentDown, hnot, hdiff]
  | negSucc shift =>
      have hle : exponent ≤ targetExponent := by
        omega
      have htoNat : (targetExponent - exponent).toNat = shift + 1 := by
        have hneg : targetExponent - exponent = Int.ofNat (shift + 1) := by
          norm_num at hdiff ⊢
          omega
        rw [hneg]
        rfl
      simp [roundMantissaAtExponentDown, hle, htoNat]

/-- The branch form used by the executable upward rounder is ceiling exponent alignment. -/
theorem roundMantissaAtExponentUp_eq_match
    (mantissa : Nat) (exponent targetExponent : Int) :
    roundMantissaAtExponentUp mantissa exponent targetExponent =
      match exponent - targetExponent with
      | .ofNat shift => Nat.shiftLeft mantissa shift
      | .negSucc shift => shiftRightCeilPow2 mantissa (shift + 1) := by
  cases hdiff : exponent - targetExponent with
  | ofNat shift =>
      cases shift with
      | zero =>
          have heq : exponent = targetExponent := by
            norm_num at hdiff
            omega
          simp [roundMantissaAtExponentUp, heq, shiftRightCeilPow2]
      | succ shift =>
          have hnot : ¬exponent ≤ targetExponent := by
            norm_num at hdiff
            omega
          simp [roundMantissaAtExponentUp, hnot, hdiff]
  | negSucc shift =>
      have hle : exponent ≤ targetExponent := by
        omega
      have htoNat : (targetExponent - exponent).toNat = shift + 1 := by
        have hneg : targetExponent - exponent = Int.ofNat (shift + 1) := by
          norm_num at hdiff ⊢
          omega
        rw [hneg]
        rfl
      simp [roundMantissaAtExponentUp, hle, htoNat]

/-! ## Exact rounded-real alignment -/

/-- Positive downward rounded-real semantics is floor alignment at the model target exponent. -/
theorem roundAtDown_pos_eq
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true) (hm : mantissa ≠ 0) :
    let target :=
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent)
    roundAtDown fmt ((mantissa : ℝ) * bpow exponent) =
      (roundMantissaAtExponentDown mantissa exponent target : ℝ) *
        bpow target := by
  let d : Numerics.Dyadic := { negative := false, significand := mantissa, exponent := exponent }
  simpa [d, Numerics.Dyadic.toReal, roundSignedMantissaAtExponentDown,
    bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
    roundAtDown_dyadic_eq fmt d hfmt hm

/-- Positive upward rounded-real semantics is ceiling alignment at the model target exponent. -/
theorem roundAtUp_pos_eq
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true) (hm : mantissa ≠ 0) :
    let target :=
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent)
    roundAtUp fmt ((mantissa : ℝ) * bpow exponent) =
      (roundMantissaAtExponentUp mantissa exponent target : ℝ) *
        bpow target := by
  let d : Numerics.Dyadic := { negative := false, significand := mantissa, exponent := exponent }
  simpa [d, Numerics.Dyadic.toReal, roundSignedMantissaAtExponentUp,
    bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
    roundAtUp_dyadic_eq fmt d hfmt hm

/-- Below the subnormal grid, downward alignment has zero mantissa. -/
theorem roundMantissaAtExponentDown_eq_zero_of_lt_minSubnormal
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hm : mantissa ≠ 0)
    (hunderflow :
      (mantissa.log2 : Int) + exponent < fmt.minSubnormalExponent) :
    roundMantissaAtExponentDown mantissa exponent
        (fmt.minSubnormalExponent) = 0 := by
  have hexponentLe : exponent ≤ fmt.minSubnormalExponent := by
    have hlog : (0 : Int) ≤ mantissa.log2 := by omega
    omega
  let shift := (fmt.minSubnormalExponent - exponent).toNat
  have hshiftInt :
      (shift : Int) = fmt.minSubnormalExponent - exponent :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hexponentLe)
  have hlogInt : (mantissa.log2 : Int) + 1 ≤ shift := by
    rw [hshiftInt]
    omega
  have hlogNat : mantissa.log2 + 1 ≤ shift := by
    exact_mod_cast hlogInt
  have hmantissaLt : mantissa < 2 ^ shift := by
    have hleading := lt_pow2_log2_add_one hm
    have hleading' : mantissa < 2 ^ (mantissa.log2 + 1) := by
      simpa [pow2_eq_two_pow] using hleading
    have hpow :
        2 ^ (mantissa.log2 + 1) ≤ 2 ^ shift :=
      Nat.pow_le_pow_right (by decide) hlogNat
    exact hleading'.trans_le hpow
  simp [roundMantissaAtExponentDown, hexponentLe, shift,
    Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hmantissaLt]

/-- Below the subnormal grid, upward alignment has the minimum positive mantissa. -/
theorem roundMantissaAtExponentUp_eq_one_of_lt_minSubnormal
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hm : mantissa ≠ 0)
    (hunderflow :
      (mantissa.log2 : Int) + exponent < fmt.minSubnormalExponent) :
    roundMantissaAtExponentUp mantissa exponent
        (fmt.minSubnormalExponent) = 1 := by
  have hdown :
      roundMantissaAtExponentDown mantissa exponent
          (fmt.minSubnormalExponent) = 0 :=
    roundMantissaAtExponentDown_eq_zero_of_lt_minSubnormal
      fmt mantissa exponent hm hunderflow
  have hupLe :=
    roundMantissaAtExponentUp_le_down_add_one mantissa exponent
      (fmt.minSubnormalExponent)
  have hupNe :=
    roundMantissaAtExponentUp_ne_zero mantissa exponent
      (fmt.minSubnormalExponent) hm
  rw [hdown] at hupLe
  omega

/-! ## Positive executable branches -/

/-- Downward positive rounding saturates at the largest finite value on overflow. -/
theorem roundDyadicPosDown_eq_posMaxFinite_of_overflow
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hoverflow :
      fmt.maxNormalExponent <
        (mantissa.log2 : Int) + exponent) :
    roundDyadicPosDown fmt mantissa exponent = posMaxFinite fmt := by
  have hoverflow' :
      fmt.maxNormalExponent <
        Int.ofNat mantissa.log2 + exponent := by
    simpa only [Int.ofNat_eq_natCast] using hoverflow
  unfold roundDyadicPosDown roundDyadicMagnitudeDown
  rw [ite_eq_left hoverflow']
  rfl

/-- Upward positive rounding returns the format's positive overflow value. -/
theorem roundDyadicPosUp_eq_nativeOverflow_of_overflow
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hoverflow :
      fmt.maxNormalExponent <
        (mantissa.log2 : Int) + exponent) :
    roundDyadicPosUp fmt mantissa exponent = nativeOverflow fmt false := by
  have hoverflow' :
      fmt.maxNormalExponent <
        Int.ofNat mantissa.log2 + exponent := by
    simpa only [Int.ofNat_eq_natCast] using hoverflow
  unfold roundDyadicPosUp roundDyadicMagnitudeUp
  rw [ite_eq_left hoverflow']

/-- Downward positive rounding below the subnormal grid is format zero. -/
theorem roundDyadicPosDown_eq_zero_of_underflow
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hunderflow :
      (mantissa.log2 : Int) + exponent < fmt.minSubnormalExponent) :
    roundDyadicPosDown fmt mantissa exponent = zero fmt false := by
  have hmax :
      (mantissa.log2 : Int) + exponent ≤
        fmt.maxNormalExponent :=
    (le_of_lt hunderflow).trans
      ((minSubnormalExponent_lt_minNormalExponent fmt).le.trans
        (minNormalExponent_le_maxNormalExponent fmt))
  have hmax' :
      Int.ofNat mantissa.log2 + exponent ≤
        fmt.maxNormalExponent := by
    simpa only [Int.ofNat_eq_natCast] using hmax
  have hunderflow' :
      Int.ofNat mantissa.log2 + exponent <
        fmt.minSubnormalExponent := by
    simpa only [Int.ofNat_eq_natCast] using hunderflow
  unfold roundDyadicPosDown roundDyadicMagnitudeDown
  rw [ite_eq_right (not_lt_of_ge hmax'), ite_eq_left hunderflow']

/-- Upward positive rounding below the subnormal grid is the smallest positive subnormal. -/
theorem roundDyadicPosUp_eq_posMinSubnormal_of_underflow
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hunderflow :
      (mantissa.log2 : Int) + exponent < fmt.minSubnormalExponent) :
    roundDyadicPosUp fmt mantissa exponent = posMinSubnormal fmt := by
  have hmax :
      (mantissa.log2 : Int) + exponent ≤
        fmt.maxNormalExponent :=
    (le_of_lt hunderflow).trans
      ((minSubnormalExponent_lt_minNormalExponent fmt).le.trans
        (minNormalExponent_le_maxNormalExponent fmt))
  have hmax' :
      Int.ofNat mantissa.log2 + exponent ≤
        fmt.maxNormalExponent := by
    simpa only [Int.ofNat_eq_natCast] using hmax
  have hunderflow' :
      Int.ofNat mantissa.log2 + exponent <
        fmt.minSubnormalExponent := by
    simpa only [Int.ofNat_eq_natCast] using hunderflow
  unfold roundDyadicPosUp roundDyadicMagnitudeUp
  rw [ite_eq_right (not_lt_of_ge hmax'), ite_eq_left hunderflow']
  exact (posMinSubnormal_eq_ofFields fmt).symm

/-- The executable downward subnormal branch is floor alignment to the minimum grid. -/
theorem roundDyadicPosDown_eq_subnormal
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hlow :
      fmt.minSubnormalExponent ≤ (mantissa.log2 : Int) + exponent)
    (hhigh :
      (mantissa.log2 : Int) + exponent <
        fmt.minNormalExponent) :
    roundDyadicPosDown fmt mantissa exponent =
      let rounded :=
        roundMantissaAtExponentDown mantissa exponent
          (fmt.minSubnormalExponent)
      if rounded = 0 then zero fmt false else ofFields fmt false 0 rounded := by
  have hmax :
      (mantissa.log2 : Int) + exponent ≤
        fmt.maxNormalExponent :=
    hhigh.le.trans (minNormalExponent_le_maxNormalExponent fmt)
  have hmax' :
      Int.ofNat mantissa.log2 + exponent ≤
        fmt.maxNormalExponent := by
    simpa only [Int.ofNat_eq_natCast] using hmax
  have hlow' :
      fmt.minSubnormalExponent ≤
        Int.ofNat mantissa.log2 + exponent := by
    simpa only [Int.ofNat_eq_natCast] using hlow
  have hhigh' :
      Int.ofNat mantissa.log2 + exponent <
        fmt.minNormalExponent := by
    simpa only [Int.ofNat_eq_natCast] using hhigh
  unfold roundDyadicPosDown roundDyadicMagnitudeDown
  rw [ite_eq_right (not_lt_of_ge hmax'), ite_eq_right (not_lt_of_ge hlow'),
    ite_eq_left hhigh']
  rw [roundMantissaAtExponentDown_eq_match]
  simp only [beq_iff_eq]
  rfl

/-- The executable upward subnormal branch is ceiling alignment to the minimum grid. -/
theorem roundDyadicPosUp_eq_subnormal
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hlow :
      fmt.minSubnormalExponent ≤ (mantissa.log2 : Int) + exponent)
    (hhigh :
      (mantissa.log2 : Int) + exponent <
        fmt.minNormalExponent) :
    roundDyadicPosUp fmt mantissa exponent =
      let rounded :=
        roundMantissaAtExponentUp mantissa exponent
          (fmt.minSubnormalExponent)
      if rounded = 0 then
        posMinSubnormal fmt
      else if pow2 fmt.fracWidth ≤ rounded then
        ofFields fmt false 1 0
      else
        ofFields fmt false 0 rounded := by
  have hmax :
      (mantissa.log2 : Int) + exponent ≤
        fmt.maxNormalExponent :=
    hhigh.le.trans (minNormalExponent_le_maxNormalExponent fmt)
  have hmax' :
      Int.ofNat mantissa.log2 + exponent ≤
        fmt.maxNormalExponent := by
    simpa only [Int.ofNat_eq_natCast] using hmax
  have hlow' :
      fmt.minSubnormalExponent ≤
        Int.ofNat mantissa.log2 + exponent := by
    simpa only [Int.ofNat_eq_natCast] using hlow
  have hhigh' :
      Int.ofNat mantissa.log2 + exponent <
        fmt.minNormalExponent := by
    simpa only [Int.ofNat_eq_natCast] using hhigh
  unfold roundDyadicPosUp roundDyadicMagnitudeUp
  rw [ite_eq_right (not_lt_of_ge hmax'), ite_eq_right (not_lt_of_ge hlow'),
    ite_eq_left hhigh']
  rw [roundMantissaAtExponentUp_eq_match]
  simp only [packRoundedSubnormal, beq_iff_eq]
  rw [posMinSubnormal_eq_ofFields]
  rfl

/-- The downward normal branch packs the mantissa or saturates if the fields exceed the range. -/
theorem roundDyadicPosDown_eq_normal
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hnormal :
      fmt.minNormalExponent ≤
        (mantissa.log2 : Int) + exponent)
    (hmax :
      (mantissa.log2 : Int) + exponent ≤
        fmt.maxNormalExponent) :
    roundDyadicPosDown fmt mantissa exponent =
      let totalExponent := (mantissa.log2 : Int) + exponent
      let rounded :=
        roundMantissaToLeadingBitDown mantissa fmt.fracWidth
      let encodedExponent :=
        Int.toNat (totalExponent + Int.ofNat fmt.exponentBias)
      let fraction := rounded - pow2 fmt.fracWidth
      if encodedExponent > fmt.maxFiniteExpField ||
          (encodedExponent == fmt.maxFiniteExpField &&
            fraction > fmt.maxFiniteFracField) then
        posMaxFinite fmt
      else
        ofFields fmt false encodedExponent fraction := by
  have hnormal' :
      fmt.minNormalExponent ≤
        Int.ofNat mantissa.log2 + exponent := by
    simpa only [Int.ofNat_eq_natCast] using hnormal
  have hmax' :
      Int.ofNat mantissa.log2 + exponent ≤
        fmt.maxNormalExponent := by
    simpa only [Int.ofNat_eq_natCast] using hmax
  unfold roundDyadicPosDown roundDyadicMagnitudeDown
  rw [ite_eq_right (not_lt_of_ge hmax'),
    ite_eq_right (not_lt_of_ge
      ((minSubnormalExponent_lt_minNormalExponent fmt).le.trans hnormal')),
    ite_eq_right (not_lt_of_ge hnormal')]
  rfl

/-- Without a carry, the upward normal branch packs the mantissa or returns the overflow value. -/
theorem roundDyadicPosUp_eq_normal_of_no_carry
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hnormal :
      fmt.minNormalExponent ≤
        (mantissa.log2 : Int) + exponent)
    (hmax :
      (mantissa.log2 : Int) + exponent ≤
        fmt.maxNormalExponent)
    (hcarry :
      roundMantissaToLeadingBitUp mantissa fmt.fracWidth ≠
        pow2 (fmt.fracWidth + 1)) :
    roundDyadicPosUp fmt mantissa exponent =
      let encodedExponent :=
        Int.toNat
          ((mantissa.log2 : Int) + exponent + Int.ofNat fmt.exponentBias)
      let fraction :=
        roundMantissaToLeadingBitUp mantissa fmt.fracWidth -
          pow2 fmt.fracWidth
      if encodedExponent > fmt.maxFiniteExpField ||
          (encodedExponent == fmt.maxFiniteExpField &&
            fraction > fmt.maxFiniteFracField) then
        nativeOverflow fmt false
      else
        ofFields fmt false encodedExponent fraction := by
  have hnormal' :
      fmt.minNormalExponent ≤
        Int.ofNat mantissa.log2 + exponent := by
    simpa only [Int.ofNat_eq_natCast] using hnormal
  have hmax' :
      Int.ofNat mantissa.log2 + exponent ≤
        fmt.maxNormalExponent := by
    simpa only [Int.ofNat_eq_natCast] using hmax
  unfold roundDyadicPosUp roundDyadicMagnitudeUp
  rw [ite_eq_right (not_lt_of_ge hmax'),
    ite_eq_right (not_lt_of_ge
      ((minSubnormalExponent_lt_minNormalExponent fmt).le.trans hnormal')),
    ite_eq_right (not_lt_of_ge hnormal')]
  have hrounded :
      (if mantissa.log2 ≥ fmt.fracWidth then
        shiftRightCeilPow2 mantissa (mantissa.log2 - fmt.fracWidth)
      else
        Nat.shiftLeft mantissa (fmt.fracWidth - mantissa.log2)) =
        roundMantissaToLeadingBitUp mantissa fmt.fracWidth := rfl
  rw [hrounded]
  simp only [packRoundedNormal, hcarry, beq_iff_eq, ite_false]
  rw [ite_eq_right (not_lt_of_ge hmax')]
  rfl

/-- Upward positive rounding packs the renormalized mantissa after a finite carry. -/
theorem roundDyadicPosUp_eq_normal_of_carry
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hnormal :
      fmt.minNormalExponent ≤
        (mantissa.log2 : Int) + exponent)
    (hmax :
      (mantissa.log2 : Int) + exponent ≤
        fmt.maxNormalExponent)
    (hcarry :
      roundMantissaToLeadingBitUp mantissa fmt.fracWidth =
        pow2 (fmt.fracWidth + 1))
    (hcarryMax :
      (mantissa.log2 : Int) + exponent + 1 ≤
        fmt.maxNormalExponent) :
    roundDyadicPosUp fmt mantissa exponent =
      ofFields fmt false
        (Int.toNat
          ((mantissa.log2 : Int) + exponent + 1 + Int.ofNat fmt.exponentBias))
        0 := by
  have hnormal' :
      fmt.minNormalExponent ≤
        Int.ofNat mantissa.log2 + exponent := by
    simpa only [Int.ofNat_eq_natCast] using hnormal
  have hmax' :
      Int.ofNat mantissa.log2 + exponent ≤
        fmt.maxNormalExponent := by
    simpa only [Int.ofNat_eq_natCast] using hmax
  have hcarryMax' :
      Int.ofNat mantissa.log2 + exponent + 1 ≤
        fmt.maxNormalExponent := by
    simpa only [Int.ofNat_eq_natCast] using hcarryMax
  unfold roundDyadicPosUp roundDyadicMagnitudeUp
  rw [ite_eq_right (not_lt_of_ge hmax'),
    ite_eq_right (not_lt_of_ge
      ((minSubnormalExponent_lt_minNormalExponent fmt).le.trans hnormal')),
    ite_eq_right (not_lt_of_ge hnormal')]
  have hrounded :
      (if mantissa.log2 ≥ fmt.fracWidth then
        shiftRightCeilPow2 mantissa (mantissa.log2 - fmt.fracWidth)
      else
        Nat.shiftLeft mantissa (fmt.fracWidth - mantissa.log2)) =
        roundMantissaToLeadingBitUp mantissa fmt.fracWidth := rfl
  rw [hrounded]
  simp only [packRoundedNormal, hcarry, beq_iff_eq, ite_true]
  rw [ite_eq_right (not_lt_of_ge hcarryMax')]
  simp only [Nat.sub_self]
  have hencoded :
      Int.toNat
          (Int.ofNat mantissa.log2 + exponent + 1 +
            Int.ofNat fmt.exponentBias) ≤
        fmt.maxFiniteExpField := by
    have hpositive :
        0 <
          Int.ofNat mantissa.log2 + exponent + 1 +
            Int.ofNat fmt.exponentBias := by
      unfold FloatFormat.minNormalExponent at hnormal'
      omega
    have hexact :
        Int.ofNat
            (Int.toNat
              (Int.ofNat mantissa.log2 + exponent + 1 +
                Int.ofNat fmt.exponentBias)) =
          Int.ofNat mantissa.log2 + exponent + 1 +
            Int.ofNat fmt.exponentBias :=
      Int.toNat_of_nonneg hpositive.le
    have hbound :
        Int.ofNat
            (Int.toNat
              (Int.ofNat mantissa.log2 + exponent + 1 +
                Int.ofNat fmt.exponentBias)) ≤
          Int.ofNat fmt.maxFiniteExpField := by
      rw [hexact]
      unfold FloatFormat.maxNormalExponent at hcarryMax'
      omega
    exact Int.ofNat_le.mp hbound
  have hencodedNot :
      ¬Int.toNat
          (Int.ofNat mantissa.log2 + exponent + 1 +
            Int.ofNat fmt.exponentBias) >
        fmt.maxFiniteExpField :=
    not_lt_of_ge hencoded
  have hfractionNot : ¬0 > fmt.maxFiniteFracField := by omega
  simp only [hencodedNot, hfractionNot, decide_false, Bool.and_false,
    Bool.or_false, Bool.false_eq_true, ite_false]
  simp only [Int.ofNat_eq_natCast]

/-- A normalization carry beyond the largest exponent produces the format's overflow value. -/
theorem roundDyadicPosUp_eq_nativeOverflow_of_carry_overflow
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hnormal :
      fmt.minNormalExponent ≤
        (mantissa.log2 : Int) + exponent)
    (hmax :
      (mantissa.log2 : Int) + exponent ≤
        fmt.maxNormalExponent)
    (hcarry :
      roundMantissaToLeadingBitUp mantissa fmt.fracWidth =
        pow2 (fmt.fracWidth + 1))
    (hcarryOverflow :
      fmt.maxNormalExponent <
        (mantissa.log2 : Int) + exponent + 1) :
    roundDyadicPosUp fmt mantissa exponent = nativeOverflow fmt false := by
  have hnormal' :
      fmt.minNormalExponent ≤
        Int.ofNat mantissa.log2 + exponent := by
    simpa only [Int.ofNat_eq_natCast] using hnormal
  have hmax' :
      Int.ofNat mantissa.log2 + exponent ≤
        fmt.maxNormalExponent := by
    simpa only [Int.ofNat_eq_natCast] using hmax
  have hcarryOverflow' :
      fmt.maxNormalExponent <
        Int.ofNat mantissa.log2 + exponent + 1 := by
    simpa only [Int.ofNat_eq_natCast] using hcarryOverflow
  unfold roundDyadicPosUp roundDyadicMagnitudeUp
  rw [ite_eq_right (not_lt_of_ge hmax'),
    ite_eq_right (not_lt_of_ge
      ((minSubnormalExponent_lt_minNormalExponent fmt).le.trans hnormal')),
    ite_eq_right (not_lt_of_ge hnormal')]
  have hrounded :
      (if mantissa.log2 ≥ fmt.fracWidth then
        shiftRightCeilPow2 mantissa (mantissa.log2 - fmt.fracWidth)
      else
        Nat.shiftLeft mantissa (fmt.fracWidth - mantissa.log2)) =
        roundMantissaToLeadingBitUp mantissa fmt.fracWidth := rfl
  rw [hrounded]
  simp only [packRoundedNormal, hcarry, beq_iff_eq, ite_true]
  rw [ite_eq_left hcarryOverflow']

/-! ## Subnormal-grid bounds -/

/--
Downward rounding below the normal range remains strictly below the smallest normal mantissa.
-/
theorem roundMantissaAtExponentDown_minSubnormal_lt_pow2
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hk : (mantissa.log2 : Int) + exponent <
      fmt.minNormalExponent) :
    roundMantissaAtExponentDown mantissa exponent (fmt.minSubnormalExponent) <
      pow2 fmt.fracWidth := by
  have hscale :
      fmt.minSubnormalExponent + (fmt.fracWidth : Int) =
        fmt.minNormalExponent := by
    simpa only [Int.ofNat_eq_natCast] using minSubnormalExponent_add_fracWidth fmt
  by_cases hle : exponent ≤ fmt.minSubnormalExponent
  · let shift := (fmt.minSubnormalExponent - exponent).toNat
    have hshiftInt :
        (shift : Int) = fmt.minSubnormalExponent - exponent :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hle)
    have hlogInt :
        (mantissa.log2 : Int) + 1 ≤ (fmt.fracWidth : Int) + shift := by
      rw [hshiftInt]
      omega
    have hlogNat : mantissa.log2 + 1 ≤ fmt.fracWidth + shift := by
      exact_mod_cast hlogInt
    have hmLt : mantissa < 2 ^ (fmt.fracWidth + shift) :=
      (Nat.lt_log2_self (n := mantissa)).trans_le
        (Nat.pow_le_pow_right (by decide) hlogNat)
    have hq : mantissa >>> shift < pow2 fmt.fracWidth := by
      rw [Nat.shiftRight_eq_div_pow]
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
      rw [pow2_eq_two_pow, ← Nat.pow_add]
      exact hmLt
    simpa [roundMantissaAtExponentDown, hle, shift] using hq
  · have hlt : fmt.minSubnormalExponent < exponent := lt_of_not_ge hle
    let shift := (exponent - fmt.minSubnormalExponent).toNat
    have hshiftInt :
        (shift : Int) = exponent - fmt.minSubnormalExponent :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hlt.le)
    have hlogInt :
        (mantissa.log2 : Int) + shift < fmt.fracWidth := by
      rw [hshiftInt]
      omega
    have hlogNat : mantissa.log2 + shift < fmt.fracWidth := by
      exact_mod_cast hlogInt
    have hraw :=
      Nat.shiftLeft_lt (m := shift) (Nat.lt_log2_self (n := mantissa))
    have hexponent : mantissa.log2 + 1 + shift ≤ fmt.fracWidth := by
      omega
    have hpow : 2 ^ (mantissa.log2 + 1 + shift) ≤ 2 ^ fmt.fracWidth :=
      Nat.pow_le_pow_right (by decide) hexponent
    simpa [roundMantissaAtExponentDown, hle, shift, pow2_eq_two_pow] using
      hraw.trans_le hpow

/--
Upward rounding below the normal range reaches at most the smallest normal mantissa.
-/
theorem roundMantissaAtExponentUp_minSubnormal_le_pow2
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hk : (mantissa.log2 : Int) + exponent <
      fmt.minNormalExponent) :
    roundMantissaAtExponentUp mantissa exponent (fmt.minSubnormalExponent) ≤
      pow2 fmt.fracWidth := by
  have hscale :
      fmt.minSubnormalExponent + (fmt.fracWidth : Int) =
        fmt.minNormalExponent := by
    simpa only [Int.ofNat_eq_natCast] using minSubnormalExponent_add_fracWidth fmt
  by_cases hle : exponent ≤ fmt.minSubnormalExponent
  · let shift := (fmt.minSubnormalExponent - exponent).toNat
    have hshiftInt :
        (shift : Int) = fmt.minSubnormalExponent - exponent :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hle)
    have hlogInt :
        (mantissa.log2 : Int) + 1 ≤ (fmt.fracWidth : Int) + shift := by
      rw [hshiftInt]
      omega
    have hlogNat : mantissa.log2 + 1 ≤ fmt.fracWidth + shift := by
      exact_mod_cast hlogInt
    have hmLt : mantissa < 2 ^ (fmt.fracWidth + shift) :=
      (Nat.lt_log2_self (n := mantissa)).trans_le
        (Nat.pow_le_pow_right (by decide) hlogNat)
    have hq : mantissa >>> shift < pow2 fmt.fracWidth := by
      rw [Nat.shiftRight_eq_div_pow]
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
      rw [pow2_eq_two_pow, ← Nat.pow_add]
      exact hmLt
    have hround := shiftRightCeilPow2_le_shiftRight_add_one mantissa shift
    simp only [roundMantissaAtExponentUp, hle, ite_true]
    change shiftRightCeilPow2 mantissa shift ≤ pow2 fmt.fracWidth
    exact hround.trans (Nat.succ_le_iff.mpr hq)
  · have hlt : fmt.minSubnormalExponent < exponent := lt_of_not_ge hle
    let shift := (exponent - fmt.minSubnormalExponent).toNat
    have hshiftInt :
        (shift : Int) = exponent - fmt.minSubnormalExponent :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hlt.le)
    have hlogInt :
        (mantissa.log2 : Int) + shift < fmt.fracWidth := by
      rw [hshiftInt]
      omega
    have hlogNat : mantissa.log2 + shift < fmt.fracWidth := by
      exact_mod_cast hlogInt
    have hraw :=
      Nat.shiftLeft_lt (m := shift) (Nat.lt_log2_self (n := mantissa))
    have hexponent : mantissa.log2 + 1 + shift ≤ fmt.fracWidth := by
      omega
    have hpow : 2 ^ (mantissa.log2 + 1 + shift) ≤ 2 ^ fmt.fracWidth :=
      Nat.pow_le_pow_right (by decide) hexponent
    simp only [roundMantissaAtExponentUp, hle, ite_false]
    change mantissa <<< shift ≤ pow2 fmt.fracWidth
    simpa [pow2_eq_two_pow] using (hraw.trans_le hpow).le

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
