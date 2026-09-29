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

public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Rounding.Accuracy.Proof
import LeanPool.FloatLibBinary.Numerics.Bitwise
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.Arithmetic.Proof
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Basic
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.DirectedSemantics.Finite

/-!
# Correctness of binary square root

Lean's unpacked floating-point square root computes an integer square root and records whether the
discarded real fraction is below or above one half. This module proves that certificate correct,
connects the positive finite executable path to Lean's unpacked square-root model, proves that the
square root of a finite nonnegative value never overflows, and concludes that the result for a
conventional IEEE descriptor is one nearest-even rounding of the exact real square root.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model.UnpackedFloat
open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

/--
The residual classification produced from an integer square root locates the exact real square
root in the unit interval beginning at `Nat.sqrt n`, with the correct half-way comparison.
-/
theorem accuracyRepresents_natSqrt (n : Nat) :
    let root := Nat.sqrt n
    let remainder := n - root * root
    let accuracy : Accuracy :=
      if remainder = 0 then
        .exact
      else
        .inexact (if remainder ≤ root then .lt else .gt)
    accuracyRepresents root accuracy (Real.sqrt n) := by
  dsimp only
  let root := Nat.sqrt n
  let remainder := n - root * root
  change accuracyRepresents root
    (if remainder = 0 then
      .exact
    else
      .inexact (if remainder ≤ root then .lt else .gt))
    (Real.sqrt n)
  have hrootSq : root * root ≤ n := by
    simpa [root] using Nat.sqrt_le n
  have hnDecomp : n = root * root + remainder := by
    dsimp only [remainder]
    omega
  have hsqrtNonneg : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt n) ^ 2 = n := by
    simp [Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)]
  by_cases hremainderZero : remainder = 0
  · simp only [ite_eq_left hremainderZero, accuracyRepresents]
    have hnEq : n = root * root := by omega
    rw [hnEq]
    norm_num [Nat.cast_mul, Real.sqrt_sq_eq_abs]
  · have hrootLt : (root : ℝ) < Real.sqrt n := by
      have hnLt : root * root < n := by omega
      have hnLtCast : (root : ℝ) * root < (n : ℝ) := by
        exact_mod_cast hnLt
      have hrootNonneg : (0 : ℝ) ≤ root := by positivity
      nlinarith [hsqrtSq, hnLtCast]
    by_cases hremainderLe : remainder ≤ root
    · simp only [ite_eq_right hremainderZero, ite_eq_left hremainderLe, accuracyRepresents]
      constructor
      · exact hrootLt
      · have hremainderCast : (remainder : ℝ) ≤ root := by exact_mod_cast hremainderLe
        have hnDecompCast :
            (n : ℝ) = (root : ℝ) * root + remainder := by
          exact_mod_cast hnDecomp
        nlinarith [hsqrtSq]
    · simp only [ite_eq_right hremainderZero, ite_eq_right hremainderLe, accuracyRepresents]
      constructor
      · have hremainderLower : root + 1 ≤ remainder := by omega
        have hremainderCast : (root : ℝ) + 1 ≤ remainder := by
          exact_mod_cast hremainderLower
        have hnDecompCast :
            (n : ℝ) = (root : ℝ) * root + remainder := by
          exact_mod_cast hnDecomp
        nlinarith [hsqrtSq]
      · exact Real.real_sqrt_lt_nat_sqrt_succ

private theorem log2_sqrt (n : Nat) (hn : n ≠ 0) :
    (Nat.sqrt n).log2 = n.log2 / 2 := by
  have hsqrtPos : 0 < Nat.sqrt n := (Nat.sqrt_pos).2 (Nat.pos_of_ne_zero hn)
  apply (Nat.log2_eq_iff (Nat.ne_of_gt hsqrtPos)).2
  constructor
  · rw [Nat.le_sqrt, ← Nat.pow_add]
    calc
      2 ^ (n.log2 / 2 + n.log2 / 2) ≤ 2 ^ n.log2 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ n := Nat.log2_self_le hn
  · rw [Nat.sqrt_lt, ← Nat.pow_add]
    calc
      n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
      _ ≤ 2 ^ ((n.log2 / 2 + 1) + (n.log2 / 2 + 1)) :=
        Nat.pow_le_pow_right (by decide) (by omega)

private theorem totalExponent_sqrt_shift
    (mantissa shift root : Nat) (exponent target : Int)
    (hmantissa : mantissa ≠ 0)
    (hshift : (shift : Int) = exponent - 2 * target)
    (hroot : root = Nat.sqrt (mantissa <<< shift)) :
    Float.Model.totalExponent root target =
      (Float.Model.totalExponent mantissa exponent + 1).ediv 2 := by
  have hscaled : mantissa <<< shift ≠ 0 := by
    simp [Nat.shiftLeft_eq, hmantissa]
  unfold Float.Model.totalExponent
  rw [hroot, log2_sqrt _ hscaled,
    Nat.log2_shiftLeft_of_ne_zero mantissa shift hmantissa]
  change Int.ofNat ((mantissa.log2 + shift) / 2) + 1 + target =
    (Int.ofNat mantissa.log2 + 1 + exponent + 1) / 2
  simp only [Int.ofNat_eq_natCast] at *
  omega

private theorem sqrt_shift_mul_bpow
    (mantissa shift : Nat) (exponent target : Int)
    (hshift : (shift : Int) = exponent - 2 * target) :
    Real.sqrt (mantissa <<< shift : Nat) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix target =
      Real.sqrt ((mantissa : Real) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent) := by
  have hscaledNonneg : (0 : Real) ≤ (mantissa <<< shift : Nat) := by
    positivity
  have hsourceNonneg :
      (0 : Real) ≤ (mantissa : Real) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent :=
    mul_nonneg (by positivity) (bpow.pos _ _).le
  have hlhsNonneg :
      0 ≤ Real.sqrt (mantissa <<< shift : Nat) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix target :=
    mul_nonneg (Real.sqrt_nonneg _) (bpow.pos _ _).le
  apply Eq.symm
  apply (Real.sqrt_eq_iff_eq_sq hsourceNonneg hlhsNonneg).2
  rw [mul_pow, Real.sq_sqrt hscaledNonneg]
  have hcastShift :
      ((mantissa <<< shift : Nat) : Real) =
        (mantissa : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (Int.ofNat shift) := by
    rw [Nat.shiftLeft_eq, Nat.cast_mul]
    simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
      Numerics.Radix.toReal]
  rw [hcastShift]
  have hbpowSq :
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix target ^ 2 =
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (2 * target) := by
    rw [pow_two, ← bpow.add_exp]
    congr 1
    ring
  rw [hbpowSq, mul_assoc, ← bpow.add_exp]
  have hshiftInt : Int.ofNat shift = exponent - 2 * target := by
    simpa using hshift
  have hexponent : exponent = Int.ofNat shift + 2 * target := by
    omega
  rw [hexponent]

/--
Lean's positive finite model square root has the same real value as independent nearest-even
rounding of the exact real square root whenever the packed result is finite.
-/
theorem toReal_ofModel_sqrt_finite_eq_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mantissa : Nat) (exponent : Int)
    (hmantissa : mantissa ≠ 0)
    (hfinite :
      isFinite
        (ofModel fmt
          (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
            (.finite .positive mantissa exponent
              (Nat.pos_of_ne_zero hmantissa)))) = true) :
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
            (.finite .positive mantissa exponent
              (Nat.pos_of_ne_zero hmantissa)))) =
      roundAt fmt
        (Real.sqrt ((mantissa : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent)) := by
  let spec := FloatFormat.toModel fmt
  let total := (Float.Model.totalExponent mantissa exponent + 1).ediv 2
  let target := min (exponent.ediv 2) (spec.targetExponent total)
  let shift := (exponent - 2 * target).toNat
  let scaled := mantissa <<< shift
  let root := Nat.sqrt scaled
  let remainder := scaled - root * root
  let accuracy : Accuracy :=
    if remainder = 0 then .exact
    else .inexact (if remainder ≤ root then .lt else .gt)
  have htargetLeHalf : target ≤ exponent.ediv 2 := min_le_left _ _
  have htwiceTargetLe : 2 * target ≤ exponent := by
    have h := Int.mul_le_of_le_ediv (a := target) (b := exponent) (c := 2)
      (by norm_num) htargetLeHalf
    omega
  have hshiftNonneg : 0 ≤ exponent - 2 * target := by
    omega
  have hshiftInt : (shift : Int) = exponent - 2 * target := by
    exact Int.toNat_of_nonneg hshiftNonneg
  have hscaledNe : scaled ≠ 0 := by
    simp [scaled, Nat.shiftLeft_eq, hmantissa]
  have hrootNe : root ≠ 0 := by
    exact Nat.ne_of_gt ((Nat.sqrt_pos).2 (Nat.pos_of_ne_zero hscaledNe))
  have haccuracy :
      accuracyRepresents root accuracy (Real.sqrt scaled) := by
    simpa [root, remainder, accuracy] using accuracyRepresents_natSqrt scaled
  have htotalRoot :
      Float.Model.totalExponent root target = total := by
    exact totalExponent_sqrt_shift mantissa shift root exponent target
      hmantissa hshiftInt rfl
  have htargetLe :
      target ≤ spec.targetExponent
        (Float.Model.totalExponent root target) := by
    have hright : target ≤ spec.targetExponent total := min_le_right _ _
    simpa [htotalRoot] using hright
  have hround :=
    toReal_ofModel_roundWithAccuracy_eq_roundAt
      fmt hfmt .positive root target accuracy (Real.sqrt scaled)
      hrootNe haccuracy htargetLe
      (by
        simpa [spec, total, target, shift, scaled, root, remainder, accuracy,
          Float.Model.UnpackedFloat.sqrt,
          Float.Model.UnpackedFloat.sqrtCore] using hfinite)
  have hscale :=
    sqrt_shift_mul_bpow mantissa shift exponent target hshiftInt
  simpa [spec, total, target, shift, scaled, root, remainder, accuracy,
    Float.Model.UnpackedFloat.sqrt, Float.Model.UnpackedFloat.sqrtCore,
    hscale] using hround

/-!
## Square root never overflows

The largest finite value of every IEEE descriptor exceeds one, so its square root is below it and
the rounded result stays inside the finite range. We first show that packing a model value whose
biased exponent is in range yields a finite word, then that `roundWithAccuracy` of a certified real
below `2^maxNormal` packs to such a value.
-/

/--
Packing a finite model value whose biased exponent stays below the all-ones pattern yields a
finite word. This is the converse of `noOverflow_of_isFinite_ofModel_finite`.
-/
theorem isFinite_ofModel_finite_of_noOverflow
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Sign) (mantissa : Nat) (exponent : Int) (hm : mantissa ≠ 0)
    (hnoOverflow :
      ¬2 ^ (FloatFormat.toModel fmt).exponentBits ≤
        (exponent + (FloatFormat.toModel fmt).exponentBias +
          (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat + 1) :
    isFinite (ofModel fmt (.finite sign mantissa exponent (Nat.pos_of_ne_zero hm))) = true := by
  have hencoding := (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt |>.1
  have hlt :
      (exponent + (FloatFormat.toModel fmt).exponentBias +
          (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat + 1 <
        2 ^ fmt.expWidth :=
    Nat.lt_of_not_le hnoOverflow
  have hallOnes : 0 < FloatFormat.expAllOnesNat fmt := FloatFormat.expAllOnesNat_pos fmt
  simp only [isFinite, hencoding, IEEE.isFinite, bne_iff_ne, ne_eq]
  rw [← unpackExponent_toNat]
  unfold ofModel toModelBits ofModelBits Float.Model.UnpackedFloat.pack
  simp only [hnoOverflow, ite_false]
  split_ifs
  · rw [Float.Model.UnpackedFloat.unpackExponent_packComponents, BitVec.toNat_ofNat]
    change ¬ _ % 2 ^ fmt.expWidth = FloatFormat.expAllOnesNat fmt
    rw [Nat.mod_eq_of_lt (by omega)]
    unfold FloatFormat.expAllOnesNat
    omega
  · rw [Float.Model.UnpackedFloat.unpackExponent_packComponents]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega

/--
Rounding a positive certified real whose magnitude is below `2^maxNormal` never overflows, so the
packed result is finite. The exponent premise is the documented precondition of
`roundWithAccuracy`: normalization may discard low bits but never shifts left.
-/
theorem isFinite_ofModel_roundWithAccuracy_of_lt_bpow
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Sign) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) (value : Real)
    (hmantissa : mantissa ≠ 0)
    (haccuracy : accuracyRepresents mantissa accuracy value)
    (hle : exponent ≤
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent))
    (hbound :
      value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent <
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt))) :
    isFinite
      (ofModel fmt
        (Float.Model.UnpackedFloat.roundWithAccuracy
          (FloatFormat.toModel fmt) sign mantissa exponent accuracy)) = true := by
  let k : Int := Int.ofNat mantissa.log2 + exponent
  let target : Int :=
    (FloatFormat.toModel fmt).targetExponent
      (Float.Model.totalExponent mantissa exponent)
  let scaled : Real :=
    value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (exponent - target)
  let rounded : Nat :=
    (Float.Model.UnpackedFloat.shiftToTargetExponent
      (FloatFormat.toModel fmt) mantissa exponent accuracy).1.roundedMantissa
  have hvaluePos : 0 < value := by
    have hbounds := accuracyRepresents_bounds haccuracy
    have hmantissaPos : (0 : Real) < mantissa := by
      exact_mod_cast Nat.pos_of_ne_zero hmantissa
    exact hmantissaPos.trans_le hbounds.1
  have hexactPos :
      0 < value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent :=
    mul_pos hvaluePos (bpow.pos _ _)
  have hmagnitude :
      magnitude Numerics.binaryRadix
          (value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent) =
        k + 1 := by
    dsimp only [k]
    rw [magnitude_mul_bpow _ _ _ hvaluePos.ne',
      magnitude_of_accuracyRepresents hmantissa haccuracy]
    ring
  have hk : k + 1 ≤ Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
    rw [← hmagnitude]
    exact magnitude_le_of_abs_lt_bpow Numerics.binaryRadix _ _ hexactPos.ne'
      (by rw [abs_of_pos hexactPos]; exact hbound)
  have hscaled :
      scaledMantissa Numerics.binaryRadix (fexpOf fmt)
          (value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent) =
        scaled :=
    scaledMantissa_accuracy_mul_bpow fmt mantissa exponent accuracy value hfmt hmantissa haccuracy
  have hrounded : Int.ofNat rounded = nearestEven scaled :=
    roundedMantissa_shiftToTargetExponent_eq_nearestEven fmt mantissa exponent accuracy value
      haccuracy hle
  have hbias := FloatFormat.two_pow_expWidth_eq_two_mul_bias_add_two fmt
  have hbiasPos : 1 ≤ fmt.bias := by
    have hfour : 4 ≤ 2 ^ fmt.expWidth := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) fmt.expWidth_ge_two
    omega
  rw [roundWithAccuracy_eq_finishRoundedMantissa,
    shiftToTargetExponent_eq_of_le_targetExponent fmt mantissa exponent accuracy hle]
  change
    isFinite
      (ofModel fmt
        (finishRoundedMantissa (FloatFormat.toModel fmt) sign (rounded, target))) = true
  by_cases hsub : k < FloatFormat.ieeeMinNormalExponent fmt
  · have htargetMin : target = FloatFormat.ieeeMinSubnormalExponent fmt :=
      targetExponent_eq_minSubnormal_of_lt_minNormal fmt mantissa exponent hsub
    have hupperExact :
        value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent <
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (FloatFormat.ieeeMinSubnormalExponent fmt + fmt.fracWidth) := by
      have hupper :=
        abs_lt_bpow_magnitude Numerics.binaryRadix
          (value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent)
          hexactPos.ne'
      rw [abs_of_pos hexactPos, hmagnitude] at hupper
      refine hupper.trans_le ((bpow_le_bpow_iff Numerics.binaryRadix _ _).2 ?_)
      unfold FloatFormat.ieeeMinNormalExponent at hsub
      unfold FloatFormat.ieeeMinSubnormalExponent
      simp only [Int.ofNat_eq_natCast] at hsub ⊢
      omega
    have hscaledLe : scaled ≤ (pow2 fmt.fracWidth : Real) := by
      have hdenPos :
          0 < FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (FloatFormat.ieeeMinSubnormalExponent fmt) := bpow.pos _ _
      apply le_of_mul_le_mul_right (a0 := hdenPos)
      calc
        scaled * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (FloatFormat.ieeeMinSubnormalExponent fmt) =
            value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent := by
          dsimp only [scaled]
          rw [htargetMin, mul_assoc, ← bpow.add_exp]
          congr 1
          ring_nf
        _ ≤ FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (FloatFormat.ieeeMinSubnormalExponent fmt + fmt.fracWidth) :=
          hupperExact.le
        _ = (pow2 fmt.fracWidth : Real) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (FloatFormat.ieeeMinSubnormalExponent fmt) := by
          rw [natCast_pow2_eq_bpow, ← bpow.add_exp]
          congr 1
          ring
    have hroundedLe : rounded ≤ pow2 fmt.fracWidth :=
      Int.ofNat_le.mp (hrounded.trans_le (nearestEven_le_natCast_of_le hscaledLe))
    rw [htargetMin]
    by_cases hzero : rounded = 0
    · rw [hzero, finishRoundedMantissa_zero]
      exact isFinite_ofModel_zero fmt hfmt sign
    · rw [finishRoundedMantissa_at_minSubnormal fmt sign rounded hzero hroundedLe]
      apply isFinite_ofModel_finite_of_noOverflow fmt hfmt sign rounded _ hzero
      change
        ¬2 ^ fmt.expWidth ≤
          (FloatFormat.ieeeMinSubnormalExponent fmt + fmt.bias + fmt.fracWidth).toNat + 1
      simp only [FloatFormat.ieeeMinSubnormalExponent, Int.ofNat_eq_natCast]
      omega
  · have hnormal : FloatFormat.ieeeMinNormalExponent fmt ≤ k := le_of_not_gt hsub
    have htargetNormal : target = k - fmt.fracWidth :=
      targetExponent_eq_normal fmt mantissa exponent hnormal
    have hlowerExact :
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix k ≤
          value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent := by
      have hlower :=
        bpow_magnitude_sub_one_le Numerics.binaryRadix
          (value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent)
          hexactPos.ne'
      simpa [abs_of_pos hexactPos, hmagnitude] using hlower
    have hupperExact :
        value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent <
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k + 1) := by
      have hupper :=
        abs_lt_bpow_magnitude Numerics.binaryRadix
          (value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent)
          hexactPos.ne'
      simpa [abs_of_pos hexactPos, hmagnitude] using hupper
    have hdenPos :
        0 < FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k - fmt.fracWidth) :=
      bpow.pos _ _
    have hscaledEq :
        scaled * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k - fmt.fracWidth) =
          value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent := by
      dsimp only [scaled]
      rw [htargetNormal, mul_assoc, ← bpow.add_exp]
      congr 1
      ring_nf
    have hscaledLower : (pow2 fmt.fracWidth : Real) ≤ scaled := by
      apply le_of_mul_le_mul_right (a0 := hdenPos)
      calc
        (pow2 fmt.fracWidth : Real) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k - fmt.fracWidth) =
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix k := by
          rw [natCast_pow2_eq_bpow, ← bpow.add_exp]
          congr 1
          ring
        _ ≤ value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent :=
          hlowerExact
        _ = scaled *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k - fmt.fracWidth) :=
          hscaledEq.symm
    have hscaledUpper : scaled ≤ (pow2 (fmt.fracWidth + 1) : Real) := by
      apply le_of_mul_le_mul_right (a0 := hdenPos)
      calc
        scaled * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k - fmt.fracWidth) =
            value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent :=
          hscaledEq
        _ ≤ FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k + 1) := hupperExact.le
        _ = (pow2 (fmt.fracWidth + 1) : Real) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k - fmt.fracWidth) := by
          rw [natCast_pow2_eq_bpow, ← bpow.add_exp]
          congr 1
          push_cast
          ring
    have hroundedLow : pow2 fmt.fracWidth ≤ rounded :=
      Int.ofNat_le.mp ((natCast_le_nearestEven_of_le hscaledLower).trans hrounded.symm.le)
    have hroundedHigh : rounded ≤ pow2 (fmt.fracWidth + 1) :=
      Int.ofNat_le.mp (hrounded.trans_le (nearestEven_le_natCast_of_le hscaledUpper))
    have hkBias : k + 1 ≤ Int.ofNat fmt.bias := by
      simpa [FloatFormat.ieeeMaxNormalExponent] using hk
    have hkMin : (1 : Int) - Int.ofNat fmt.bias ≤ k := by
      simpa [FloatFormat.ieeeMinNormalExponent] using hnormal
    by_cases hcarry : rounded = pow2 (fmt.fracWidth + 1)
    · rw [htargetNormal, hcarry, finishRoundedMantissa_normalized_carry fmt sign k hnormal]
      apply isFinite_ofModel_finite_of_noOverflow fmt hfmt sign _ _ (by simp [pow2_eq_two_pow])
      change ¬2 ^ fmt.expWidth ≤ (k + 1 - fmt.fracWidth + fmt.bias + fmt.fracWidth).toNat + 1
      have hexp : k + 1 - fmt.fracWidth + fmt.bias + fmt.fracWidth = k + 1 + fmt.bias := by
        ring
      rw [hexp, hbias]
      simp only [Int.ofNat_eq_natCast] at hkBias hkMin
      omega
    · have hhigh : rounded < pow2 (fmt.fracWidth + 1) := lt_of_le_of_ne hroundedHigh hcarry
      rw [htargetNormal, finishRoundedMantissa_normalized fmt sign rounded k hroundedLow hhigh
        hnormal]
      apply isFinite_ofModel_finite_of_noOverflow fmt hfmt sign _ _
        (Nat.ne_of_gt ((pow2_pos _).trans_le hroundedLow))
      change ¬2 ^ fmt.expWidth ≤ (k - fmt.fracWidth + fmt.bias + fmt.fracWidth).toNat + 1
      have hexp : k - fmt.fracWidth + fmt.bias + fmt.fracWidth = k + fmt.bias := by
        ring
      rw [hexp, hbias]
      simp only [Int.ofNat_eq_natCast] at hkBias hkMin
      omega

/--
Lean's positive finite model square root packs to a finite word whenever the radicand is below
`2^(2 * maxNormal)`, which every finite IEEE value is.
-/
theorem isFinite_modelSqrt_of_lt_bpow
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mantissa : Nat) (exponent : Int)
    (hmantissa : mantissa ≠ 0)
    (hbound :
      (mantissa : Real) * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent <
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (2 * Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt))) :
    isFinite
      (ofModel fmt
        (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
          (.finite .positive mantissa exponent (Nat.pos_of_ne_zero hmantissa)))) = true := by
  let spec := FloatFormat.toModel fmt
  let total := (Float.Model.totalExponent mantissa exponent + 1).ediv 2
  let target := min (exponent.ediv 2) (spec.targetExponent total)
  let shift := (exponent - 2 * target).toNat
  let scaled := mantissa <<< shift
  let root := Nat.sqrt scaled
  let remainder := scaled - root * root
  let accuracy : Accuracy :=
    if remainder = 0 then .exact
    else .inexact (if remainder ≤ root then .lt else .gt)
  have htargetLeHalf : target ≤ exponent.ediv 2 := min_le_left _ _
  have htwiceTargetLe : 2 * target ≤ exponent := by
    have h := Int.mul_le_of_le_ediv (a := target) (b := exponent) (c := 2)
      (by norm_num) htargetLeHalf
    omega
  have hshiftNonneg : 0 ≤ exponent - 2 * target := by
    omega
  have hshiftInt : (shift : Int) = exponent - 2 * target := by
    exact Int.toNat_of_nonneg hshiftNonneg
  have hscaledNe : scaled ≠ 0 := by
    simp [scaled, Nat.shiftLeft_eq, hmantissa]
  have hrootNe : root ≠ 0 := by
    exact Nat.ne_of_gt ((Nat.sqrt_pos).2 (Nat.pos_of_ne_zero hscaledNe))
  have haccuracy :
      accuracyRepresents root accuracy (Real.sqrt scaled) := by
    simpa [root, remainder, accuracy] using accuracyRepresents_natSqrt scaled
  have htotalRoot :
      Float.Model.totalExponent root target = total := by
    exact totalExponent_sqrt_shift mantissa shift root exponent target
      hmantissa hshiftInt rfl
  have htargetLe :
      target ≤ spec.targetExponent
        (Float.Model.totalExponent root target) := by
    have hright : target ≤ spec.targetExponent total := min_le_right _ _
    simpa [htotalRoot] using hright
  have hscale :=
    sqrt_shift_mul_bpow mantissa shift exponent target hshiftInt
  have hmaxPos :
      0 < FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)) := bpow.pos _ _
  have hsquare :
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)) ^ 2 =
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (2 * Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)) := by
    rw [pow_two, ← bpow.add_exp]
    congr 1
    ring
  have hsqrtBound :
      Real.sqrt scaled * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix target <
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)) := by
    rw [hscale]
    apply (Real.sqrt_lt' hmaxPos).2
    rw [hsquare]
    exact hbound
  have hfinite :=
    isFinite_ofModel_roundWithAccuracy_of_lt_bpow
      fmt hfmt .positive root target accuracy (Real.sqrt scaled)
      hrootNe haccuracy htargetLe hsqrtBound
  simpa [spec, total, target, shift, scaled, root, remainder, accuracy,
    Float.Model.UnpackedFloat.sqrt, Float.Model.UnpackedFloat.sqrtCore] using hfinite

/--
The square root of a finite nonnegative value, including either signed zero, is finite for every
conventional IEEE descriptor. The largest finite value exceeds one, so its square root lies below
it and rounding cannot reach infinity.
-/
theorem isFinite_sqrt_of_isFinite
    {fmt : FloatFormat} (x : Model fmt) (hfmt : fmt.isIEEE = true)
    (hfinite : isFinite x = true)
    (hdomain : isZero x = true ∨ signBit x = false) :
    isFinite (sqrt x) = true := by
  by_cases hzero : isZero x = true
  · have hsqrt : sqrt x = x := by
      rw [Proof.sqrt_eq_spec]
      simp [Spec.sqrt, chooseNaN1_none_of_isFinite x hfinite,
        isInf_eq_false_of_isFinite_eq_true x hfinite, hzero]
    rw [hsqrt]
    exact hfinite
  · have hnonnegative : signBit x = false := hdomain.resolve_left hzero
    have hnonzero : isZero x = false := Bool.eq_false_iff.mpr hzero
    obtain ⟨d, hd⟩ := exists_toDyadicOption_of_isFinite hfinite
    have hsign : d.negative = false :=
      (sign_eq_signBit_of_toDyadicOption_some hd).trans hnonnegative
    have hmantissa : d.significand ≠ 0 := by
      intro hzero'
      have hzeroResult :=
        isZero_eq_true_of_toDyadicOption_some_of_mant_eq_zero hd hzero'
      simp [hnonzero] at hzeroResult
    have hmodel :
        toModel x =
          .finite .positive d.significand d.exponent (Nat.pos_of_ne_zero hmantissa) := by
      have hieeeDecode : ieeeToDyadicOption x = some d := by
        simpa [toDyadicOption, hfmt] using hd
      simpa [hsign] using
        toModel_eq_finite_of_ieeeToDyadicOption_eq_some
          x d.negative d.significand d.exponent hmantissa hieeeDecode
    have hsqrt :
        sqrt x =
          ofModel fmt
            (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
              (.finite .positive d.significand d.exponent
                (Nat.pos_of_ne_zero hmantissa))) := by
      rw [Proof.sqrt_eq_spec, Spec.sqrt_eq_model hfmt x hfinite hnonzero hnonnegative, hmodel]
    have hxReal :
        toReal x =
          (d.significand : Real) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix d.exponent := by
      rw [toReal_eq, hd]
      simp [Numerics.Dyadic.toReal, hsign, Flocq.bpow, Numerics.binaryRadix,
        Numerics.Radix.toReal]
    have hxNonneg : 0 ≤ toReal x := by
      rw [hxReal]
      exact mul_nonneg (Nat.cast_nonneg _) (bpow.pos _ _).le
    have hxLe : toReal x ≤ toReal (posMaxFinite fmt) := by
      have := abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite x hfmt hfinite
      rwa [abs_of_nonneg hxNonneg] at this
    have hmaxLt := toReal_posMaxFinite_lt_bpow fmt
    rw [FloatFormat.maxNormalExponent_eq_ieee fmt hfmt] at hmaxLt
    have hbiasPos : 1 ≤ FloatFormat.ieeeMaxNormalExponent fmt := by
      have hwidth := fmt.expWidth_ge_two
      have hpow : 2 ≤ 2 ^ (fmt.expWidth - 1) := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega : 1 ≤ fmt.expWidth
          - 1)
      unfold FloatFormat.ieeeMaxNormalExponent FloatFormat.bias
      omega
    have hexpLe :
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) + 1) ≤
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (2 * Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)) :=
      (bpow_le_bpow_iff Numerics.binaryRadix _ _).2 (by
        simp only [Int.ofNat_eq_natCast]
        omega)
    have hbound :
        (d.significand : Real) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix d.exponent <
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (2 * Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)) := by
      rw [← hxReal]
      exact (hxLe.trans_lt hmaxLt).trans_le hexpLe
    rw [hsqrt]
    exact isFinite_modelSqrt_of_lt_bpow fmt hfmt d.significand d.exponent hmantissa hbound

private theorem toReal_sqrt_eq_roundAt_of_nonzero
    {fmt : FloatFormat} (x : Model fmt) (hfmt : fmt.isIEEE = true)
    (hfinite : isFinite x = true)
    (hnonzero : isZero x = false)
    (hnonnegative : signBit x = false)
    (hresult : isFinite (sqrt x) = true) :
    toReal (sqrt x) = roundAt fmt (Real.sqrt (toReal x)) := by
  obtain ⟨d, hd⟩ := exists_toDyadicOption_of_isFinite hfinite
  have hsign : d.negative = false :=
    (sign_eq_signBit_of_toDyadicOption_some hd).trans hnonnegative
  have hmantissa : d.significand ≠ 0 := by
    intro hzero
    have hzeroResult :=
      isZero_eq_true_of_toDyadicOption_some_of_mant_eq_zero hd hzero
    simp [hnonzero] at hzeroResult
  have hmodel :
      toModel x =
        .finite .positive d.significand d.exponent (Nat.pos_of_ne_zero hmantissa) := by
    have hieeeDecode : ieeeToDyadicOption x = some d := by
      simpa [toDyadicOption, hfmt] using hd
    simpa [hsign] using
      toModel_eq_finite_of_ieeeToDyadicOption_eq_some
        x d.negative d.significand d.exponent hmantissa hieeeDecode
  have hsqrt :
      sqrt x =
        ofModel fmt
          (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
            (.finite .positive d.significand d.exponent
              (Nat.pos_of_ne_zero hmantissa))) := by
    calc
      sqrt x = Spec.sqrt x := Proof.sqrt_eq_spec x
      _ = ofModel fmt
          (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
            (.finite .positive d.significand d.exponent
              (Nat.pos_of_ne_zero hmantissa))) := by
        simpa [hmodel] using
          Spec.sqrt_eq_model
            hfmt x hfinite hnonzero hnonnegative
  have hmodelFinite :
      isFinite
        (ofModel fmt
          (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
            (.finite .positive d.significand d.exponent
              (Nat.pos_of_ne_zero hmantissa)))) = true := by
    rw [← hsqrt]
    exact hresult
  have hxReal :
      toReal x =
        (d.significand : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix d.exponent := by
    rw [toReal_eq, hd]
    simp [Numerics.Dyadic.toReal, hsign, Flocq.bpow, Numerics.binaryRadix,
      Numerics.Radix.toReal]
  calc
    toReal (sqrt x) =
        toReal
          (ofModel fmt
            (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
              (.finite .positive d.significand d.exponent
                (Nat.pos_of_ne_zero hmantissa)))) := by
          rw [hsqrt]
    _ = roundAt fmt
          (Real.sqrt ((d.significand : Real) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix d.exponent)) :=
      toReal_ofModel_sqrt_finite_eq_roundAt
        fmt hfmt d.significand d.exponent hmantissa hmodelFinite
    _ = roundAt fmt (Real.sqrt (toReal x)) := by rw [hxReal]

/--
Generic executable square root performs one nearest-even rounding of the exact real square root
on every finite, nonnegative conventional IEEE input. The domain condition includes both signed
zeros. Unlike the other arithmetic operations, no finiteness of the result is assumed:
`isFinite_sqrt_of_isFinite` shows that square root cannot overflow.
-/
theorem toReal_sqrt_eq_roundAt
    {fmt : FloatFormat} (x : Model fmt) (hfmt : fmt.isIEEE = true)
    (hfinite : isFinite x = true)
    (hdomain : isZero x = true ∨ signBit x = false) :
    toReal (sqrt x) = roundAt fmt (Real.sqrt (toReal x)) := by
  have hresult : isFinite (sqrt x) = true := isFinite_sqrt_of_isFinite x hfmt hfinite hdomain
  by_cases hzero : isZero x = true
  · have hsqrt : sqrt x = x := by
      rw [Proof.sqrt_eq_spec]
      simp [Spec.sqrt, chooseNaN1_none_of_isFinite x hfinite,
        isInf_eq_false_of_isFinite_eq_true x hfinite, hzero]
    have hxReal : toReal x = 0 := by
      rw [toReal_eq, toDyadicOption_eq_zero_of_isZero_eq_true x hzero]
      simp [Numerics.Dyadic.toReal]
    rw [hsqrt, hxReal, Real.sqrt_zero, roundAt_zero]
  · exact toReal_sqrt_eq_roundAt_of_nonzero x hfmt hfinite
      (Bool.eq_false_iff.mpr hzero) (hdomain.resolve_left hzero) hresult

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
