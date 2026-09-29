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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Subtraction.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.ProductRound.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Proof
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Difference.Proof

/-!
# Two-word subtraction with equal exponents

The two-word subtraction kernel handles same-sign normal operands with equal exponents. Their
significand difference is exact, so the backend only subtracts, normalizes, adjusts the
exponent, and packs. Cancellation into the subnormal range and every unsupported case retain the
generic exact finite kernel. Start with `subNormalSameExponent_refines`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

open FloatLib.Numerics.FixedWord

variable {fmt : FloatFormat}

private theorem packNormalizedDifference_eq_round (h : Eligible fmt)
    (sign : Bool) (difference : UInt128) (exponent : UInt64)
    (hdifference : difference.toNat ≠ 0)
    (hdifferenceFit : difference.toNat < 2 ^ (fmt.fracWidth + 1))
    (hexponentPositive : 0 < exponent.toNat)
    (hexponentFinite : exponent.toNat < fmt.expAllOnesNat)
    (hnormal : fmt.fracWidth < exponent.toNat + difference.toNat.log2) :
    let leading := UInt128.log2 difference
    let normalized := UInt128.shiftLeft difference (fmt.fracWidth - leading)
    let encodedExponent := UInt64.ofNat (exponent.toNat + leading - fmt.fracWidth)
    packNormal fmt sign encodedExponent normalized =
      FiniteProductRound.round fmt sign difference.toNat
        (exponent.toNat + (fmt.bias + fmt.fracWidth - 2)) := by
  dsimp only
  have hfrac := h.frac_gt
  have hfracLe := h.frac_le
  have hallOnes := fmt.expAllOnesNat_eq_two_mul_bias_add_one
  have hbias := h.bias_lt
  have hleading : UInt128.log2 difference = difference.toNat.log2 :=
    UInt128.log2_toNat difference
  have hleadingLt : difference.toNat.log2 < fmt.fracWidth + 1 := by
    rw [Nat.log2_lt hdifference]
    exact hdifferenceFit
  have hleadingLe : difference.toNat.log2 ≤ fmt.fracWidth := by omega
  have hshiftLt : fmt.fracWidth - difference.toNat.log2 < 128 := by omega
  have hnormalizedLower :=
    two_pow_le_shiftLeft_sub_log2 fmt.fracWidth difference.toNat hdifference hleadingLe
  have hnormalizedUpper :=
    shiftLeft_sub_log2_lt_two_pow fmt.fracWidth difference.toNat hleadingLe
  have hnormalizedFit :
      difference.toNat <<< (fmt.fracWidth - difference.toNat.log2) < 2 ^ 128 :=
    lt_trans hnormalizedUpper (Nat.pow_lt_pow_right (by decide) (by omega))
  have hnormalized :
      (UInt128.shiftLeft difference
          (fmt.fracWidth - UInt128.log2 difference)).toNat =
        difference.toNat <<< (fmt.fracWidth - difference.toNat.log2) := by
    rw [hleading]
    exact UInt128.shiftLeft_toNat difference
      (fmt.fracWidth - difference.toNat.log2) hshiftLt hnormalizedFit
  have hencodedFinite :
      exponent.toNat + difference.toNat.log2 - fmt.fracWidth < fmt.expAllOnesNat := by
    omega
  have hencodedWord :
      (UInt64.ofNat
          (exponent.toNat + UInt128.log2 difference - fmt.fracWidth)).toNat =
        exponent.toNat + difference.toNat.log2 - fmt.fracWidth := by
    rw [hleading, UInt64.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    norm_num at hbias ⊢
    omega
  rw [packNormal_eq_ofFields h sign
    (UInt64.ofNat (exponent.toNat + UInt128.log2 difference - fmt.fracWidth))
    (UInt128.shiftLeft difference (fmt.fracWidth - UInt128.log2 difference))]
  · rw [hencodedWord, hnormalized]
    have hnormalBranch :
        ¬difference.toNat.log2 + (exponent.toNat + (fmt.bias + fmt.fracWidth - 2)) <
          fmt.bias + 2 * fmt.fracWidth - 1 := by
      omega
    have hnormalizedForm :
        (if fmt.fracWidth ≤ difference.toNat.log2 then
            Numerics.roundShiftRightEven difference.toNat
              (difference.toNat.log2 - fmt.fracWidth)
          else
            difference.toNat <<< (fmt.fracWidth - difference.toNat.log2)) =
          difference.toNat <<< (fmt.fracWidth - difference.toNat.log2) := by
      by_cases htop : difference.toNat.log2 = fmt.fracWidth
      · simp [htop]
      · have hsmall : difference.toNat.log2 < fmt.fracWidth := by omega
        simp [Nat.not_le_of_lt hsmall]
    have hcarry :
        difference.toNat <<< (fmt.fracWidth - difference.toNat.log2) ≠
          pow2 (fmt.fracWidth + 1) := by
      rw [pow2_eq_two_pow]
      exact Nat.ne_of_lt hnormalizedUpper
    have hoverflow :
        ¬3 * fmt.bias + 2 * fmt.fracWidth - 2 <
          difference.toNat.log2 + (exponent.toNat + (fmt.bias + fmt.fracWidth - 2)) := by
      omega
    have hencoded :
        difference.toNat.log2 + (exponent.toNat + (fmt.bias + fmt.fracWidth - 2)) -
            (fmt.bias + 2 * fmt.fracWidth - 2) =
          exponent.toNat + difference.toNat.log2 - fmt.fracWidth := by
      omega
    unfold FiniteProductRound.round
    simp only [beq_iff_eq, hdifference, ite_false]
    rw [ite_eq_right hnormalBranch, hnormalizedForm, ite_eq_right hcarry,
      ite_eq_right hoverflow, hencoded,
      ite_eq_right hcarry]
  · rw [hencodedWord, fmt.two_pow_expWidth_eq_two_mul_bias_add_two]
    omega
  · rw [hnormalized]
    exact hnormalizedLower
  · rw [hnormalized]
    exact hnormalizedUpper

private theorem decode_neg_of_normalExponent (h : Eligible fmt) (x : Model fmt)
    (hexponentZero : expField fmt (toWords x).hi ≠ 0)
    (hexponentFinite : expField fmt (toWords x).hi ≠ expAllOnes fmt) :
    FiniteKernel.decodeOption (neg x) =
      some {
        sign := !signBit fmt (toWords x).hi
        exponent := (expField fmt (toWords x).hi).toNat
        mantissa :=
          (normalMantissa fmt (fracHigh fmt (toWords x).hi)
            (toWords x).lo).toNat } := by
  rw [FiniteKernel.decodeOption_neg h.isIEEE,
    decode_of_normalExponent h x hexponentZero hexponentFinite]
  rfl

private theorem addComponents_opposite_large_left (h : Eligible fmt)
    (sign : Bool) (large small exponent : Nat)
    (hexponent : exponent ≠ 0) (hsmall : small ≠ 0)
    (hlt : small < large) :
    FiniteKernel.addComponents fmt
        { sign, exponent, mantissa := large }
        { sign := !sign, exponent, mantissa := small } =
      FiniteProductRound.round fmt sign (large - small)
        (exponent + (fmt.bias + fmt.fracWidth - 2)) := by
  have hlarge : large ≠ 0 := by omega
  unfold FiniteKernel.addComponents
  rw [← roundDyadic_eq_roundDyadicImpl,
    normalComponents_toDyadic h sign exponent large hexponent hlarge,
    normalComponents_toDyadic h (!sign) exponent small hexponent hsmall,
    addDyadic_oppositeSign_sameExponent_largeLeft sign (!sign) large small
      (Int.ofNat exponent - Int.ofNat (fmt.bias + fmt.fracWidth)) hlarge hsmall
      (by cases sign <;> decide) hlt,
    FiniteProductRound.round_eq_roundDyadic fmt h.isIEEE]
  rw [roundScaleExponent h]

private theorem addComponents_opposite_large_right (h : Eligible fmt)
    (sign : Bool) (small large exponent : Nat)
    (hexponent : exponent ≠ 0) (hsmall : small ≠ 0)
    (hlt : small < large) :
    FiniteKernel.addComponents fmt
        { sign, exponent, mantissa := small }
        { sign := !sign, exponent, mantissa := large } =
      FiniteProductRound.round fmt (!sign) (large - small)
        (exponent + (fmt.bias + fmt.fracWidth - 2)) := by
  have hlarge : large ≠ 0 := by omega
  unfold FiniteKernel.addComponents
  rw [← roundDyadic_eq_roundDyadicImpl,
    normalComponents_toDyadic h sign exponent small hexponent hsmall,
    normalComponents_toDyadic h (!sign) exponent large hexponent hlarge,
    addDyadic_oppositeSign_sameExponent_largeRight sign (!sign) small large
      (Int.ofNat exponent - Int.ofNat (fmt.bias + fmt.fracWidth)) hsmall hlarge
      (by cases sign <;> decide) hlt,
    FiniteProductRound.round_eq_roundDyadic fmt h.isIEEE]
  rw [roundScaleExponent h]

private theorem addComponents_opposite_equal (h : Eligible fmt)
    (sign : Bool) (mantissa exponent : Nat)
    (hexponent : exponent ≠ 0) (hmantissa : mantissa ≠ 0) :
    FiniteKernel.addComponents fmt
        { sign, exponent, mantissa }
        { sign := !sign, exponent, mantissa } =
      Model.posZero fmt := by
  unfold FiniteKernel.addComponents
  rw [normalComponents_toDyadic h sign exponent mantissa hexponent hmantissa,
    normalComponents_toDyadic h (!sign) exponent mantissa hexponent hmantissa]
  have hsum :
      addDyadic
          { negative := sign, significand := mantissa,
            exponent := Int.ofNat exponent - Int.ofNat (fmt.bias + fmt.fracWidth) }
          { negative := !sign, significand := mantissa,
            exponent := Int.ofNat exponent - Int.ofNat (fmt.bias + fmt.fracWidth) } =
        { negative := false, significand := 0, exponent := 0 } := by
    exact addDyadic_oppositeSign_sameExponent_eq_zero
      sign (!sign) mantissa (Int.ofNat exponent - Int.ofNat (fmt.bias + fmt.fracWidth))
      hmantissa (by cases sign <;> decide)
  rw [hsum]
  simp [roundDyadicImpl, h.isIEEE, ieeeRoundDyadicImpl]

/--
Every accepted native equal-exponent subtraction is exactly the existing finite path.

Rejected values retain `FiniteKernel.addOption x (neg y)`; this theorem is the trust boundary for
the
native specialization.
-/
theorem subNormalSameExponent_refines (h : Eligible fmt) (x y result : Model fmt)
    (hfast : subNormalSameExponentOption x y = some result) :
    FiniteKernel.addOption x (neg y) = some result := by
  unfold subNormalSameExponentOption at hfast
  dsimp only at hfast
  set xWords := toWords x with hxWords
  set yWords := toWords y with hyWords
  set xExponent := expField fmt xWords.hi with hxExponent
  set yExponent := expField fmt yWords.hi with hyExponent
  set xSign := signBit fmt xWords.hi with hxSign
  set ySign := signBit fmt yWords.hi with hySign
  set xFractionHigh := fracHigh fmt xWords.hi with hxFractionHigh
  set yFractionHigh := fracHigh fmt yWords.hi with hyFractionHigh
  set xMantissa := normalMantissa fmt xFractionHigh xWords.lo with hxMantissa
  set yMantissa := normalMantissa fmt yFractionHigh yWords.lo with hyMantissa
  have hsign : xSign = ySign := by
    by_contra hne
    simp [hne] at hfast
  have hxExponentZero : xExponent ≠ 0 := by
    intro hzero
    simp [hsign, hzero] at hfast
  have hxExponentFinite : xExponent ≠ expAllOnes fmt := by
    intro hexceptional
    simp [hsign, hexceptional] at hfast
  have hyExponentEq : yExponent = xExponent := by
    by_contra hne
    simp [hsign, hxExponentZero, hxExponentFinite, hne] at hfast
  have hyExponentZero : yExponent ≠ 0 := by
    rw [hyExponentEq]
    exact hxExponentZero
  have hyExponentFinite : yExponent ≠ expAllOnes fmt := by
    rw [hyExponentEq]
    exact hxExponentFinite
  have hxBounds :
      2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ (fmt.fracWidth + 1) :=
    normalMantissa_bounds h xFractionHigh xWords.lo (fracHigh_lt h xWords.hi)
  have hyBounds :
      2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ (fmt.fracWidth + 1) :=
    normalMantissa_bounds h yFractionHigh yWords.lo (fracHigh_lt h yWords.hi)
  have hxExponentBounds :=
    normalExponent_bounds h x hxExponentZero hxExponentFinite
  have hxExponentPositive : 0 < xExponent.toNat := hxExponentBounds.1
  have hxExponentFiniteNat : xExponent.toNat < fmt.expAllOnesNat := hxExponentBounds.2
  have hxMantissaNe : xMantissa.toNat ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hxBounds.1)
  have hyMantissaNe : yMantissa.toNat ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hyBounds.1)
  have hfracLe := h.frac_le
  by_cases hequal : xMantissa = yMantissa
  · have hresult : Model.posZero fmt = result := by
      simpa [hsign, hxExponentZero, hxExponentFinite, hyExponentEq,
        xFractionHigh, yFractionHigh, xMantissa, yMantissa, hequal]
        using hfast
    have hcomponents :
        FiniteKernel.addComponents fmt
            { sign := xSign
              exponent := xExponent.toNat
              mantissa := xMantissa.toNat }
            { sign := !xSign
              exponent := xExponent.toNat
              mantissa := yMantissa.toNat } =
          result := by
      rw [show yMantissa.toNat = xMantissa.toNat by rw [hequal]]
      rw [addComponents_opposite_equal h xSign xMantissa.toNat
        xExponent.toNat (Nat.ne_of_gt hxExponentPositive) hxMantissaNe]
      exact hresult
    unfold FiniteKernel.addOption
    rw [decode_of_normalExponent h x hxExponentZero hxExponentFinite,
      decode_neg_of_normalExponent h y hyExponentZero hyExponentFinite]
    simp only [Option.some.injEq]
    simpa [xWords, yWords, xExponent, yExponent, xSign, ySign,
      xFractionHigh, yFractionHigh, xMantissa, yMantissa, hxWords,
      hyWords, hsign, hyExponentEq] using hcomponents
  · by_cases hless : UInt128.less xMantissa yMantissa = true
    · have hxy : xMantissa.toNat < yMantissa.toNat :=
        (UInt128.less_eq_true_iff xMantissa yMantissa).mp hless
      let difference := UInt128.sub yMantissa xMantissa
      have hdifference : difference.toNat = yMantissa.toNat - xMantissa.toNat :=
        UInt128.sub_toNat yMantissa xMantissa hxy.le
      have hdifferenceNe : difference.toNat ≠ 0 := by
        rw [hdifference]
        omega
      have hdifferenceFit : difference.toNat < 2 ^ (fmt.fracWidth + 1) := by
        rw [hdifference]
        omega
      have haccepted :
          fmt.fracWidth < xExponent.toNat + UInt128.log2 difference ∧
            packNormal fmt (!xSign)
                (UInt64.ofNat (xExponent.toNat + UInt128.log2 difference - fmt.fracWidth))
                (UInt128.shiftLeft difference (fmt.fracWidth - UInt128.log2 difference)) =
              result := by
        simpa [hsign, hxExponentZero, hxExponentFinite, hyExponentEq,
          xFractionHigh, yFractionHigh, xMantissa, yMantissa, hequal,
          hless, difference] using hfast
      have hnormal : fmt.fracWidth < xExponent.toNat + difference.toNat.log2 := by
        simpa only [UInt128.log2_toNat] using haccepted.1
      have hpack :=
        packNormalizedDifference_eq_round h (!xSign) difference xExponent
          hdifferenceNe hdifferenceFit hxExponentPositive hxExponentFiniteNat hnormal
      have hcomponents :
          FiniteKernel.addComponents fmt
              { sign := xSign
                exponent := xExponent.toNat
                mantissa := xMantissa.toNat }
              { sign := !xSign
                exponent := xExponent.toNat
                mantissa := yMantissa.toNat } =
            result := by
        rw [addComponents_opposite_large_right h xSign
          xMantissa.toNat yMantissa.toNat xExponent.toNat
          (Nat.ne_of_gt hxExponentPositive) hxMantissaNe hxy, ← hdifference]
        exact hpack.symm.trans haccepted.2
      unfold FiniteKernel.addOption
      rw [decode_of_normalExponent h x hxExponentZero hxExponentFinite,
        decode_neg_of_normalExponent h y hyExponentZero hyExponentFinite]
      simp only [Option.some.injEq]
      simpa [xWords, yWords, xExponent, yExponent, xSign, ySign,
        xFractionHigh, yFractionHigh, xMantissa, yMantissa, hxWords,
        hyWords, hsign, hyExponentEq] using hcomponents
    · have hnotLt : ¬xMantissa.toNat < yMantissa.toNat := by
        intro hxy
        exact hless ((UInt128.less_eq_true_iff xMantissa yMantissa).mpr hxy)
      have hnatNe : xMantissa.toNat ≠ yMantissa.toNat := by
        intro hvalue
        exact hequal (UInt128.toNat_injective hvalue)
      have hyx : yMantissa.toNat < xMantissa.toNat := by omega
      let difference := UInt128.sub xMantissa yMantissa
      have hdifference : difference.toNat = xMantissa.toNat - yMantissa.toNat :=
        UInt128.sub_toNat xMantissa yMantissa hyx.le
      have hdifferenceNe : difference.toNat ≠ 0 := by
        rw [hdifference]
        omega
      have hdifferenceFit : difference.toNat < 2 ^ (fmt.fracWidth + 1) := by
        rw [hdifference]
        omega
      have haccepted :
          fmt.fracWidth < xExponent.toNat + UInt128.log2 difference ∧
            packNormal fmt xSign
                (UInt64.ofNat (xExponent.toNat + UInt128.log2 difference - fmt.fracWidth))
                (UInt128.shiftLeft difference (fmt.fracWidth - UInt128.log2 difference)) =
              result := by
        simpa [hsign, hxExponentZero, hxExponentFinite, hyExponentEq,
          xFractionHigh, yFractionHigh, xMantissa, yMantissa, hequal,
          hless, difference] using hfast
      have hnormal : fmt.fracWidth < xExponent.toNat + difference.toNat.log2 := by
        simpa only [UInt128.log2_toNat] using haccepted.1
      have hpack :=
        packNormalizedDifference_eq_round h xSign difference xExponent
          hdifferenceNe hdifferenceFit hxExponentPositive hxExponentFiniteNat hnormal
      have hcomponents :
          FiniteKernel.addComponents fmt
              { sign := xSign
                exponent := xExponent.toNat
                mantissa := xMantissa.toNat }
              { sign := !xSign
                exponent := xExponent.toNat
                mantissa := yMantissa.toNat } =
            result := by
        rw [addComponents_opposite_large_left h xSign
          xMantissa.toNat yMantissa.toNat xExponent.toNat
          (Nat.ne_of_gt hxExponentPositive) hyMantissaNe hyx, ← hdifference]
        exact hpack.symm.trans haccepted.2
      unfold FiniteKernel.addOption
      rw [decode_of_normalExponent h x hxExponentZero hxExponentFinite,
        decode_neg_of_normalExponent h y hyExponentZero hyExponentFinite]
      simp only [Option.some.injEq]
      simpa [xWords, yWords, xExponent, yExponent, xSign, ySign,
        xFractionHigh, yFractionHigh, xMantissa, yMantissa, hxWords,
        hyWords, hsign, hyExponentEq] using hcomponents

/-- The two-word finite subtraction chain equals exact addition with a negated right operand. -/
theorem subFinite_eq (h : Eligible fmt) (x y : Model fmt) :
    subFiniteOption x y = FiniteKernel.addOption x (neg y) := by
  unfold subFiniteOption
  cases hfast : subNormalSameExponentOption x y with
  | none => exact FiniteKernel.addRuntime_eq x (neg y)
  | some result =>
      rw [subNormalSameExponent_refines h x y result hfast]

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
