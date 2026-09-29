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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Addition.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.Kernel.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.ProductRound.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Proof
public import LeanPool.FloatLibBinary.Kernels.FixedWord.LimbRound.Proof

/-!
# Two-word addition with equal exponents

The two-word addition kernel handles same-sign normal operands with equal exponents. Their exact
`fracWidth + 2`-bit significand sum is rounded once to nearest-even and packed directly. Unequal
exponents, opposite signs, subnormals, exceptional values, and overflow boundaries retain the
generic exact finite kernel. Every theorem takes `NativePair.Eligible fmt`; start with
`addNormalSameExponent_refines`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

open FloatLib.Numerics.FixedWord

variable {fmt : FloatFormat}

private theorem uint64_add_one_toNat (value : UInt64)
    (hfit : value.toNat + 1 < 2 ^ 64) :
    (value + 1).toNat = value.toNat + 1 := by
  rw [UInt64.toNat_add]
  change (value.toNat + 1) % 2 ^ 64 = value.toNat + 1
  exact Nat.mod_eq_of_lt hfit

private theorem packRoundedSum_eq_round (h : Eligible fmt)
    (sign : Bool) (exponent : UInt64) (left right : UInt128)
    (hexponent : 0 < exponent.toNat ∧ exponent.toNat + 1 < fmt.expAllOnesNat)
    (hleft : 2 ^ fmt.fracWidth ≤ left.toNat ∧ left.toNat < 2 ^ (fmt.fracWidth + 1))
    (hright : 2 ^ fmt.fracWidth ≤ right.toNat ∧ right.toNat < 2 ^ (fmt.fracWidth + 1)) :
    let exact := add128 left right
    let rounded := exact.value.roundShiftRightOneEven
    packNormal fmt sign (exponent + 1) rounded =
      FiniteProductRound.round fmt sign
        (left.toNat + right.toNat) (exponent.toNat + (fmt.bias + fmt.fracWidth - 2)) := by
  dsimp only
  have hfrac := h.frac_gt
  have hfracLe := h.frac_le
  have hallOnes := fmt.expAllOnesNat_eq_two_mul_bias_add_one
  have hbias := h.bias_lt
  have hsumUpper : left.toNat + right.toNat < 2 ^ (fmt.fracWidth + 2) := by
    rw [pow_succ, pow_succ]
    omega
  have hsumFit : left.toNat + right.toNat < 2 ^ 128 :=
    lt_of_lt_of_le hsumUpper (Nat.pow_le_pow_right (by decide) (by omega))
  have hexact : (add128 left right).value.toNat = left.toNat + right.toNat :=
    add128_value_toNat_of_lt left right hsumFit
  have hroundFit : (add128 left right).value.toNat / 2 + 1 < 2 ^ 128 := by
    rw [hexact]
    omega
  have hrounded :
      (add128 left right).value.roundShiftRightOneEven.toNat =
        Numerics.roundShiftRightEven (left.toNat + right.toNat) 1 := by
    rw [UInt128.roundShiftRightOneEven_toNat _ hroundFit, hexact]
  have hroundedBounds :=
    roundShiftRightEven_add_normalized_bounds fmt.fracWidth
      left.toNat right.toNat hleft hright
  have hroundedLower :
      2 ^ fmt.fracWidth ≤ (add128 left right).value.roundShiftRightOneEven.toNat := by
    rw [hrounded]
    exact hroundedBounds.1
  have hroundedUpper :
      (add128 left right).value.roundShiftRightOneEven.toNat < 2 ^ (fmt.fracWidth + 1) := by
    rw [hrounded]
    exact hroundedBounds.2
  have hexponentAdd : (exponent + 1).toNat = exponent.toNat + 1 :=
    uint64_add_one_toNat exponent (by norm_num at hbias ⊢; omega)
  have hexponentFit : (exponent + 1).toNat < 2 ^ fmt.expWidth := by
    rw [hexponentAdd, fmt.two_pow_expWidth_eq_two_mul_bias_add_two]
    omega
  rw [packNormal_eq_ofFields h sign (exponent + 1)
    (add128 left right).value.roundShiftRightOneEven
    hexponentFit hroundedLower hroundedUpper]
  rw [hexponentAdd, hrounded]
  symm
  exact FiniteProductRound.round_normalized_sum fmt sign exponent.toNat
    left.toNat right.toNat (by omega) hleft hright

/-- The all-ones exponent minus one is a proper native predecessor. -/
theorem expAllOnes_pred_toNat (h : Eligible fmt) :
    (expAllOnes fmt - 1).toNat = fmt.expAllOnesNat - 1 := by
  rw [UInt64.toNat_sub_of_le, expAllOnes_toNat h]
  · simp
  · apply UInt64.le_iff_toNat_le.mpr
    rw [expAllOnes_toNat h]
    have := FloatFormat.one_lt_expAllOnesNat fmt
    simp
    omega

/--
Every accepted native equal-exponent addition is exactly the existing finite path.

Rejected values retain `FiniteKernel.addOption`; this theorem is the trust boundary for the native
specialization.
-/
theorem addNormalSameExponent_refines (h : Eligible fmt) (x y result : Model fmt)
    (hfast : addNormalSameExponentOption x y = some result) :
    FiniteKernel.addOption x y = some result := by
  unfold addNormalSameExponentOption at hfast
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
  set exact := add128 xMantissa yMantissa with hexact
  set rounded := exact.value.roundShiftRightOneEven with hrounded
  have hsign : xSign = ySign := by
    by_contra hne
    simp [hne] at hfast
  have hxExponentZero : xExponent ≠ 0 := by
    intro hzero
    simp [hsign, hzero] at hfast
  have hxExponentUpper : ¬expAllOnes fmt - 1 ≤ xExponent := by
    intro hupper
    simp [hsign, hupper] at hfast
  have hyExponentEq : yExponent = xExponent := by
    by_contra hne
    simp [hsign, hxExponentZero, hxExponentUpper, hne] at hfast
  have hresult :
      packNormal fmt xSign (xExponent + 1) rounded = result := by
    simpa [hsign, hxExponentZero, hxExponentUpper, hyExponentEq,
      xFractionHigh, yFractionHigh, xMantissa, yMantissa, exact,
      rounded] using hfast
  have hxFractionHighFit : xFractionHigh.toNat < 2 ^ (fmt.fracWidth - 64) :=
    fracHigh_lt h xWords.hi
  have hyFractionHighFit : yFractionHigh.toNat < 2 ^ (fmt.fracWidth - 64) :=
    fracHigh_lt h yWords.hi
  have hxBounds :
      2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ (fmt.fracWidth + 1) :=
    normalMantissa_bounds h xFractionHigh xWords.lo hxFractionHighFit
  have hyBounds :
      2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ (fmt.fracWidth + 1) :=
    normalMantissa_bounds h yFractionHigh yWords.lo hyFractionHighFit
  have hxExponentUpperNat : ¬fmt.expAllOnesNat - 1 ≤ xExponent.toNat := by
    intro hupper
    apply hxExponentUpper
    apply UInt64.le_iff_toNat_le.mpr
    rwa [expAllOnes_pred_toNat h]
  have hxExponentFinite : xExponent ≠ expAllOnes fmt := by
    intro hexceptional
    apply hxExponentUpperNat
    rw [hexceptional, expAllOnes_toNat h]
    omega
  have hxNormalBounds :=
    normalExponent_bounds h x hxExponentZero hxExponentFinite
  have hxExponentBounds :
      0 < xExponent.toNat ∧ xExponent.toNat + 1 < fmt.expAllOnesNat :=
    ⟨hxNormalBounds.1, by omega⟩
  have hyExponentZero : yExponent ≠ 0 := by
    rw [hyExponentEq]
    exact hxExponentZero
  have hyExponentFinite : yExponent ≠ expAllOnes fmt := by
    rw [hyExponentEq]
    exact hxExponentFinite
  have hpack :=
    packRoundedSum_eq_round h xSign xExponent xMantissa yMantissa
      hxExponentBounds hxBounds hyBounds
  have hxMantissaNe : xMantissa.toNat ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hxBounds.1)
  have hyMantissaNe : yMantissa.toNat ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (Nat.two_pow_pos _) hyBounds.1)
  have hroundScale :
      FiniteKernel.scale xExponent.toNat + FiniteKernel.finiteScaleOffset fmt =
        xExponent.toNat + (fmt.bias + fmt.fracWidth - 2) := by
    have hscale : FiniteKernel.scale xExponent.toNat = xExponent.toNat - 1 := by
      simp [FiniteKernel.scale, Nat.ne_of_gt hxExponentBounds.1]
    have hfrac := h.frac_gt
    rw [hscale]
    unfold FiniteKernel.finiteScaleOffset
    rw [h.exponentBias_eq]
    omega
  have hcomponents :
      FiniteKernel.addComponents fmt
          { sign := xSign
            exponent := xExponent.toNat
            mantissa := xMantissa.toNat }
          { sign := xSign
            exponent := xExponent.toNat
            mantissa := yMantissa.toNat } =
        result := by
    rw [FiniteKernel.addComponents_sameSign_sameExponent fmt h.isIEEE xSign
      xMantissa.toNat yMantissa.toNat xExponent.toNat hxMantissaNe hyMantissaNe]
    rw [hroundScale]
    calc
      FiniteProductRound.round fmt xSign (xMantissa.toNat + yMantissa.toNat)
            (xExponent.toNat + (fmt.bias + fmt.fracWidth - 2)) =
          packNormal fmt xSign (xExponent + 1) rounded := by
        simpa [exact, rounded] using hpack.symm
      _ = result := hresult
  unfold FiniteKernel.addOption
  rw [decode_of_normalExponent h x hxExponentZero hxExponentFinite,
    decode_of_normalExponent h y hyExponentZero hyExponentFinite]
  simp only [Option.some.injEq]
  simpa [xWords, yWords, xExponent, yExponent, xSign, ySign,
    xFractionHigh, yFractionHigh, xMantissa, yMantissa, hxWords,
    hyWords, hsign, hyExponentEq] using hcomponents

/-- The two-word finite addition chain equals the width-generic exact finite kernel. -/
theorem addFinite_eq (h : Eligible fmt) (x y : Model fmt) :
    addFiniteOption x y = FiniteKernel.addOption x y := by
  unfold addFiniteOption
  cases hfast : addNormalSameExponentOption x y with
  | none => exact FiniteKernel.addRuntime_eq x y
  | some result =>
      rw [addNormalSameExponent_refines h x y result hfast]

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
