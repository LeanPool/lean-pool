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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Addition.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Full.Subtraction.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.AddDyadic.Proof

/-!
# Verified equal-exponent binary64 addition

The binary64 addition kernel handles same-sign normal operands with equal exponents entirely in
`UInt64`. Their exact 54-bit significand sum is rounded once to nearest-even and packed
directly. Unequal exponents, opposite signs, subnormals, and overflow boundaries are left to the
generic finite kernel. Exceptional values are handled by the outer operation dispatcher.

The subtraction dispatcher composes this adder with the signed Sterbenz backend: same-sign nearby
operands use exact native subtraction, opposite-sign operands reuse native addition, and every
declined case retains the generic kernel.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Numerics.FixedWord

private theorem packRoundedSum_eq_round
    (sign : Bool) (exponent left right : UInt64)
    (hexponent : 0 < exponent.toNat ∧ exponent.toNat < 2046)
    (hleft :
      2 ^ 52 ≤ left.toNat ∧ left.toNat < 2 ^ 53)
    (hright :
      2 ^ 52 ≤ right.toNat ∧ right.toNat < 2 ^ 53) :
    let rounded := FloatLib.Numerics.FixedWord.roundShiftRightEven (left + right) 1
    ofUInt64
        (packFieldsWord sign (exponent + 1)
          (rounded - 0x0010000000000000)) =
      FiniteProductRound.round FloatFormat.binary64 sign
        (left.toNat + right.toNat) (exponent.toNat + 1073) := by
  dsimp only
  have hsumLower : 2 ^ 53 ≤ left.toNat + right.toNat := by
    norm_num at hleft hright ⊢
    omega
  have hsumUpper : left.toNat + right.toNat < 2 ^ 54 := by
    norm_num at hleft hright ⊢
    omega
  have hsumFit : left.toNat + right.toNat < 2 ^ 64 :=
    lt_trans hsumUpper (by norm_num)
  have hsum :
      (left + right).toNat = left.toNat + right.toNat :=
    uint64_add_toNat_of_lt left right hsumFit
  have hrounded :
      (FloatLib.Numerics.FixedWord.roundShiftRightEven (left + right) 1).toNat =
        Numerics.roundShiftRightEven (left.toNat + right.toNat) 1 := by
    rw [FloatLib.Numerics.FixedWord.roundShiftRightEven_toNat, hsum]
  have hroundedBounds :=
    roundShiftRightEven_add_normalized_bounds 52
      left.toNat right.toNat hleft hright
  have hroundedLower :
      2 ^ 52 ≤
        (FloatLib.Numerics.FixedWord.roundShiftRightEven (left + right) 1).toNat := by
    rw [hrounded]
    exact hroundedBounds.1
  have hroundedUpper :
      (FloatLib.Numerics.FixedWord.roundShiftRightEven (left + right) 1).toNat < 2 ^ 53 := by
    rw [hrounded]
    exact hroundedBounds.2
  have hbaseLe :
      (0x0010000000000000 : UInt64) ≤
        FloatLib.Numerics.FixedWord.roundShiftRightEven (left + right) 1 := by
    apply UInt64.le_iff_toNat_le.mpr
    exact hroundedLower
  have hexponentFit : exponent.toNat + 1 < 2 ^ 64 := by
    omega
  have hexponentWord :
      exponent + 1 = UInt64.ofNat (exponent.toNat + 1) := by
    apply UInt64.toNat_inj.mp
    rw [uint64_add_toNat_of_lt exponent 1 (by simpa using hexponentFit)]
    simp only [UInt64.reduceToNat, UInt64.toNat_ofNat']
    exact (Nat.mod_eq_of_lt hexponentFit).symm
  have hfractionWord :
      FloatLib.Numerics.FixedWord.roundShiftRightEven (left + right) 1 -
          0x0010000000000000 =
        UInt64.ofNat
          (Numerics.roundShiftRightEven (left.toNat + right.toNat) 1 - 2 ^ 52) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ hbaseLe, hrounded]
    norm_num
    exact (Nat.mod_eq_of_lt (by omega)).symm
  rw [hexponentWord, hfractionWord, packFieldsWord_eq_ofNat]
  symm
  have hround :=
    FiniteProductRound.round_normalized_sum
      FloatFormat.binary64 sign exponent.toNat left.toNat right.toNat
      hexponent.2 hleft hright
  rw [show FloatFormat.binary64.bias +
      FloatFormat.binary64.fracWidth - 2 = 1073 by decide] at hround
  rw [show FloatFormat.binary64.fracWidth = 52 by decide] at hround
  simpa [pow2_eq_two_pow] using hround

/--
Every accepted native equal-exponent addition is exactly the existing finite binary64 path.

Rejected values retain `addFiniteImplOption`; this theorem is the trust boundary for the native
specialization.
-/
theorem addNormalSameExponent_refines (x y result : Value)
    (hfast : addNormalSameExponentOption x y = some result) :
    addFiniteImplOption x y = some result := by
  unfold addNormalSameExponentOption at hfast
  dsimp only at hfast
  set xBits := toUInt64 x with hxBits
  set yBits := toUInt64 y with hyBits
  set xExponent := expField xBits with hxExponent
  set yExponent := expField yBits with hyExponent
  set xSign := signBit xBits with hxSign
  set ySign := signBit yBits with hySign
  set xFraction := fracField xBits with hxFraction
  set yFraction := fracField yBits with hyFraction
  set xMantissa := finiteMantissa xExponent xFraction with hxMantissa
  set yMantissa := finiteMantissa yExponent yFraction with hyMantissa
  set rounded :=
    FloatLib.Numerics.FixedWord.roundShiftRightEven (xMantissa + yMantissa) 1 with hrounded
  have hsign : xSign = ySign := by
    by_contra hne
    simp [hne] at hfast
  have hxExponentZero : xExponent ≠ 0 := by
    intro hzero
    simp [hsign, hzero] at hfast
  have hxExponentExceptional : xExponent ≠ 0x7ff := by
    intro hexceptional
    simp [hsign, hexceptional] at hfast
  have hyExponentEq : yExponent = xExponent := by
    by_contra hne
    simp [hsign, hxExponentZero, hxExponentExceptional, hne] at hfast
  have hoverflow : ¬0x7ff ≤ xExponent + 1 := by
    intro hover
    simp [hsign, hxExponentZero, hxExponentExceptional, hyExponentEq,
      hover] at hfast
  have hresult :
      ofUInt64
          (packFieldsWord xSign (xExponent + 1)
            (rounded - 0x0010000000000000)) =
        result := by
    simpa [hsign, hxExponentZero, hxExponentExceptional, hyExponentEq,
      hoverflow, xMantissa, yMantissa, xFraction, yFraction, rounded] using
        hfast
  have hxFractionFit : xFraction.toNat < 2 ^ 52 := by
    simpa [xFraction, xBits, hxBits] using fracField_lt x
  have hyFractionFit : yFraction.toNat < 2 ^ 52 := by
    simpa [yFraction, yBits, hyBits] using fracField_lt y
  have hxBounds :
      2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53 := by
    simpa [xMantissa] using
      finiteMantissa_bounds xExponent xFraction
        hxExponentZero hxFractionFit
  have hyExponentZero : yExponent ≠ 0 := by
    rw [hyExponentEq]
    exact hxExponentZero
  have hyBounds :
      2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53 := by
    simpa [yMantissa] using
      finiteMantissa_bounds yExponent yFraction
        hyExponentZero hyFractionFit
  have hxExponentAdd :
      (xExponent + 1).toNat = xExponent.toNat + 1 := by
    apply uint64_add_toNat_of_lt
    have hxLt : xExponent.toNat < 2 ^ 11 := by
      simpa [xExponent, xBits, hxBits] using expField_lt x
    change xExponent.toNat + 1 < 2 ^ 64
    norm_num at hxLt
    omega
  have hnotOverflowNat : ¬2047 ≤ xExponent.toNat + 1 := by
    intro h
    apply hoverflow
    apply UInt64.le_iff_toNat_le.mpr
    rw [hxExponentAdd]
    simpa using h
  have hxFinite :
      expField (toUInt64 x) ≠ 0x7ff := by
    simpa [xBits, xExponent, hxBits] using hxExponentExceptional
  have hxNonzero :
      expField (toUInt64 x) ≠ 0 := by
    simpa [xBits, xExponent, hxBits] using hxExponentZero
  have hxNormalBounds :
      0 < xExponent.toNat ∧ xExponent.toNat < 2047 := by
    simpa [xBits, xExponent, hxBits] using
      normalExponent_bounds x hxNonzero hxFinite
  have hxExponentBounds :
      0 < xExponent.toNat ∧ xExponent.toNat < 2046 := by
    exact ⟨hxNormalBounds.1, by omega⟩
  have hyFinite :
      expField (toUInt64 y) ≠ 0x7ff := by
    simpa [yBits, yExponent, hyBits, hyExponentEq] using
      hxExponentExceptional
  have hpack :=
    packRoundedSum_eq_round xSign xExponent xMantissa yMantissa
      hxExponentBounds hxBounds hyBounds
  have hxMantissaNe : xMantissa.toNat ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hxBounds.1)
  have hyMantissaNe : yMantissa.toNat ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hyBounds.1)
  have hroundScale :
      FiniteKernel.scale xExponent.toNat +
          FiniteKernel.finiteScaleOffset FloatFormat.binary64 =
        xExponent.toNat + 1073 := by
    have hscale :
        FiniteKernel.scale xExponent.toNat = xExponent.toNat - 1 := by
      simp [FiniteKernel.scale, Nat.ne_of_gt hxExponentBounds.1]
    rw [hscale, show
      FiniteKernel.finiteScaleOffset FloatFormat.binary64 = 1074 by rfl]
    omega
  have hcomponents :
      FiniteKernel.addComponents FloatFormat.binary64
          { sign := xSign
            exponent := xExponent.toNat
            mantissa := xMantissa.toNat }
          { sign := xSign
            exponent := xExponent.toNat
            mantissa := yMantissa.toNat } =
        result := by
    rw [FiniteKernel.addComponents_sameSign_sameExponent
      FloatFormat.binary64 (by decide) xSign
      xMantissa.toNat yMantissa.toNat xExponent.toNat
      hxMantissaNe hyMantissaNe]
    rw [hroundScale]
    calc
      FiniteProductRound.round FloatFormat.binary64 xSign
            (xMantissa.toNat + yMantissa.toNat)
            (xExponent.toNat + 1073) =
          ofUInt64
            (packFieldsWord xSign (xExponent + 1)
              (rounded - 0x0010000000000000)) := by
        simpa [rounded] using hpack.symm
      _ = result := hresult
  unfold addFiniteImplOption
  rw [decode_of_finiteExponent x hxFinite,
    decode_of_finiteExponent y hyFinite]
  simp only [Option.some.injEq]
  simpa [xBits, yBits, xExponent, yExponent, xSign, ySign,
    xFraction, yFraction, xMantissa, yMantissa, hxBits, hyBits,
    hsign, hyExponentEq, FiniteKernel.addComponentsImpl_eq] using hcomponents

/-- The native addition dispatcher is bit-for-bit equal to the exact finite implementation. -/
theorem addFiniteFastImpl_eq (x y : Value) :
    addFiniteFastImplOption x y = addFiniteImplOption x y := by
  unfold addFiniteFastImplOption
  cases hfast : addNormalSameExponentOption x y with
  | none => rfl
  | some result =>
      rw [addNormalSameExponent_refines x y result hfast]

/-- The native subtraction dispatcher is bit-for-bit equal to exact finite subtraction. -/
theorem subFiniteFastImpl_eq (x y : Value) :
    subFiniteFastImplOption x y = addFiniteImplOption x (negate y) := by
  unfold subFiniteFastImplOption
  cases hfast : subSignedSterbenzOption x y with
  | some result =>
      exact (subSignedSterbenz_refines x y result hfast).symm
  | none =>
      exact addFiniteFastImpl_eq x (negate y)

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
