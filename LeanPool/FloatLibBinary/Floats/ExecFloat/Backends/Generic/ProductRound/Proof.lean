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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.ProductRound.Runtime
public import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.RoundDyadicImpl.Proof

/-!
# Correctness of unsigned-scale product rounding

`round_eq_roundDyadic` identifies unsigned-scale rounding with `roundDyadic` for descriptors
satisfying `fmt.isIEEE = true`. The equality covers signed zero, subnormal results, carry
normalization, and overflow.

`normalSpec_refines` supplies the common natural-number normal-product contract used by word
backends. `round_normalized_sum` gives the one-bit nearest-even reduction used by equal-exponent
addition.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteProductRound

/--
Proof-facing specification of the successful normal-product path.

The optimized word backends use different integer representations, but successful normal results
all have this format-independent meaning. Keeping the specification here prevents one specialized
backend from becoming a proof dependency of another.
-/
def normalSpecOption (fmt : FloatFormat) (sign : Bool)
    (xExponent yExponent xMantissa yMantissa : Nat) :
    Option (Model fmt) :=
  let product := xMantissa * yMantissa
  let leading := product.log2
  let scale := (xExponent - 1) + (yExponent - 1)
  let position := leading + scale
  let normalThreshold := fmt.bias + 2 * fmt.fracWidth - 1
  if position < normalThreshold then
    none
  else
    let rounded :=
      Numerics.roundShiftRightEven product (leading - fmt.fracWidth)
    let carry := rounded = pow2 (fmt.fracWidth + 1)
    let normalizedPosition := if carry then position + 1 else position
    let overflowThreshold :=
      3 * fmt.bias + 2 * fmt.fracWidth - 2
    if overflowThreshold < normalizedPosition then
      none
    else
      let normalizedMantissa :=
        if carry then pow2 fmt.fracWidth else rounded
      let exponentOffset :=
        fmt.bias + 2 * fmt.fracWidth - 2
      some <| ofFields fmt sign
        (normalizedPosition - exponentOffset)
        (normalizedMantissa - pow2 fmt.fracWidth)

/--
A successful normal-product specification result is exactly the arbitrary-precision product
rounder.
-/
theorem normalSpec_refines
    (fmt : FloatFormat) (sign : Bool)
    (xExponent yExponent xMantissa yMantissa : Nat)
    (hproduct : xMantissa * yMantissa ≠ 0)
    (hleading : fmt.fracWidth ≤ (xMantissa * yMantissa).log2)
    (result : Model fmt)
    (hresult :
      normalSpecOption fmt sign xExponent yExponent xMantissa yMantissa =
        some result) :
    result =
      round fmt sign
        (xMantissa * yMantissa)
        ((xExponent - 1) + (yExponent - 1)) := by
  unfold normalSpecOption at hresult
  let product := xMantissa * yMantissa
  let leading := product.log2
  let scale := (xExponent - 1) + (yExponent - 1)
  let position := leading + scale
  let normalThreshold := fmt.bias + 2 * fmt.fracWidth - 1
  by_cases hsubnormal : position < normalThreshold
  · simp [product, leading, scale, position, normalThreshold, hsubnormal] at hresult
  let rounded := Numerics.roundShiftRightEven product (leading - fmt.fracWidth)
  let carry := rounded = pow2 (fmt.fracWidth + 1)
  let normalizedPosition := if carry then position + 1 else position
  let overflowThreshold := 3 * fmt.bias + 2 * fmt.fracWidth - 2
  by_cases hoverflow : overflowThreshold < normalizedPosition
  · simp [product, leading, scale, position, normalThreshold, hsubnormal,
      rounded, carry, normalizedPosition, overflowThreshold, hoverflow] at hresult
  have hresultEq :
      ofFields fmt sign
          (normalizedPosition -
            (fmt.bias + 2 * fmt.fracWidth - 2))
          ((if carry then pow2 fmt.fracWidth else rounded) -
            pow2 fmt.fracWidth) =
        result := by
    simpa [product, leading, scale, position, normalThreshold, hsubnormal,
      rounded, carry, normalizedPosition, overflowThreshold, hoverflow] using
      hresult
  rw [← hresultEq]
  unfold round
  simp only [beq_iff_eq, hproduct, ite_false]
  rw [ite_eq_right hsubnormal, ite_eq_left hleading, ite_eq_right hoverflow]

/--
Significands at least `2 ^ fmt.fracWidth` satisfy the side conditions of `normalSpec_refines`.
-/
theorem normalSpec_refines_of_normalized
    (fmt : FloatFormat) (sign : Bool)
    (xExponent yExponent xMantissa yMantissa : Nat)
    (hxMantissa : 2 ^ fmt.fracWidth ≤ xMantissa)
    (hyMantissa : 2 ^ fmt.fracWidth ≤ yMantissa)
    (result : Model fmt)
    (hresult :
      normalSpecOption fmt sign xExponent yExponent xMantissa yMantissa =
        some result) :
    result =
      round fmt sign
        (xMantissa * yMantissa)
        ((xExponent - 1) + (yExponent - 1)) := by
  have hxPositive : 0 < xMantissa :=
    (Nat.two_pow_pos _).trans_le hxMantissa
  have hyPositive : 0 < yMantissa :=
    (Nat.two_pow_pos _).trans_le hyMantissa
  have hproduct : xMantissa * yMantissa ≠ 0 := by
    positivity
  have hproductLower :
      2 ^ (2 * fmt.fracWidth) ≤ xMantissa * yMantissa := by
    have hmul := Nat.mul_le_mul hxMantissa hyMantissa
    simpa [← pow_add, two_mul] using hmul
  have hleading :
      fmt.fracWidth ≤ (xMantissa * yMantissa).log2 := by
    have htwice :
        2 * fmt.fracWidth ≤ (xMantissa * yMantissa).log2 :=
      (Nat.le_log2 hproduct).2 hproductLower
    omega
  exact normalSpec_refines fmt sign xExponent yExponent
    xMantissa yMantissa hproduct hleading result hresult

/--
Adding two normalized significands at one encoded exponent discards exactly one low bit.

This is the format-independent part of equal-exponent native addition. Word backends still prove
that their machine addition and packing operations represent the `Nat` expression below, but the
rounding argument is shared by every binary descriptor.
-/
theorem round_normalized_sum
    (fmt : FloatFormat) (sign : Bool) (exponent left right : Nat)
    (hexponent : exponent < 2 * fmt.bias)
    (hleft :
      2 ^ fmt.fracWidth ≤ left ∧
        left < 2 ^ (fmt.fracWidth + 1))
    (hright :
      2 ^ fmt.fracWidth ≤ right ∧
        right < 2 ^ (fmt.fracWidth + 1)) :
    round fmt sign (left + right)
        (exponent + (fmt.bias + fmt.fracWidth - 2)) =
      ofFields fmt sign (exponent + 1)
        (Numerics.roundShiftRightEven (left + right) 1 -
          pow2 fmt.fracWidth) := by
  have hsumLower :
      2 ^ (fmt.fracWidth + 1) ≤ left + right := by
    have hdouble :
        2 ^ (fmt.fracWidth + 1) =
          2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth := by
      rw [pow_succ]
      omega
    rw [hdouble]
    exact Nat.add_le_add hleft.1 hright.1
  have hsumUpper :
      left + right < 2 ^ (fmt.fracWidth + 2) := by
    have hdouble :
        2 ^ (fmt.fracWidth + 2) =
          2 ^ (fmt.fracWidth + 1) +
            2 ^ (fmt.fracWidth + 1) := by
      rw [show fmt.fracWidth + 2 =
        (fmt.fracWidth + 1) + 1 by omega, pow_succ]
      omega
    rw [hdouble]
    exact Nat.add_lt_add hleft.2 hright.2
  have hsumPositive : 0 < left + right := by
    have hpowPositive : 0 < 2 ^ (fmt.fracWidth + 1) := by
      positivity
    omega
  have hsumNe : left + right ≠ 0 := hsumPositive.ne'
  have hleading :
      (left + right).log2 = fmt.fracWidth + 1 := by
    apply (Nat.log2_eq_iff hsumNe).2
    constructor
    · exact hsumLower
    · simpa [Nat.add_assoc] using hsumUpper
  have hroundedBounds :=
    roundShiftRightEven_add_normalized_bounds fmt.fracWidth
      left right hleft hright
  have hcarry :
      Numerics.roundShiftRightEven (left + right) 1 ≠
        pow2 (fmt.fracWidth + 1) := by
    rw [pow2_eq_two_pow]
    exact Nat.ne_of_lt hroundedBounds.2
  have hbias := fmt.bias_pos
  have hfraction := fmt.fracWidth_pos
  have hnormal :
      ¬(left + right).log2 +
          (exponent + (fmt.bias + fmt.fracWidth - 2)) <
        fmt.bias + 2 * fmt.fracWidth - 1 := by
    rw [hleading]
    omega
  have hoverflow :
      ¬3 * fmt.bias + 2 * fmt.fracWidth - 2 <
        fmt.fracWidth + 1 +
          (exponent + (fmt.bias + fmt.fracWidth - 2)) := by
    omega
  have hencodedExponent :
      fmt.fracWidth + 1 +
            (exponent + (fmt.bias + fmt.fracWidth - 2)) -
          (fmt.bias + 2 * fmt.fracWidth - 2) =
        exponent + 1 := by
    omega
  unfold round
  simp only [beq_iff_eq, hsumNe, ite_false]
  rw [ite_eq_right hnormal, hleading]
  rw [ite_eq_left (show fmt.fracWidth ≤ fmt.fracWidth + 1 by omega)]
  rw [show fmt.fracWidth + 1 - fmt.fracWidth = 1 by omega]
  rw [ite_eq_right hcarry, ite_eq_right hoverflow, hencodedExponent]
  rw [ite_eq_right hcarry]

private theorem exponent_add_align (fmt : FloatFormat) (scale : Nat) :
    (Int.ofNat scale -
          Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt)) +
        Int.ofNat (FloatFormat.ieeeSubnormalAlignExp fmt) =
      Int.ofNat scale -
        Int.ofNat (FloatFormat.ieeeSubnormalAlignExp fmt) := by
  simp only [Int.ofNat_eq_natCast, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem double_align_eq_bias_add_offset (fmt : FloatFormat) :
    2 * FloatFormat.ieeeSubnormalAlignExp fmt =
      fmt.bias + (fmt.bias + 2 * fmt.fracWidth - 2) := by
  unfold FloatFormat.ieeeSubnormalAlignExp
  have hbias := fmt.bias_pos
  have hfraction := fmt.fracWidth_pos
  omega

private theorem normalized_exponent_eq
    (fmt : FloatFormat) (position : Nat) :
    Int.ofNat position -
          Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt) +
        Int.ofNat fmt.bias =
      Int.ofNat position -
        Int.ofNat (fmt.bias + 2 * fmt.fracWidth - 2) := by
  have hnat := double_align_eq_bias_add_offset fmt
  have hint :
      Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt) =
        Int.ofNat fmt.bias +
          Int.ofNat (fmt.bias + 2 * fmt.fracWidth - 2) := by
    simp only [Int.ofNat_eq_natCast]
    exact_mod_cast hnat
  omega

private theorem normalized_exponent_gt_max_iff
    (fmt : FloatFormat) (position : Nat) :
    Int.ofNat position -
          Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt) >
        Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) ↔
      3 * fmt.bias + 2 * fmt.fracWidth - 2 < position := by
  have hdouble := double_align_eq_bias_add_offset fmt
  have hoverflow :
      2 * FloatFormat.ieeeSubnormalAlignExp fmt + fmt.bias =
        3 * fmt.bias + 2 * fmt.fracWidth - 2 := by
    rw [hdouble]
    have hbias := fmt.bias_pos
    have hfraction := fmt.fracWidth_pos
    omega
  have hoverflowInt :
      (2 * FloatFormat.ieeeSubnormalAlignExp fmt : Int) +
          (fmt.bias : Int) =
        (3 * fmt.bias + 2 * fmt.fracWidth - 2 : Nat) := by
    exact_mod_cast hoverflow
  unfold FloatFormat.ieeeMaxNormalExponent
  simp only [Int.ofNat_eq_natCast]
  omega

/--
Unsigned-scale product rounding agrees with the public exact-dyadic rounder for a conventional
IEEE descriptor.
-/
theorem round_eq_roundDyadic
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Bool) (product scale : Nat) :
    round fmt sign product scale =
      roundDyadic fmt {
        negative := sign
        significand := product
        exponent :=
          Int.ofNat scale -
            Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt) } := by
  rw [roundDyadic_eq_roundDyadicImpl]
  unfold roundDyadicImpl
  rw [ite_eq_left hfmt]
  unfold round ieeeRoundDyadicImpl
  dsimp only
  by_cases hproduct : product = 0
  · simp [hproduct]
  simp only [beq_iff_eq, hproduct, ite_false]
  have hbias := fmt.bias_pos
  have halign : fmt.ieeeSubnormalAlignExp = fmt.bias + fmt.fracWidth - 1 := rfl
  let leading := product.log2
  let position := leading + scale
  let normalThreshold := fmt.bias + 2 * fmt.fracWidth - 1
  by_cases hsubnormal : position < normalThreshold
  · have hgenericSubnormal :
        (leading : Int) +
              (Int.ofNat scale -
                Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt)) <
            FloatFormat.ieeeMinNormalExponent fmt := by
      dsimp only [leading, position, normalThreshold] at hsubnormal ⊢
      unfold FloatFormat.ieeeMinNormalExponent FloatFormat.ieeeSubnormalAlignExp
      simp only [Int.ofNat_eq_natCast, Nat.cast_mul, Nat.cast_ofNat]
      omega
    rw [ite_eq_left hsubnormal, ite_eq_left hgenericSubnormal]
    rw [exponent_add_align]
    let align := FloatFormat.ieeeSubnormalAlignExp fmt
    by_cases hscale : scale < align
    · have hgap : 0 < align - scale := by omega
      have hscaleLe : scale ≤ align := Nat.le_of_lt hscale
      have hgapSucc : align - scale - 1 + 1 = align - scale := by
        omega
      have hcastSucc :
          ((align - scale - 1 : Nat) : Int) + 1 =
            ((align - scale : Nat) : Int) := by
        exact_mod_cast hgapSucc
      have hcastGap :
          ((align - scale - 1 : Nat) : Int) + 1 =
            (align : Int) - (scale : Int) := by
        rw [hcastSucc]
        exact Int.ofNat_sub hscaleLe
      have hexponent :
          Int.ofNat scale - Int.ofNat align =
            Int.negSucc (align - scale - 1) := by
        rw [Int.negSucc_eq]
        simp only [Int.ofNat_eq_natCast, hcastGap]
        omega
      rw [hexponent]
      simp only
      rw [hgapSucc]
      rw [ite_eq_left hscale]
    · have hscaleLe : align ≤ scale := Nat.le_of_not_gt hscale
      have hexponent :
          Int.ofNat scale - Int.ofNat align =
            Int.ofNat (scale - align) := by
        simpa only [Int.ofNat_eq_natCast] using
          (Int.ofNat_sub hscaleLe).symm
      rw [hexponent]
      simp only
      rw [ite_eq_right hscale]
  · have hnormal : normalThreshold ≤ position :=
      Nat.le_of_not_gt hsubnormal
    have hgenericNormal :
        ¬(leading : Int) +
              (Int.ofNat scale -
                Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt)) <
            FloatFormat.ieeeMinNormalExponent fmt := by
      dsimp only [leading, position, normalThreshold] at hnormal ⊢
      unfold FloatFormat.ieeeMinNormalExponent FloatFormat.ieeeSubnormalAlignExp
      simp only [Int.ofNat_eq_natCast, Nat.cast_mul, Nat.cast_ofNat]
      omega
    rw [ite_eq_right hsubnormal, ite_eq_right hgenericNormal]
    let roundedMantissa :=
      if fmt.fracWidth ≤ leading then
        Numerics.roundShiftRightEven product (leading - fmt.fracWidth)
      else
        product <<< (fmt.fracWidth - leading)
    let overflowThreshold := 3 * fmt.bias + 2 * fmt.fracWidth - 2
    have htotal :
        (leading : Int) +
              (Int.ofNat scale -
                Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt)) =
            Int.ofNat position -
              Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt) := by
      simp only [position, Int.ofNat_eq_natCast, Nat.cast_add]
      omega
    rw [htotal]
    by_cases hcarry :
        roundedMantissa = pow2 (fmt.fracWidth + 1)
    · simp only [roundedMantissa, leading] at hcarry
      simp only [hcarry, ite_true]
      have hnormalized :
          (Int.ofNat position -
                Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt)) +
              1 =
            Int.ofNat (position + 1) -
              Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt) := by
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
        ring
      rw [hnormalized]
      by_cases hoverflow : overflowThreshold < position + 1
      · have hgenericOverflow :
            Int.ofNat (position + 1) -
                  Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt) >
                Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
          exact
            (normalized_exponent_gt_max_iff fmt (position + 1)).2 hoverflow
        rw [ite_eq_left hoverflow, ite_eq_left hgenericOverflow]
      · have hnoOverflow : position + 1 ≤ overflowThreshold :=
          Nat.le_of_not_gt hoverflow
        have hgenericNoOverflow :
            ¬Int.ofNat (position + 1) -
                  Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt) >
                Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
          exact fun h =>
            hoverflow <|
              (normalized_exponent_gt_max_iff fmt (position + 1)).1 h
        rw [ite_eq_right hoverflow, ite_eq_right hgenericNoOverflow]
        congr 2
        change position + 1 - (fmt.bias + 2 * fmt.fracWidth - 2) =
          (Int.ofNat (position + 1) -
              Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt) +
              Int.ofNat fmt.bias).toNat
        rw [normalized_exponent_eq]
        simpa only [Int.ofNat_eq_natCast] using
          (Int.toNat_sub (position + 1)
            (fmt.bias + 2 * fmt.fracWidth - 2)).symm
    · simp only [roundedMantissa, leading] at hcarry
      simp only [hcarry, ite_false]
      by_cases hoverflow : overflowThreshold < position
      · have hgenericOverflow :
            Int.ofNat position -
                  Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt) >
                Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
          exact (normalized_exponent_gt_max_iff fmt position).2 hoverflow
        rw [ite_eq_left hoverflow, ite_eq_left hgenericOverflow]
      · have hnoOverflow : position ≤ overflowThreshold :=
          Nat.le_of_not_gt hoverflow
        have hgenericNoOverflow :
            ¬Int.ofNat position -
                  Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt) >
                Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
          exact fun h =>
            hoverflow <| (normalized_exponent_gt_max_iff fmt position).1 h
        rw [ite_eq_right hoverflow, ite_eq_right hgenericNoOverflow]
        congr 2
        change position - (fmt.bias + 2 * fmt.fracWidth - 2) =
          (Int.ofNat position -
              Int.ofNat (2 * FloatFormat.ieeeSubnormalAlignExp fmt) +
              Int.ofNat fmt.bias).toNat
        rw [normalized_exponent_eq]
        simpa only [Int.ofNat_eq_natCast] using
          (Int.toNat_sub position
            (fmt.bias + 2 * fmt.fracWidth - 2)).symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteProductRound
