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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Rounding.Runtime
public import LeanPool.FloatLibBinary.Kernels.FixedWord.Core.Proof
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.ModelRounding.Proof
import Mathlib.Tactic.NormNum

/-!
# Correctness of native binary32 product rounding

The binary32 product path keeps the unrounded product and all rounding decisions in native words.
The refinement covers normal, subnormal, carry, overflow, and signed-zero branches and relates each
one to the generic exact-dyadic rounder.

`roundProduct_eq_roundDyadic` applies to every `UInt64` magnitude at a scale of at most 506,
covering multiplication, aligned addition, and fused multiply-add. Runtime clients import
`Rounding.Runtime` independently of these proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/--
An aligned remainder below half an ulp leaves a normal binary32 mantissa unchanged by rounding.
-/
theorem roundDyadic_shiftLeft_add_of_lt_half
    (sign : Bool) (small large gap : Nat) (exponent : Int)
    (hlargeLow : 2 ^ 23 ≤ large) (hlargeHigh : large < 2 ^ 24)
    (hgap : 0 < gap) (hsmall : small < 2 ^ (gap - 1))
    (hnormal : -126 ≤ Int.ofNat (23 + gap) + exponent)
    (hoverflow : Int.ofNat (23 + gap) + exponent ≤ 127) :
    roundDyadic {
        negative := sign
        significand := (large <<< gap) + small
        exponent } =
      mkBits sign (Int.toNat (Int.ofNat (23 + gap) + exponent + 127))
        (large - 2 ^ 23) := by
  have hlargePos : 0 < large := lt_of_lt_of_le (by norm_num) hlargeLow
  have hcombinedPos : 0 < (large <<< gap) + small := by
    simp only [Nat.shiftLeft_eq]
    positivity
  have hcombinedNe := Nat.ne_of_gt hcombinedPos
  have hsmallGap : small < 2 ^ gap :=
    hsmall.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le gap 1))
  have hlower : 2 ^ (23 + gap) ≤ (large <<< gap) + small := by
    calc
      2 ^ (23 + gap) = 2 ^ 23 * 2 ^ gap := by rw [pow_add]
      _ ≤ large * 2 ^ gap := Nat.mul_le_mul_right _ hlargeLow
      _ ≤ large * 2 ^ gap + small := Nat.le_add_right _ _
      _ = (large <<< gap) + small := by rw [Nat.shiftLeft_eq]
  have hupper : (large <<< gap) + small < 2 ^ ((23 + gap) + 1) := by
    calc
      (large <<< gap) + small = large * 2 ^ gap + small := by rw [Nat.shiftLeft_eq]
      _ < large * 2 ^ gap + 2 ^ gap := Nat.add_lt_add_left hsmallGap _
      _ = (large + 1) * 2 ^ gap := by ring
      _ ≤ 2 ^ 24 * 2 ^ gap := Nat.mul_le_mul_right _ hlargeHigh
      _ = 2 ^ (24 + gap) := by rw [pow_add]
      _ = 2 ^ ((23 + gap) + 1) := by congr 1; omega
  have hleading : ((large <<< gap) + small).log2 = 23 + gap :=
    (Nat.log2_eq_iff hcombinedNe).2 ⟨hlower, hupper⟩
  have hround :
      Numerics.roundShiftRightEven ((large <<< gap) + small) gap = large :=
    Model.roundShiftRightEven_shiftLeft_add_of_lt_half large small gap hgap
      (by simpa only [Model.pow2_eq_two_pow] using hsmall)
  have hcarry : large ≠ 2 ^ 24 := hlargeHigh.ne
  unfold roundDyadic
  simp only [beq_iff_eq, hcombinedNe, ite_false, hleading, not_lt_of_ge hnormal,
    Nat.le_add_right, ite_true, Nat.add_sub_cancel_left, hround, hcarry,
    not_lt_of_ge hoverflow, Model.pow2_eq_two_pow]

private theorem roundSubnormal_eq
    (sign : Bool) (nativeFraction : UInt64) (genericFraction : Nat)
    (hfraction : nativeFraction.toNat = genericFraction) :
    (if nativeFraction = 0 then
        if sign = true then (0x80000000 : UInt32) else 0
      else if nativeFraction = 0x800000 then
        mkBits sign 1 0
      else
        mkBits sign 0 nativeFraction.toNat) =
      if genericFraction = 0 then
        if sign = true then (0x80000000 : UInt32) else 0
      else if genericFraction = Model.pow2 23 then
        mkBits sign 1 0
      else
        mkBits sign 0 genericFraction := by
  have hfractionZero :
      nativeFraction = 0 ↔ genericFraction = 0 := by
    rw [← UInt64.toNat_inj]
    simp [hfraction]
  have hfractionNormal :
      nativeFraction = 0x800000 ↔
        genericFraction = Model.pow2 23 := by
    rw [← UInt64.toNat_inj]
    simp [hfraction, Model.pow2_eq_two_pow]
  by_cases hfzero : nativeFraction = 0
  · rw [ite_eq_left hfzero, ite_eq_left (hfractionZero.mp hfzero)]
  · rw [ite_eq_right hfzero, ite_eq_right (not_congr hfractionZero |>.mp hfzero)]
    by_cases hfnormal : nativeFraction = 0x800000
    · rw [ite_eq_left hfnormal, ite_eq_left (hfractionNormal.mp hfnormal)]
    · rw [ite_eq_right hfnormal,
        ite_eq_right (not_congr hfractionNormal |>.mp hfnormal), hfraction]

private theorem roundNormal_eq
    (sign : Bool)
    (nativeRounded nativePosition : UInt64)
    (genericRounded genericPosition : Nat)
    (genericTotal : Int)
    (hrounded : nativeRounded.toNat = genericRounded)
    (hposition : nativePosition.toNat = genericPosition)
    (hpositionSucc : (nativePosition + 1).toNat = genericPosition + 1)
    (htotal : genericTotal = Int.ofNat genericPosition - 298)
    (hpositionMin : 172 ≤ genericPosition) :
    (if
          (if nativeRounded = 0x1000000 then
              nativePosition + 1
            else
              nativePosition) >
            425 then
        if sign = true then (0xff800000 : UInt32) else 0x7f800000
      else
        mkBits sign
          ((if nativeRounded = 0x1000000 then
                nativePosition + 1
              else
                nativePosition) -
            171).toNat
          ((if nativeRounded = 0x1000000 then
                (0x800000 : UInt64)
              else
                nativeRounded).toNat -
            0x800000)) =
      if
          (if genericRounded = Model.pow2 24 then
              genericTotal + 1
            else
              genericTotal) >
            127 then
        if sign = true then (0xff800000 : UInt32) else 0x7f800000
      else
        mkBits sign
          (Int.toNat
            ((if genericRounded = Model.pow2 24 then
                  genericTotal + 1
                else
                  genericTotal) +
              127))
          ((if genericRounded = Model.pow2 24 then
                Model.pow2 23
              else
                genericRounded) -
            Model.pow2 23) := by
  have h171 : ((171 : UInt64).toNat) = 171 := by
    decide
  have h425 : ((425 : UInt64).toNat) = 425 := by
    decide
  have hminMantissa : ((0x800000 : UInt64).toNat) = 0x800000 := by
    decide
  have hcarry :
      nativeRounded = 0x1000000 ↔
        genericRounded = Model.pow2 24 := by
    rw [← UInt64.toNat_inj]
    simp [hrounded, Model.pow2_eq_two_pow]
  by_cases hnativeCarry : nativeRounded = 0x1000000
  · have hgenericCarry := hcarry.mp hnativeCarry
    simp only [ite_eq_left hnativeCarry, ite_eq_left hgenericCarry]
    have hoverflow :
        nativePosition + 1 > (425 : UInt64) ↔
          genericTotal + 1 > 127 := by
      change
        (425 : UInt64) < nativePosition + 1 ↔
          (127 : Int) < genericTotal + 1
      rw [UInt64.lt_iff_toNat_lt, hpositionSucc, htotal]
      simp only [h425]
      simp only [Int.ofNat_eq_natCast]
      omega
    by_cases hnativeOverflow : nativePosition + 1 > (425 : UInt64)
    · rw [ite_eq_left hnativeOverflow, ite_eq_left (hoverflow.mp hnativeOverflow)]
    · rw [ite_eq_right hnativeOverflow,
        ite_eq_right (not_congr hoverflow |>.mp hnativeOverflow)]
      have hpositionLe : (171 : UInt64) ≤ nativePosition + 1 := by
        apply UInt64.le_iff_toNat_le.mpr
        rw [hpositionSucc]
        simp only [h171]
        omega
      have hnonnegative : 0 ≤ genericTotal + 1 + 127 := by
        rw [htotal]
        simp only [Int.ofNat_eq_natCast]
        omega
      have hencoded :
          (nativePosition + 1 - (171 : UInt64)).toNat =
            Int.toNat (genericTotal + 1 + 127) := by
        rw [UInt64.toNat_sub_of_le
          (nativePosition + 1) (171 : UInt64) hpositionLe]
        rw [hpositionSucc]
        simp only [h171]
        rw [← Int.ofNat_inj, Int.toNat_of_nonneg hnonnegative, htotal]
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [hencoded]
      norm_num [hminMantissa, Model.pow2_eq_two_pow]
  · have hgenericCarry : genericRounded ≠ Model.pow2 24 :=
      not_congr hcarry |>.mp hnativeCarry
    simp only [ite_eq_right hnativeCarry, ite_eq_right hgenericCarry]
    have hoverflow :
        nativePosition > (425 : UInt64) ↔ genericTotal > 127 := by
      change
        (425 : UInt64) < nativePosition ↔
          (127 : Int) < genericTotal
      rw [UInt64.lt_iff_toNat_lt, hposition, htotal]
      simp only [h425]
      simp only [Int.ofNat_eq_natCast]
      omega
    by_cases hnativeOverflow : nativePosition > (425 : UInt64)
    · rw [ite_eq_left hnativeOverflow, ite_eq_left (hoverflow.mp hnativeOverflow)]
    · rw [ite_eq_right hnativeOverflow,
        ite_eq_right (not_congr hoverflow |>.mp hnativeOverflow)]
      have hpositionLe : (171 : UInt64) ≤ nativePosition := by
        apply UInt64.le_iff_toNat_le.mpr
        rw [hposition]
        simp only [h171]
        omega
      have hnonnegative : 0 ≤ genericTotal + 127 := by
        rw [htotal]
        simp only [Int.ofNat_eq_natCast]
        omega
      have hencoded :
          (nativePosition - (171 : UInt64)).toNat =
            Int.toNat (genericTotal + 127) := by
        rw [UInt64.toNat_sub_of_le
          nativePosition (171 : UInt64) hpositionLe]
        rw [hposition]
        simp only [h171]
        rw [← Int.ofNat_inj, Int.toNat_of_nonneg hnonnegative, htotal]
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [hencoded, hrounded]
      norm_num [Model.pow2_eq_two_pow]

private theorem subnormalProductFraction (product scale : UInt64) (hscale : scale.toNat ≤ 506)
  (hlog : product.log2.toNat = product.toNat.log2) (hleading : product.log2.toNat < 64)
  (hpositionBound : product.toNat.log2 + scale.toNat < 2 ^ 64)
  (hposition : (product.log2 + scale).toNat = product.toNat.log2 + scale.toNat)
  (hsubnormalNat : product.toNat.log2 + scale.toNat < 172) :
  let nativeFraction :=
    if scale < 149 then Numerics.FixedWord.roundShiftRightEven product (149 - scale).toNat
    else product <<< (scale - 149);
  let genericFraction :=
    match Int.ofNat scale.toNat - 298 + 149 with
    | Int.ofNat shift => product.toNat <<< shift
    | Int.negSucc shift => Numerics.roundShiftRightEven product.toNat (shift + 1);
  UInt64.toNat 149 = 149 → nativeFraction.toNat = genericFraction := by
  intro nativeFraction genericFraction h149
  dsimp only [nativeFraction, genericFraction]
  by_cases hscaleSmall : scale < 149
  · rw [ite_eq_left hscaleSmall]
    have hscaleNat : scale.toNat < 149 := by
      simpa using UInt64.lt_iff_toNat_lt.mp hscaleSmall
    have hscaleWord : scale ≤ (149 : UInt64) := by
      apply UInt64.le_iff_toNat_le.mpr
      simpa [h149] using Nat.le_of_lt hscaleNat
    have hshift :
        ((149 : UInt64) - scale).toNat = 149 - scale.toNat := by
      rw [UInt64.toNat_sub_of_le (149 : UInt64) scale hscaleWord]
      simp [h149]
    have hexponent :
        Int.ofNat scale.toNat - 298 + 149 =
          Int.negSucc (148 - scale.toNat) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hshift, FloatLib.Numerics.FixedWord.roundShiftRightEven_toNat, hexponent]
    congr 1
    omega
  · rw [ite_eq_right hscaleSmall]
    have hscaleNat : 149 ≤ scale.toNat := by
      have hnot : ¬scale.toNat < (149 : UInt64).toNat := by
        intro hlt
        exact hscaleSmall (UInt64.lt_iff_toNat_lt.mpr hlt)
      simpa [h149] using Nat.le_of_not_gt hnot
    have hscaleWord : (149 : UInt64) ≤ scale := by
      apply UInt64.le_iff_toNat_le.mpr
      simpa [h149] using hscaleNat
    have hshift :
        (scale - (149 : UInt64)).toNat = scale.toNat - 149 := by
      rw [UInt64.toNat_sub_of_le scale (149 : UInt64) hscaleWord]
      simp [h149]
    have hshiftLt : scale.toNat - 149 < 64 := by
      omega
    have hshifted :
        product.toNat <<< (scale.toNat - 149) <
          2 ^ (product.toNat.log2 + 1 + (scale.toNat - 149)) :=
      Nat.shiftLeft_lt Nat.lt_log2_self
    have hexponentLt :
        product.toNat.log2 + 1 + (scale.toNat - 149) < 64 := by
      omega
    have hfit :
        product.toNat <<< (scale.toNat - 149) < 2 ^ 64 :=
      lt_trans hshifted (Nat.pow_lt_pow_right (by decide) hexponentLt)
    have hexponent :
        Int.ofNat scale.toNat - 298 + 149 =
          Int.ofNat (scale.toNat - 149) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have hnativeShift :
        (product <<< (scale - 149)).toNat =
          product.toNat <<< (scale.toNat - 149) := by
      simpa only [← hshift, UInt64.ofNat_toNat] using
        FloatLib.Numerics.FixedWord.shiftLeft_toNat product
          (scale.toNat - 149) hshiftLt hfit
    rw [hnativeShift, hexponent]

/--
Native word rounding agrees with the generic dyadic rounder.

The scale bound covers binary32 multiplication and aligned addition. The magnitude needs no
separate hypothesis because every `UInt64` value is below `2^64`.
-/
theorem roundProduct_eq_roundDyadic
    (sign : Bool) (product scale : UInt64)
    (hscale : scale.toNat ≤ 506) :
    roundProduct sign product scale =
      roundDyadic {
        negative := sign
        significand := product.toNat
        exponent := Int.ofNat scale.toNat - 298 } := by
  unfold roundProduct roundDyadic
  simp only [beq_iff_eq]
  by_cases hzero : product = 0
  · have hzeroNat : product.toNat = 0 := by
      simpa [← UInt64.toNat_inj] using hzero
    simp [hzero]
  · have hzeroNat : product.toNat ≠ 0 := by
      simpa [← UInt64.toNat_inj] using hzero
    have hlog :
        product.log2.toNat = product.toNat.log2 := by
      exact FloatLib.Numerics.FixedWord.log2_toNat product
    have hleading : product.log2.toNat < 64 := by
      rw [hlog, Nat.log2_lt hzeroNat]
      exact product.toNat_lt
    have hleadingNat : product.toNat.log2 < 64 := by
      simpa [hlog] using hleading
    have hpositionBound :
        product.toNat.log2 + scale.toNat < 2 ^ 64 := by
      omega
    have hposition :
        (product.log2 + scale).toNat =
          product.toNat.log2 + scale.toNat := by
      rw [UInt64.toNat_add, hlog, Nat.mod_eq_of_lt hpositionBound]
    rw [ite_eq_right hzero]
    simp only [hzeroNat, ite_false]
    by_cases hsubnormal : product.log2 + scale < 172
    · rw [ite_eq_left hsubnormal]
      have hsubnormalNat :
          product.toNat.log2 + scale.toNat < 172 := by
        have h := UInt64.lt_iff_toNat_lt.mp hsubnormal
        rw [hposition] at h
        simpa using h
      have hsubnormalGeneric :
          Int.ofNat product.toNat.log2 +
              (Int.ofNat scale.toNat - 298) <
            -126 := by
        have hsumInt :
            (product.toNat.log2 : Int) + (scale.toNat : Int) < 172 := by
          exact_mod_cast hsubnormalNat
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [ite_eq_left hsubnormalGeneric]
      let nativeFraction : UInt64 :=
        if scale < 149 then
          FloatLib.Numerics.FixedWord.roundShiftRightEven product (149 - scale).toNat
        else
          product <<< (scale - 149)
      let genericFraction : Nat :=
        match Int.ofNat scale.toNat - 298 + 149 with
        | .ofNat shift => product.toNat <<< shift
        | .negSucc shift =>
            Numerics.roundShiftRightEven product.toNat (shift + 1)
      have h149 : ((149 : UInt64).toNat) = 149 := by
        decide
      have hfraction : nativeFraction.toNat = genericFraction := by
        exact subnormalProductFraction (product := product) (scale := scale)
          (hscale := hscale) (hlog := hlog) (hleading := hleading)
          (hpositionBound := hpositionBound) (hposition := hposition)
          (hsubnormalNat := hsubnormalNat) h149
      exact roundSubnormal_eq sign nativeFraction genericFraction hfraction
    · rw [ite_eq_right hsubnormal]
      have hsubnormalNat :
          172 ≤ product.toNat.log2 + scale.toNat := by
        have h :
            ¬(product.log2 + scale).toNat < 172 := by
          intro hlt
          apply hsubnormal
          apply UInt64.lt_iff_toNat_lt.mpr
          simpa using hlt
        rw [hposition] at h
        omega
      have hsubnormalGeneric :
          ¬Int.ofNat product.toNat.log2 +
              (Int.ofNat scale.toNat - 298) <
            -126 := by
        have hsumInt :
            172 ≤ (product.toNat.log2 : Int) + (scale.toNat : Int) := by
          exact_mod_cast hsubnormalNat
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [ite_eq_right hsubnormalGeneric]
      let nativeRounded : UInt64 :=
        if product.log2 < 23 then
          product <<< (23 - product.log2)
        else
          FloatLib.Numerics.FixedWord.roundShiftRightEven product (product.log2 - 23).toNat
      let genericRounded : Nat :=
        if 23 ≤ product.toNat.log2 then
          Numerics.roundShiftRightEven product.toNat
            (product.toNat.log2 - 23)
        else
          product.toNat <<< (23 - product.toNat.log2)
      have h23 : ((23 : UInt64).toNat) = 23 := by
        decide
      have hrounded : nativeRounded.toNat = genericRounded := by
        dsimp only [nativeRounded, genericRounded]
        by_cases hleadingSmall : product.log2 < 23
        · have hleadingSmallNat : product.toNat.log2 < 23 := by
            have h := UInt64.lt_iff_toNat_lt.mp hleadingSmall
            rw [hlog] at h
            simpa using h
          rw [ite_eq_left hleadingSmall, ite_eq_right (Nat.not_le_of_lt hleadingSmallNat)]
          have hleadingWord : product.log2 ≤ (23 : UInt64) := by
            apply UInt64.le_iff_toNat_le.mpr
            rw [hlog, h23]
            exact Nat.le_of_lt hleadingSmallNat
          have hshift :
              ((23 : UInt64) - product.log2).toNat =
                23 - product.toNat.log2 := by
            rw [UInt64.toNat_sub_of_le
              (23 : UInt64) product.log2 hleadingWord]
            rw [h23, hlog]
          have hshiftLt : 23 - product.toNat.log2 < 64 := by
            omega
          have hfit :
              product.toNat <<< (23 - product.toNat.log2) < 2 ^ 64 :=
            lt_trans
              (FloatLib.Numerics.FixedWord.shiftLeft_sub_log2_lt_two_pow
                23 product.toNat hleadingSmallNat.le)
              (by norm_num)
          simpa only [← hshift, UInt64.ofNat_toNat] using
            FloatLib.Numerics.FixedWord.shiftLeft_toNat product
              (23 - product.toNat.log2) hshiftLt hfit
        · have hleadingSmallNat :
              ¬product.toNat.log2 < 23 := by
            intro hlt
            apply hleadingSmall
            apply UInt64.lt_iff_toNat_lt.mpr
            rw [hlog]
            simpa using hlt
          have hleadingNat : 23 ≤ product.toNat.log2 :=
            Nat.le_of_not_gt hleadingSmallNat
          rw [ite_eq_right hleadingSmall, ite_eq_left hleadingNat]
          have hleadingWord : (23 : UInt64) ≤ product.log2 := by
            apply UInt64.le_iff_toNat_le.mpr
            rw [hlog, h23]
            exact hleadingNat
          have hshift :
              (product.log2 - (23 : UInt64)).toNat =
                product.toNat.log2 - 23 := by
            rw [UInt64.toNat_sub_of_le
              product.log2 (23 : UInt64) hleadingWord]
            rw [hlog, h23]
          rw [FloatLib.Numerics.FixedWord.roundShiftRightEven_toNat, hshift]
      have hpositionSuccBound :
          product.toNat.log2 + scale.toNat + 1 < 2 ^ 64 := by
        omega
      have hpositionSucc :
          (product.log2 + scale + 1).toNat =
            product.toNat.log2 + scale.toNat + 1 := by
        rw [UInt64.toNat_add, hposition]
        change
          (product.toNat.log2 + scale.toNat + 1) % 2 ^ 64 =
            product.toNat.log2 + scale.toNat + 1
        exact Nat.mod_eq_of_lt hpositionSuccBound
      let genericTotal : Int :=
        Int.ofNat product.toNat.log2 +
          (Int.ofNat scale.toNat - 298)
      have htotal :
          genericTotal =
            Int.ofNat (product.toNat.log2 + scale.toNat) - 298 := by
        dsimp only [genericTotal]
        simp only [Int.ofNat_eq_natCast, Nat.cast_add]
        omega
      exact roundNormal_eq sign nativeRounded (product.log2 + scale)
        genericRounded (product.toNat.log2 + scale.toNat) genericTotal
        hrounded hposition hpositionSucc htotal hsubnormalNat

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
