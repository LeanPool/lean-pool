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

public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Generic.AddDyadic.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Finite.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Fma.Runtime
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Packing
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.SignedMagnitude.Proof
import LeanPool.FloatLibBinary.Floats.Formats.BinaryInterchange.ModelRounding.Proof
public import LeanPool.FloatLibBinary.Floats.ExecFloat.Backends.Word.Narrow.Base.Proof

/-!
# Correctness of native-word fused multiply-add for generic binary32

The direct `UInt64` fused multiply-add kernel agrees with its exact-dyadic finite specification.
Runtime clients can import `Fma.Runtime` without the alignment, packing, and rounding proof
developments.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

private theorem roundFmaAlignedRight_eq
    (productSign zSign : Bool)
    (product zMantissa productScale zProductScale : UInt64)
    (hproduct : product ≠ 0) (hz : zMantissa ≠ 0)
    (hproductBound : product.toNat < 2 ^ 48)
    (hzBound : zMantissa.toNat < 2 ^ 24)
    (hproductScaleBound : productScale.toNat ≤ 506)
    (hscale : productScale ≤ zProductScale)
    (hshift : zProductScale - productScale ≤ 39) :
    roundProduct
        (FloatLib.Numerics.FixedWord.addSignedMagnitudes
          productSign zSign product
          (zMantissa <<< (zProductScale - productScale))).1
        (FloatLib.Numerics.FixedWord.addSignedMagnitudes
          productSign zSign product
          (zMantissa <<< (zProductScale - productScale))).2
        productScale =
      roundDyadic
        (Model.addDyadic
          { negative := productSign
            significand := product.toNat
            exponent := Int.ofNat productScale.toNat - 298 }
          { negative := zSign
            significand := zMantissa.toNat
            exponent := Int.ofNat zProductScale.toNat - 298 }) := by
  have hscaleNat : productScale.toNat ≤ zProductScale.toNat :=
    UInt64.le_iff_toNat_le.mp hscale
  have hshiftToNat :
      (zProductScale - productScale).toNat =
        zProductScale.toNat - productScale.toNat := by
    rw [UInt64.toNat_sub_of_le zProductScale productScale hscale]
  have hshiftNatLe : (zProductScale - productScale).toNat ≤ 39 := by
    have h := UInt64.le_iff_toNat_le.mp hshift
    simpa using h
  have hshiftNatLt : (zProductScale - productScale).toNat < 64 := by
    omega
  have hzNat : zMantissa.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hz
  have hzLogLt : zMantissa.toNat.log2 < 24 := by
    rw [Nat.log2_lt hzNat]
    exact hzBound
  have hzShiftedBound :
      zMantissa.toNat <<< (zProductScale - productScale).toNat < 2 ^ 63 := by
    calc
      zMantissa.toNat <<< (zProductScale - productScale).toNat <
          2 ^ (zMantissa.toNat.log2 + 1 +
            (zProductScale - productScale).toNat) :=
        Nat.shiftLeft_lt Nat.lt_log2_self
      _ ≤ 2 ^ 63 := by
        apply Nat.pow_le_pow_right
        · decide
        · omega
  have hzShiftedFit :
      zMantissa.toNat <<< (zProductScale - productScale).toNat < 2 ^ 64 :=
    lt_trans hzShiftedBound (by norm_num)
  have hzShiftedToNat :
      (zMantissa <<< (zProductScale - productScale)).toNat =
        zMantissa.toNat <<< (zProductScale - productScale).toNat := by
    rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hshiftNatLt,
      Nat.mod_eq_of_lt hzShiftedFit]
  have hzShiftedNatNonzero :
      zMantissa.toNat <<< (zProductScale - productScale).toNat ≠ 0 := by
    simp [Nat.shiftLeft_eq, hzNat]
  have hzShiftedNonzero :
      zMantissa <<< (zProductScale - productScale) ≠ 0 := by
    intro h
    have hnat := congrArg UInt64.toNat h
    rw [hzShiftedToNat] at hnat
    exact hzShiftedNatNonzero hnat
  have hsum :
      product.toNat +
          (zMantissa <<< (zProductScale - productScale)).toNat <
        2 ^ 64 := by
    rw [hzShiftedToNat]
    norm_num at hproductBound hzShiftedBound ⊢
    omega
  have hround := roundAddMagnitudesAtScale_eq_roundDyadic
    productSign zSign product
      (zMantissa <<< (zProductScale - productScale))
      productScale hproduct hzShiftedNonzero hsum hproductScaleBound
  rw [hzShiftedToNat, hshiftToNat] at hround
  have halign := addDyadic_alignRightOffset 298
    productSign zSign product.toNat zMantissa.toNat
    productScale.toNat zProductScale.toNat
    (by simpa [← UInt64.toNat_inj] using hproduct) hzNat hscaleNat
  norm_num at halign
  exact hround.trans (congrArg roundDyadic halign.symm)

private theorem roundFmaAlignedLeft_eq
    (productSign zSign : Bool)
    (product zMantissa productScale zProductScale : UInt64)
    (hproduct : product ≠ 0) (hz : zMantissa ≠ 0)
    (hproductBound : product.toNat < 2 ^ 48)
    (hzBound : zMantissa.toNat < 2 ^ 24)
    (hzScaleBound : zProductScale.toNat ≤ 506)
    (hscale : ¬productScale ≤ zProductScale)
    (hshift : productScale - zProductScale ≤ 15) :
    roundProduct
        (FloatLib.Numerics.FixedWord.addSignedMagnitudes
          productSign zSign
          (product <<< (productScale - zProductScale)) zMantissa).1
        (FloatLib.Numerics.FixedWord.addSignedMagnitudes
          productSign zSign
          (product <<< (productScale - zProductScale)) zMantissa).2
        zProductScale =
      roundDyadic
        (Model.addDyadic
          { negative := productSign
            significand := product.toNat
            exponent := Int.ofNat productScale.toNat - 298 }
          { negative := zSign
            significand := zMantissa.toNat
            exponent := Int.ofNat zProductScale.toNat - 298 }) := by
  have hscaleNat : zProductScale.toNat < productScale.toNat := by
    have hnot : ¬productScale.toNat ≤ zProductScale.toNat := by
      intro hle
      exact hscale (UInt64.le_iff_toNat_le.mpr hle)
    omega
  have hscaleWord : zProductScale ≤ productScale :=
    UInt64.le_iff_toNat_le.mpr hscaleNat.le
  have hshiftToNat :
      (productScale - zProductScale).toNat =
        productScale.toNat - zProductScale.toNat := by
    rw [UInt64.toNat_sub_of_le productScale zProductScale hscaleWord]
  have hshiftNatLe : (productScale - zProductScale).toNat ≤ 15 := by
    have h := UInt64.le_iff_toNat_le.mp hshift
    simpa using h
  have hshiftNatLt : (productScale - zProductScale).toNat < 64 := by
    omega
  have hproductNat : product.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hproduct
  have hproductLogLt : product.toNat.log2 < 48 := by
    rw [Nat.log2_lt hproductNat]
    exact hproductBound
  have hproductShiftedBound :
      product.toNat <<< (productScale - zProductScale).toNat < 2 ^ 63 := by
    calc
      product.toNat <<< (productScale - zProductScale).toNat <
          2 ^ (product.toNat.log2 + 1 +
            (productScale - zProductScale).toNat) :=
        Nat.shiftLeft_lt Nat.lt_log2_self
      _ ≤ 2 ^ 63 := by
        apply Nat.pow_le_pow_right
        · decide
        · omega
  have hproductShiftedFit :
      product.toNat <<< (productScale - zProductScale).toNat < 2 ^ 64 :=
    lt_trans hproductShiftedBound (by norm_num)
  have hproductShiftedToNat :
      (product <<< (productScale - zProductScale)).toNat =
        product.toNat <<< (productScale - zProductScale).toNat := by
    rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hshiftNatLt,
      Nat.mod_eq_of_lt hproductShiftedFit]
  have hproductShiftedNatNonzero :
      product.toNat <<< (productScale - zProductScale).toNat ≠ 0 := by
    simp [Nat.shiftLeft_eq, hproductNat]
  have hproductShiftedNonzero :
      product <<< (productScale - zProductScale) ≠ 0 := by
    intro h
    have hnat := congrArg UInt64.toNat h
    rw [hproductShiftedToNat] at hnat
    exact hproductShiftedNatNonzero hnat
  have hsum :
      (product <<< (productScale - zProductScale)).toNat +
          zMantissa.toNat <
        2 ^ 64 := by
    rw [hproductShiftedToNat]
    norm_num at hzBound hproductShiftedBound ⊢
    omega
  have hround := roundAddMagnitudesAtScale_eq_roundDyadic
    productSign zSign
      (product <<< (productScale - zProductScale)) zMantissa
      zProductScale hproductShiftedNonzero hz hsum hzScaleBound
  rw [hproductShiftedToNat, hshiftToNat] at hround
  have halign := addDyadic_alignLeftOffset 298
    productSign zSign product.toNat zMantissa.toNat
    productScale.toNat zProductScale.toNat hproductNat
    (by simpa [← UInt64.toNat_inj] using hz) hscaleNat
  norm_num at halign
  exact hround.trans (congrArg roundDyadic halign.symm)

private theorem roundFmaFarAddNormal
    (sign : Bool) (small large smallScale dominantScale gap : Nat)
    (hsmall : small < 2 ^ 48)
    (hlargeLow : 2 ^ 23 ≤ large)
    (hlargeHigh : large < 2 ^ 24)
    (hgap : 48 < gap)
    (hscale : smallScale + gap = dominantScale + 149)
    (hdominantScale : dominantScale ≤ 253) :
    roundDyadic
        { negative := sign
          significand := (large <<< gap) + small
          exponent := Int.ofNat smallScale - 298 } =
      mkBits sign (dominantScale + 1) (large - 2 ^ 23) := by
  have hsmallHalf : small < 2 ^ (gap - 1) :=
    hsmall.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  rw [roundDyadic_shiftLeft_add_of_lt_half sign small large gap
    (Int.ofNat smallScale - 298) hlargeLow hlargeHigh (by omega) hsmallHalf
    (by simp only [Int.ofNat_eq_natCast]; omega)
    (by simp only [Int.ofNat_eq_natCast]; omega)]
  congr 1
  simp only [Int.ofNat_eq_natCast]
  omega

private theorem roundFmaFarAddSubnormal
    (sign : Bool) (small large smallScale gap : Nat)
    (hsmall : small < 2 ^ 48)
    (hlargePos : 0 < large)
    (hlargeHigh : large < 2 ^ 23)
    (hgap : 48 < gap)
    (hscale : smallScale + gap = 149) :
    roundDyadic
        { negative := sign
          significand := (large <<< gap) + small
          exponent := Int.ofNat smallScale - 298 } =
      mkBits sign 0 large := by
  have hlargeNe : large ≠ 0 := Nat.ne_of_gt hlargePos
  have hcombinedPos : 0 < (large <<< gap) + small := by
    simp only [Nat.shiftLeft_eq]
    positivity
  have hcombinedNe : (large <<< gap) + small ≠ 0 :=
    Nat.ne_of_gt hcombinedPos
  have hsmallGap : small < 2 ^ gap := by
    exact hsmall.trans_le <|
      Nat.pow_le_pow_right (by decide) (by omega)
  have hcombinedUpper :
      (large <<< gap) + small < 2 ^ (23 + gap) := by
    have hlargeSucc : large + 1 ≤ 2 ^ 23 := by omega
    calc
      (large <<< gap) + small = large * 2 ^ gap + small := by
        rw [Nat.shiftLeft_eq]
      _ < large * 2 ^ gap + 2 ^ gap := Nat.add_lt_add_left hsmallGap _
      _ = (large + 1) * 2 ^ gap := by ring
      _ ≤ 2 ^ 23 * 2 ^ gap := Nat.mul_le_mul_right _ hlargeSucc
      _ = 2 ^ (23 + gap) := by rw [pow_add]
  have hcombinedLog :
      ((large <<< gap) + small).log2 < 23 + gap := by
    rw [Nat.log2_lt hcombinedNe]
    exact hcombinedUpper
  have hcombinedSubnormal :
      Int.ofNat ((large <<< gap) + small).log2 +
          (Int.ofNat smallScale - 298) < -126 := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hgapPos : 0 < gap := by omega
  have hsmallHalf : small < Model.pow2 (gap - 1) := by
    rw [Model.pow2_eq_two_pow]
    exact hsmall.trans_le <|
      Nat.pow_le_pow_right (by decide) (by omega)
  have hround :
      Numerics.roundShiftRightEven ((large <<< gap) + small) gap = large :=
    Model.roundShiftRightEven_shiftLeft_add_of_lt_half
      large small gap hgapPos hsmallHalf
  have hcombinedExponent :
      Int.ofNat smallScale - 298 + 149 =
        Int.negSucc (gap - 1) := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hlargePow : large ≠ Model.pow2 23 := by
    rw [Model.pow2_eq_two_pow]
    omega
  have hshift : gap - 1 + 1 = gap := by omega
  unfold roundDyadic
  simp only [beq_iff_eq, hcombinedNe, ite_false,
    hcombinedSubnormal, hcombinedExponent]
  rw [hshift, hround]
  simp [hlargeNe, hlargePow]

private theorem roundFmaFarAddValue
    (z : Value) (small smallScale gap : Nat)
    (hsmall : small < 2 ^ 48)
    (hzFinite : expField (toUInt32 z) ≠ 0xff)
    (hzNonzero :
      finiteMantissa
        (expField (toUInt32 z)) (fracField (toUInt32 z)) ≠ 0)
    (hgap : 48 < gap)
    (hscale :
      smallScale + gap =
        (finiteScale (expField (toUInt32 z))).toNat + 149) :
    roundDyadic
        { negative := signBit (toUInt32 z)
          significand :=
            (finiteMantissa
                (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat <<< gap +
              small
          exponent := Int.ofNat smallScale - 298 } =
      toUInt32 z := by
  have hfraction := fracField_lt z
  have hlargeNonzero :
      (finiteMantissa
          (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hzNonzero
  have hscaleBound :
      (finiteScale (expField (toUInt32 z))).toNat ≤ 253 :=
    finiteScale_le
      (expField (toUInt32 z)) (expField_lt z) hzFinite
  by_cases hexponent : expField (toUInt32 z) = 0
  · have hlarge :
        (finiteMantissa
            (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat =
          (fracField (toUInt32 z)).toNat := by
      rw [finiteMantissa_toNat
        (expField (toUInt32 z)) (fracField (toUInt32 z)) hfraction]
      simp [hexponent]
    have hlargePos : 0 < (fracField (toUInt32 z)).toNat := by
      rw [← hlarge]
      exact Nat.pos_of_ne_zero hlargeNonzero
    have hscaleZero :
        (finiteScale (expField (toUInt32 z))).toNat = 0 := by
      rw [finiteScale_toNat]
      simp [hexponent]
    have hscale' : smallScale + gap = 149 := by
      rw [hscale, hscaleZero]
    rw [hlarge]
    rw [roundFmaFarAddSubnormal
      (signBit (toUInt32 z)) small (fracField (toUInt32 z)).toNat
      smallScale gap hsmall hlargePos hfraction hgap hscale']
    simpa [hexponent] using mkBits_fields (toUInt32 z)
  · have hlarge :
        (finiteMantissa
            (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat =
          Model.pow2 23 + (fracField (toUInt32 z)).toNat := by
      simpa [hexponent] using
        finiteMantissa_toNat
          (expField (toUInt32 z)) (fracField (toUInt32 z)) hfraction
    have hlargeLow :
        2 ^ 23 ≤
          (finiteMantissa
            (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat := by
      rw [hlarge, Model.pow2_eq_two_pow]
      omega
    have hlargeHigh :
        (finiteMantissa
            (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat <
          2 ^ 24 :=
      finiteMantissa_lt
        (expField (toUInt32 z)) (fracField (toUInt32 z)) hfraction
    have hscaleToNat :
        (finiteScale (expField (toUInt32 z))).toNat =
          (expField (toUInt32 z)).toNat - 1 := by
      rw [finiteScale_toNat]
      simp [hexponent]
    have hexponentNatNonzero :
        (expField (toUInt32 z)).toNat ≠ 0 := by
      intro h
      apply hexponent
      apply UInt32.toNat_inj.mp
      simpa using h
    have hexponentValue :
        (finiteScale (expField (toUInt32 z))).toNat + 1 =
          (expField (toUInt32 z)).toNat := by
      rw [hscaleToNat]
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hexponentNatNonzero)
    have hfractionValue :
        (finiteMantissa
            (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat -
            2 ^ 23 =
          (fracField (toUInt32 z)).toNat := by
      rw [hlarge, Model.pow2_eq_two_pow]
      omega
    rw [roundFmaFarAddNormal
      (signBit (toUInt32 z)) small
      (finiteMantissa
        (expField (toUInt32 z)) (fracField (toUInt32 z))).toNat
      smallScale (finiteScale (expField (toUInt32 z))).toNat gap
      hsmall hlargeLow hlargeHigh hgap hscale hscaleBound]
    rw [hexponentValue, hfractionValue]
    exact mkBits_fields (toUInt32 z)

private theorem fmaFarSameSignResult (x y z : Value) :
  let xExponent := expField (toUInt32 x);
  let yExponent := expField (toUInt32 y);
  let zExponent := expField (toUInt32 z);
    let xFraction := fracField (toUInt32 x);
    let yFraction := fracField (toUInt32 y);
    let zFraction := fracField (toUInt32 z);
      let xMantissa := finiteMantissa xExponent xFraction;
      let yMantissa := finiteMantissa yExponent yFraction;
      let zMantissa := finiteMantissa zExponent zFraction;
        let xScale := finiteScale xExponent;
        let yScale := finiteScale yExponent;
        let zScale := finiteScale zExponent;
          let product := xMantissa * yMantissa;
          let productScale := xScale + yScale;
          let zProductScale := zScale + 149;
          ¬zExponent = 255 →
            ¬product = 0 →
              ¬zMantissa = 0 →
                zMantissa.toNat < 2 ^ 24 →
                  xMantissa.toNat * yMantissa.toNat < 2 ^ 48 →
                    product.toNat = xMantissa.toNat * yMantissa.toNat →
                      product.toNat < 2 ^ 48 →
                        zProductScale.toNat = zScale.toNat + 149 →
                          Int.ofNat productScale.toNat - 298 =
                              Int.ofNat xScale.toNat - 149 + (Int.ofNat yScale.toNat - 149) →
                            Int.ofNat zProductScale.toNat - 298 = Int.ofNat zScale.toNat - 149 →
                              productScale ≤ zProductScale →
                                48 < zProductScale - productScale →
                                  (signBit (toUInt32 x) ^^ signBit (toUInt32 y)) = signBit
                                    (toUInt32 z) →
                                    some z =
                                      some
                                        (ofUInt32
                                          (roundDyadic
                                            (addDyadic
                                              { negative := signBit (toUInt32 x) ^^ signBit
                                                  (toUInt32 y),
                                                significand := xMantissa.toNat * yMantissa.toNat,
                                                exponent :=
                                                  Int.ofNat xScale.toNat - 149 + (Int.ofNat
                                                    yScale.toNat - 149) }
                                              { negative := signBit (toUInt32 z), significand :=
                                                  zMantissa.toNat,
                                                exponent := Int.ofNat zScale.toNat - 149 }))) := by
  intro xExponent yExponent zExponent xFraction yFraction zFraction
    xMantissa yMantissa zMantissa xScale yScale zScale product productScale
    zProductScale hzExceptional hproductZero hzZero hzMantissaLt hproductNatBound hproductToNat
    hproductBound hzProductScaleToNat hproductExponent hzExponentValue hscale hfar hsign
  have hscaleNat : productScale.toNat ≤ zProductScale.toNat :=
    UInt64.le_iff_toNat_le.mp hscale
  have hshiftToNat :
      (zProductScale - productScale).toNat =
        zProductScale.toNat - productScale.toNat := by
    rw [UInt64.toNat_sub_of_le zProductScale productScale hscale]
  have hfarNat :
      48 < zProductScale.toNat - productScale.toNat := by
    rw [← hshiftToNat]
    have h := UInt64.lt_iff_toNat_lt.mp hfar
    simpa using h
  have hproductNatNonzero : product.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hproductZero
  have hzNatNonzero : zMantissa.toNat ≠ 0 := by
    simpa [← UInt64.toNat_inj] using hzZero
  have hzShiftedNonzero :
      zMantissa.toNat <<<
          (zProductScale.toNat - productScale.toNat) ≠ 0 := by
    simp [Nat.shiftLeft_eq, hzNatNonzero]
  have hzMantissaValue :
      zMantissa =
        finiteMantissa
          (expField (toUInt32 z)) (fracField (toUInt32 z)) := rfl
  have hzScaleValue :
      zScale = finiteScale (expField (toUInt32 z)) := rfl
  have hzActualFinite :
      expField (toUInt32 z) ≠ 0xff := hzExceptional
  have hscaleValue :
      productScale.toNat +
          (zProductScale.toNat - productScale.toNat) =
        (finiteScale (expField (toUInt32 z))).toNat + 149 := by
    rw [← hzScaleValue, ← hzProductScaleToNat]
    omega
  have halign := addDyadic_alignRightOffset 298
    (signBit (toUInt32 x) ^^ signBit (toUInt32 y))
    (signBit (toUInt32 z))
    product.toNat zMantissa.toNat
    productScale.toNat zProductScale.toNat
    hproductNatNonzero hzNatNonzero hscaleNat
  norm_num at halign
  have hround :
      roundDyadic
          (Model.addDyadic
            { negative :=
                signBit (toUInt32 x) ^^ signBit (toUInt32 y)
              significand := product.toNat
              exponent := Int.ofNat productScale.toNat - 298 }
            { negative := signBit (toUInt32 z)
              significand := zMantissa.toNat
              exponent := Int.ofNat zProductScale.toNat - 298 }) =
        toUInt32 z := by
    simp only [Int.ofNat_eq_natCast] at halign ⊢
    rw [halign, hsign]
    rw [addDyadic_sameSign_sameExponent
      (signBit (toUInt32 z)) product.toNat
      (zMantissa.toNat <<<
        (zProductScale.toNat - productScale.toNat))
      ((productScale.toNat : Int) - 298)
      hproductNatNonzero hzShiftedNonzero, Nat.add_comm product.toNat]
    rw [hzMantissaValue]
    exact roundFmaFarAddValue z product.toNat productScale.toNat
      (zProductScale.toNat - productScale.toNat)
      hproductBound hzActualFinite
      (by simpa [hzMantissaValue] using hzZero)
      hfarNat hscaleValue
  rw [hproductToNat, hproductExponent, hzExponentValue] at hround
  have hresult :
      ofUInt32
          (roundDyadic
            (Model.addDyadic
              { negative :=
                  signBit (toUInt32 x) ^^ signBit (toUInt32 y)
                significand := xMantissa.toNat * yMantissa.toNat
                exponent :=
                  (Int.ofNat xScale.toNat - 149) +
                    (Int.ofNat yScale.toNat - 149) }
              { negative := signBit (toUInt32 z)
                significand := zMantissa.toNat
                exponent := Int.ofNat zScale.toNat - 149 })) =
        z := by
    rw [hround]
    exact ofUInt32_toUInt32 z
  exact congrArg some hresult.symm

private theorem fmaFiniteAlignmentCases (x y z : Value) :
  let xExponent := expField (toUInt32 x);
  let yExponent := expField (toUInt32 y);
  let zExponent := expField (toUInt32 z);
    let xFraction := fracField (toUInt32 x);
    let yFraction := fracField (toUInt32 y);
    let zFraction := fracField (toUInt32 z);
      let xMantissa := finiteMantissa xExponent xFraction;
      let yMantissa := finiteMantissa yExponent yFraction;
      let zMantissa := finiteMantissa zExponent zFraction;
        let xScale := finiteScale xExponent;
        let yScale := finiteScale yExponent;
        let zScale := finiteScale zExponent;
          let product := xMantissa * yMantissa;
          let productScale := xScale + yScale;
          let zProductScale := zScale + 149;
          ¬zExponent = 255 →
            ¬product = 0 →
              ¬zMantissa = 0 →
                zMantissa.toNat < 2 ^ 24 →
                  xMantissa.toNat * yMantissa.toNat < 2 ^ 48 →
                    product.toNat = xMantissa.toNat * yMantissa.toNat →
                      product.toNat < 2 ^ 48 →
                        zProductScale.toNat = zScale.toNat + 149 →
                          productScale.toNat ≤ 506 →
                            zProductScale.toNat ≤ 506 →
                              Int.ofNat productScale.toNat - 298 =
                                  Int.ofNat xScale.toNat - 149 + (Int.ofNat yScale.toNat - 149) →
                                Int.ofNat zProductScale.toNat - 298 = Int.ofNat zScale.toNat - 149 →
                                  (if productScale ≤ zProductScale then
                                      if zProductScale - productScale ≤ 39 then
                                        some
                                          (ofUInt32
                                            (roundProduct
                                              (Numerics.FixedWord.addSignedMagnitudes
                                                  (signBit (toUInt32 x) ^^ signBit (toUInt32 y))
                                                    (signBit (toUInt32 z))
                                                  product (zMantissa <<< (zProductScale -
                                                    productScale))).1
                                              (Numerics.FixedWord.addSignedMagnitudes
                                                  (signBit (toUInt32 x) ^^ signBit (toUInt32 y))
                                                    (signBit (toUInt32 z))
                                                  product (zMantissa <<< (zProductScale -
                                                    productScale))).2
                                              productScale))
                                      else
                                        if
                                            (decide (48 < zProductScale - productScale) &&
                                                (signBit (toUInt32 x) ^^ signBit (toUInt32 y)) ==
                                                  signBit (toUInt32 z)) =
                                              true then
                                          some z
                                        else
                                          fmaExactFiniteOption (signBit (toUInt32 x) ^^ signBit
                                            (toUInt32 y))
                                            (signBit (toUInt32 z)) product productScale zMantissa
                                              zProductScale
                                    else
                                      if productScale - zProductScale ≤ 15 then
                                        some
                                          (ofUInt32
                                            (roundProduct
                                              (Numerics.FixedWord.addSignedMagnitudes
                                                  (signBit (toUInt32 x) ^^ signBit (toUInt32 y))
                                                    (signBit (toUInt32 z))
                                                  (product <<< (productScale - zProductScale))
                                                    zMantissa).1
                                              (Numerics.FixedWord.addSignedMagnitudes
                                                  (signBit (toUInt32 x) ^^ signBit (toUInt32 y))
                                                    (signBit (toUInt32 z))
                                                  (product <<< (productScale - zProductScale))
                                                    zMantissa).2
                                              zProductScale))
                                      else
                                        fmaExactFiniteOption (signBit (toUInt32 x) ^^ signBit
                                          (toUInt32 y))
                                          (signBit (toUInt32 z)) product productScale zMantissa
                                            zProductScale) =
                                    some
                                      (ofUInt32
                                        (roundDyadic
                                          (addDyadic
                                            { negative := signBit (toUInt32 x) ^^ signBit
                                                (toUInt32 y),
                                              significand := xMantissa.toNat * yMantissa.toNat,
                                              exponent :=
                                                Int.ofNat xScale.toNat - 149 + (Int.ofNat
                                                  yScale.toNat - 149) }
                                            { negative := signBit (toUInt32 z), significand :=
                                                zMantissa.toNat,
                                              exponent := Int.ofNat zScale.toNat - 149 }))) := by
  intro xExponent yExponent zExponent xFraction yFraction zFraction
    xMantissa yMantissa zMantissa xScale yScale zScale product productScale
    zProductScale hzExceptional hproductZero hzZero hzMantissaLt hproductNatBound hproductToNat
    hproductBound hzProductScaleToNat hproductScaleLe hzProductScaleLe hproductExponent
    hzExponentValue
  by_cases hscale : productScale ≤ zProductScale
  · rw [ite_eq_left hscale]
    by_cases hshift : zProductScale - productScale ≤ 39
    · rw [ite_eq_left hshift]
      have hround := roundFmaAlignedRight_eq
        (signBit (toUInt32 x) ^^ signBit (toUInt32 y))
        (signBit (toUInt32 z))
        product zMantissa productScale zProductScale
        hproductZero hzZero hproductBound hzMantissaLt hproductScaleLe hscale hshift
      rw [hproductToNat, hproductExponent, hzExponentValue] at hround
      exact congrArg (fun bits => some (ofUInt32 bits)) hround
    · rw [ite_eq_right hshift]
      by_cases hfar : 48 < zProductScale - productScale
      · by_cases hsign :
          (signBit (toUInt32 x) ^^ signBit (toUInt32 y)) =
            signBit (toUInt32 z)
        · have hcondition :
              (decide (48 < zProductScale - productScale) &&
                ((signBit (toUInt32 x) ^^ signBit (toUInt32 y)) ==
                  signBit (toUInt32 z))) = true := by
            simp [hfar, hsign]
          rw [ite_eq_left hcondition]
          exact fmaFarSameSignResult (x := x) (y := y) (z := z)
            hzExceptional hproductZero hzZero hzMantissaLt hproductNatBound
            hproductToNat hproductBound hzProductScaleToNat hproductExponent hzExponentValue
            hscale hfar hsign
        · have hcondition :
              ¬(decide (48 < zProductScale - productScale) &&
                ((signBit (toUInt32 x) ^^ signBit (toUInt32 y)) ==
                  signBit (toUInt32 z))) = true := by
            simpa [hfar] using hsign
          rw [ite_eq_right hcondition]
          unfold fmaExactFiniteOption
          rw [hproductToNat, hproductExponent, hzExponentValue]
      · have hcondition :
            ¬(decide (48 < zProductScale - productScale) &&
              ((signBit (toUInt32 x) ^^ signBit (toUInt32 y)) ==
                signBit (toUInt32 z))) = true := by
          simp [hfar]
        rw [ite_eq_right hcondition]
        unfold fmaExactFiniteOption
        rw [hproductToNat, hproductExponent, hzExponentValue]
  · rw [ite_eq_right hscale]
    by_cases hshift : productScale - zProductScale ≤ 15
    · rw [ite_eq_left hshift]
      have hround := roundFmaAlignedLeft_eq
        (signBit (toUInt32 x) ^^ signBit (toUInt32 y))
        (signBit (toUInt32 z))
        product zMantissa productScale zProductScale
        hproductZero hzZero hproductBound hzMantissaLt hzProductScaleLe hscale hshift
      rw [hproductToNat, hproductExponent, hzExponentValue] at hround
      exact congrArg (fun bits => some (ofUInt32 bits)) hround
    · rw [ite_eq_right hshift]
      unfold fmaExactFiniteOption
      rw [hproductToNat, hproductExponent, hzExponentValue]

/--
The guarded `UInt64` fused multiply-add kernel equals the generic exact-dyadic finite
implementation.
-/
theorem fmaFiniteImpl_eq (x y z : Value) :
    fmaFiniteImplOption x y z = fmaFiniteOption x y z := by
  unfold fmaFiniteImplOption fmaFiniteOption
  rw [toDyadic_eq_finiteComponents x, toDyadic_eq_finiteComponents y,
    toDyadic_eq_finiteComponents z]
  dsimp only
  simp only [Bool.or_eq_true, beq_iff_eq]
  set xExponent := expField (toUInt32 x) with hxExponent
  set yExponent := expField (toUInt32 y) with hyExponent
  set zExponent := expField (toUInt32 z) with hzExponent
  set xFraction := fracField (toUInt32 x) with hxFraction
  set yFraction := fracField (toUInt32 y) with hyFraction
  set zFraction := fracField (toUInt32 z) with hzFraction
  set xMantissa := finiteMantissa xExponent xFraction with hxMantissa
  set yMantissa := finiteMantissa yExponent yFraction with hyMantissa
  set zMantissa := finiteMantissa zExponent zFraction with hzMantissa
  set xScale := finiteScale xExponent with hxScale
  set yScale := finiteScale yExponent with hyScale
  set zScale := finiteScale zExponent with hzScale
  set product : UInt64 := xMantissa * yMantissa with hproductDef
  set productScale : UInt64 := xScale + yScale with hproductScaleDef
  set zProductScale : UInt64 := zScale + 149 with hzProductScaleDef
  by_cases hxExceptional : xExponent = 0xff
  · simp [hxExceptional]
  by_cases hyExceptional : yExponent = 0xff
  · simp [hxExceptional, hyExceptional]
  by_cases hzExceptional : zExponent = 0xff
  · simp [hxExceptional, hyExceptional, hzExceptional]
  by_cases hproductZero : product = 0
  · simp [hxExceptional, hyExceptional, hzExceptional, hproductZero]
  by_cases hzZero : zMantissa = 0
  · simp [hxExceptional, hyExceptional, hzExceptional, hproductZero, hzZero]
  have hxZero : xMantissa ≠ 0 := by
    intro h
    apply hproductZero
    rw [hproductDef, h]
    simp
  have hyZero : yMantissa ≠ 0 := by
    intro h
    apply hproductZero
    rw [hproductDef, h]
    simp
  simp only [hxExceptional, hyExceptional, hzExceptional, hxZero, hyZero, hzZero,
    hproductZero, or_false, ite_false]
  have hxMantissaLt :=
    finiteMantissa_lt_of_components x hxExponent hxFraction hxMantissa
  have hyMantissaLt :=
    finiteMantissa_lt_of_components y hyExponent hyFraction hyMantissa
  have hzMantissaLt :=
    finiteMantissa_lt_of_components z hzExponent hzFraction hzMantissa
  have hproductNatBound :
      xMantissa.toNat * yMantissa.toNat < 2 ^ 48 := by
    norm_num at hxMantissaLt hyMantissaLt ⊢
    nlinarith
  have hproductToNat :
      product.toNat = xMantissa.toNat * yMantissa.toNat := by
    rw [hproductDef, UInt64.toNat_mul]
    apply Nat.mod_eq_of_lt
    exact lt_trans hproductNatBound (by norm_num)
  have hproductBound : product.toNat < 2 ^ 48 := by
    rw [hproductToNat]
    exact hproductNatBound
  have hxScaleLe :=
    finiteScale_le_of_components x hxExponent hxScale hxExceptional
  have hyScaleLe :=
    finiteScale_le_of_components y hyExponent hyScale hyExceptional
  have hzScaleLe :=
    finiteScale_le_of_components z hzExponent hzScale hzExceptional
  have hproductScaleToNat :
      productScale.toNat = xScale.toNat + yScale.toNat := by
    rw [hproductScaleDef, UInt64.toNat_add]
    apply Nat.mod_eq_of_lt
    omega
  have hzProductScaleToNat :
      zProductScale.toNat = zScale.toNat + 149 := by
    rw [hzProductScaleDef, UInt64.toNat_add]
    rw [show (149 : UInt64).toNat = 149 by decide]
    apply Nat.mod_eq_of_lt
    omega
  have hproductScaleLe : productScale.toNat ≤ 506 := by
    rw [hproductScaleToNat]
    omega
  have hzProductScaleLe : zProductScale.toNat ≤ 506 := by
    rw [hzProductScaleToNat]
    omega
  have hproductExponent :
      Int.ofNat productScale.toNat - 298 =
        (Int.ofNat xScale.toNat - 149) +
          (Int.ofNat yScale.toNat - 149) := by
    rw [hproductScaleToNat]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    omega
  have hzExponentValue :
      Int.ofNat zProductScale.toNat - 298 =
        Int.ofNat zScale.toNat - 149 := by
    rw [hzProductScaleToNat]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_ofNat]
    omega
  exact fmaFiniteAlignmentCases (x := x) (y := y) (z := z)
    hzExceptional hproductZero hzZero hzMantissaLt hproductNatBound hproductToNat
    hproductBound hzProductScaleToNat hproductScaleLe hzProductScaleLe hproductExponent
    hzExponentValue

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
