/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ZerothOrderIteration
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.GradientScaleReadout

/-!
# ZerothOrderGradient

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Gradient Morrey rows with a bounded scalar source
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-- The additional dimension coefficient paid by the scalar source. -/
def smallContrastZerothGradientExtraConstant (d : ℕ) [NeZero d] : ℝ :=
  8 * ((1 / 2 : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 *
    unitCubeDirichletPoincareExplicit d * (d : ℝ)

theorem smallContrastZerothGradientExtraConstant_nonneg (d : ℕ) [NeZero d] :
    0 ≤ smallContrastZerothGradientExtraConstant d := by
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg _))
      (unitCubeDirichletPoincareExplicit_nonneg d)) (Nat.cast_nonneg d)

/-- A dimension-only coefficient controlling all three data rows. -/
def smallContrastZerothGradientConstant (d : ℕ) [NeZero d] : ℝ :=
  smallContrastGradientConstant d + smallContrastZerothGradientExtraConstant d

theorem smallContrastZerothGradientConstant_nonneg (d : ℕ) [NeZero d] :
    0 ≤ smallContrastZerothGradientConstant d :=
  add_nonneg (smallContrastGradientConstant_nonneg d)
    (smallContrastZerothGradientExtraConstant_nonneg d)

private theorem combine_three_data
    {Cb Cg X Y G : ℝ} (hCb : 0 ≤ Cb) (hCg : 0 ≤ Cg)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hG : 0 ≤ G) :
    Cb * X + Cb * Y + Cg * G ≤ (Cb + Cg) * (X + Y + G) := by
  calc
    Cb * X + Cb * Y + Cg * G ≤
        Cb * X + Cb * Y + Cg * G + (Cb * G + Cg * X + Cg * Y) := by
      exact le_add_of_nonneg_right <| add_nonneg
        (add_nonneg (mul_nonneg hCb hG) (mul_nonneg hCg hX)) (mul_nonneg hCg hY)
    _ = (Cb + Cg) * (X + Y + G) := by ring

private theorem zerothOrder_readout_price
    {H P Pd D F G N : ℝ}
    (hH : 1 ≤ H) (hP : 0 ≤ P) (hPd : 0 ≤ Pd)
    (hD : 0 ≤ D) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hN : N ≤ H * P * D) :
    H * (N + 16 * H * P * F + 8 * H * Pd * (d : ℝ) * G) ≤
      (16 * H ^ 2 * P + 8 * H ^ 2 * Pd * (d : ℝ)) * (D + F + G) := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hfirst : H * N ≤ 16 * H ^ 2 * P * D := by
    have hmul := mul_le_mul_of_nonneg_left hN hH0
    have hbase0 : 0 ≤ H ^ 2 * P * D :=
      mul_nonneg (mul_nonneg (sq_nonneg H) hP) hD
    calc
      H * N ≤ H * (H * P * D) := hmul
      _ = H ^ 2 * P * D := by ring
      _ ≤ 16 * H ^ 2 * P * D := by
        simpa only [one_mul, mul_assoc] using
          mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 16) hbase0
  have hCb : 0 ≤ 16 * H ^ 2 * P :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg H)) hP
  have hCg : 0 ≤ 8 * H ^ 2 * Pd * (d : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg H)) hPd)
      (Nat.cast_nonneg d)
  calc
    H * (N + 16 * H * P * F + 8 * H * Pd * (d : ℝ) * G) =
        H * N + (16 * H ^ 2 * P) * F + (8 * H ^ 2 * Pd * (d : ℝ)) * G := by
      ring
    _ ≤ (16 * H ^ 2 * P) * D + (16 * H ^ 2 * P) * F +
        (8 * H ^ 2 * Pd * (d : ℝ)) * G :=
      add_le_add (add_le_add hfirst le_rfl) le_rfl
    _ ≤ (16 * H ^ 2 * P + 8 * H ^ 2 * Pd * (d : ℝ)) * (D + F + G) :=
      combine_three_data hCb hCg hD hF hG

private theorem gradientScaleBound_zerothOrder_on_ball [NeZero d]
    {U : Set (Vec d)} (z : Vec d) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (houter : euclideanBall z R ⊆ U)
    {a : CoeffField d} {u : H1Function U} {g : Vec d → ℝ} {f : Vec d → Vec d}
    {delta alpha : ℝ}
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hUopen : IsOpen U) (hmeas : Measurable a)
    (ha : CoefficientIdentityDistanceLE U a delta)
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a U u g f)
    (hg : MemScalarLInfOn U g)
    (hf : MemVectorLpOn U (schauderSourceExponent d alpha) f) :
    ∀ s : ℝ, 0 < s → s ≤ R →
      s ^ (1 - alpha) * vectorNormalizedL2On (euclideanBall z s) u.grad ≤
        (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
          (R ^ (1 - alpha) * vectorNormalizedL2On (euclideanBall z R) u.grad +
            16 * (1 - alpha)⁻¹ *
              ((1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
                smallContrastUnitBallVolumePrice d) *
              vectorLpSizeOn U (schauderSourceExponent d alpha) f +
            8 * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
              unitCubeDirichletPoincareExplicit d * (d : ℝ) * scalarLInfSizeOn U g) := by
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha.1
  have hdyadic := dyadicGradientScaleBound_zerothOrder_on_interiorBall z hR hR1 houter
    hd halpha0 halpha.2 hdelta0 hdelta hUopen hmeas ha hu hg hf
  have hgradR : MemVectorL2 (euclideanBall z R) u.grad :=
    u.grad_memVectorL2.mono_measure (Measure.restrict_mono houter le_rfl)
  exact gradientScaleBound_of_dyadic z hR halpha.2 hgradR hdyadic

/-- Uniform interior Morrey-gradient bound with a bounded scalar source. -/
theorem interiorGradientScaleBound_of_smallContrast_zerothOrder [NeZero d]
    {a : CoeffField d} {u : H1Function (smallContrastUnitBall d)}
    {g : Vec d → ℝ} {f : Vec d → Vec d} {delta alpha : ℝ}
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hmeas : Measurable a)
    (ha : CoefficientIdentityDistanceLE (smallContrastUnitBall d) a delta)
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a (smallContrastUnitBall d) u g f)
    (hg : MemScalarLInfOn (smallContrastUnitBall d) g)
    (hf : MemVectorLpOn (smallContrastUnitBall d) (schauderSourceExponent d alpha) f) :
    HasInteriorSmallContrastGradientScaleBound alpha
      (smallContrastZerothGradientConstant d *
        smallContrastZerothOrderDataSize d alpha u f g) u := by
  have hgradUnit : MemVectorL2 (smallContrastUnitBall d) u.grad := u.grad_memVectorL2
  have hgradNorm := vectorNormalizedL2On_euclideanBall_le_price_mul_rpow_mul_globalLp
    (d := d) (U := smallContrastUnitBall d) (0 : Vec d) (r := 1) (p := 2)
    (f := u.grad) (by norm_num) (by norm_num) Set.Subset.rfl (by
      change MemLp (fun x => HilbertVec.ofVec (u.grad x)) (ENNReal.ofReal 2)
        (volume.restrict (smallContrastUnitBall d))
      simpa only [ENNReal.ofReal_ofNat] using!
        memHilbertVectorL2_hilbertifyVecField hgradUnit)
  intro z hz r hr hrhalf
  have houter : euclideanBall z (1 / 2) ⊆ smallContrastUnitBall d := by
    apply euclideanBall_subset_of_center_distance_add_lt (by norm_num)
    have hzE := (mem_euclideanBall_toEuc_iff z 0 (by norm_num : (0 : ℝ) < 1 / 2)).2 hz
    have hzN : euclideanNorm z < 1 / 2 := by
      have hzE' : ‖toEuc z‖ < (1 / 2 : ℝ) := by
        simpa only [Metric.mem_ball, map_zero, dist_zero_right] using hzE
      unfold euclideanNorm
      have hsq := norm_sq_toEuc_sub z 0
      simp only [map_zero, sub_zero, euclideanSqDist] at hsq
      rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
      exact hzE'
    simpa only [sub_zero] using (show euclideanNorm z + 1 / 2 ≤ 1 by
      linarith only [hzN])
  have hread := gradientScaleBound_zerothOrder_on_ball z (R := 1 / 2)
    (by norm_num) (by norm_num) houter hd halpha hdelta0 hdelta
    (isOpen_euclideanBall 0 1) hmeas ha hu hg hf r hr hrhalf
  have hhalfNorm := vectorNormalizedL2On_le_of_subset houter
    (lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero
        (0 : Vec d) (by norm_num))))
    (lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero
        z (by norm_num))))
    (memHilbertVectorL2_hilbertifyVecField hgradUnit)
  have hratio : Real.sqrt ((volume (smallContrastUnitBall d)).toReal /
      (volume (euclideanBall z (1 / 2))).toReal) =
      (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) := by
    rw [volume_euclideanBall_toReal_eq_unit_mul_pow z (by norm_num)]
    have hV : 0 < (volume (smallContrastUnitBall d)).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg
        (Ne.symm (HCPolySupport.Book.Ch01.volume_euclideanBall_toReal_ne_zero
          (0 : Vec d) (by norm_num)))
    rw [show (volume (smallContrastUnitBall d)).toReal /
        ((volume (smallContrastUnitBall d)).toReal * (1 / 2 : ℝ) ^ d) =
        1 / ((1 / 2 : ℝ) ^ d) by field_simp]
    rw [show 1 / ((1 / 2 : ℝ) ^ d) = (2 : ℝ) ^ d by
      rw [div_pow]
      norm_num]
    rw [show Real.sqrt ((2 : ℝ) ^ d) = (2 : ℝ) ^ ((d : ℝ) / 2) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 2
      ring]
    rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
      Real.rpow_neg_eq_inv_rpow]
    norm_num
  rw [hratio] at hhalfNorm
  let H : ℝ := (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)
  let P : ℝ := smallContrastUnitBallVolumePrice d
  let Pd : ℝ := unitCubeDirichletPoincareExplicit d
  let D : ℝ := vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad
  let F : ℝ := (1 - alpha)⁻¹ * vectorLpSizeOn (smallContrastUnitBall d)
    (schauderSourceExponent d alpha) f
  let G : ℝ := scalarLInfSizeOn (smallContrastUnitBall d) g
  have hH : 1 ≤ H := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    (by norm_num) (by norm_num) (by
      have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith only [hd0])
  have hRpow : (1 / 2 : ℝ) ^ (1 - alpha) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (sub_nonneg.mpr halpha.2.le)
  have hgradNorm' : vectorNormalizedL2On (smallContrastUnitBall d) u.grad ≤ P * D := by
    dsimp only [P, D]
    simpa only [smallContrastUnitBall, Real.one_rpow, mul_one] using hgradNorm
  have hN : (1 / 2 : ℝ) ^ (1 - alpha) *
      vectorNormalizedL2On (euclideanBall z (1 / 2)) u.grad ≤ H * P * D := by
    have hmul := mul_le_mul hRpow hhalfNorm (Real.sqrt_nonneg _) zero_le_one
    have hnorm := mul_le_mul_of_nonneg_left hgradNorm' (zero_le_one.trans hH)
    exact hmul.trans <| by
      dsimp only [H, P, D]
      simpa only [one_mul, mul_assoc] using hnorm
  have hprice := zerothOrder_readout_price (d := d)
    (H := H) (P := P) (Pd := Pd) (D := D) (F := F) (G := G)
    (N := (1 / 2 : ℝ) ^ (1 - alpha) *
      vectorNormalizedL2On (euclideanBall z (1 / 2)) u.grad)
    hH (smallContrastUnitBallVolumePrice_nonneg d)
    (unitCubeDirichletPoincareExplicit_nonneg d)
    (show 0 ≤ D from ENNReal.toReal_nonneg)
    (show 0 ≤ F from
      mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr halpha.2.le)) ENNReal.toReal_nonneg)
    (show 0 ≤ G from ENNReal.toReal_nonneg) hN
  exact hread.trans <| by
    dsimp only [smallContrastZerothGradientConstant,
      smallContrastZerothGradientExtraConstant, smallContrastGradientConstant,
      smallContrastZerothOrderDataSize, smallContrastDataSize, H, P, Pd, D, F, G] at hprice ⊢
    convert hprice using 1
    all_goals first | rfl | ring

/-- Concentric gradient row for the zeroth-order equation. -/
theorem gradientScaleBound_of_smallContrast_zerothOrder [NeZero d]
    {a : CoeffField d} {u : H1Function (smallContrastUnitBall d)}
    {g : Vec d → ℝ} {f : Vec d → Vec d} {delta alpha : ℝ}
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hmeas : Measurable a)
    (ha : CoefficientIdentityDistanceLE (smallContrastUnitBall d) a delta)
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a (smallContrastUnitBall d) u g f)
    (hg : MemScalarLInfOn (smallContrastUnitBall d) g)
    (hf : MemVectorLpOn (smallContrastUnitBall d) (schauderSourceExponent d alpha) f) :
    HasSmallContrastGradientScaleBound alpha
      (smallContrastZerothGradientConstant d *
        smallContrastZerothOrderDataSize d alpha u f g) u := by
  have hgradUnit : MemVectorL2 (smallContrastUnitBall d) u.grad := u.grad_memVectorL2
  have hgradNorm := vectorNormalizedL2On_euclideanBall_le_price_mul_rpow_mul_globalLp
    (d := d) (U := smallContrastUnitBall d) (0 : Vec d) (r := 1) (p := 2)
    (f := u.grad) (by norm_num) (by norm_num) Set.Subset.rfl (by
      change MemLp (fun x => HilbertVec.ofVec (u.grad x)) (ENNReal.ofReal 2)
        (volume.restrict (smallContrastUnitBall d))
      simpa only [ENNReal.ofReal_ofNat] using!
        memHilbertVectorL2_hilbertifyVecField hgradUnit)
  have hread := gradientScaleBound_zerothOrder_on_ball (0 : Vec d) (R := 1)
    (by norm_num) (by norm_num) Set.Subset.rfl hd halpha hdelta0 hdelta
    (isOpen_euclideanBall 0 1) hmeas ha hu hg hf
  let H : ℝ := (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)
  let P : ℝ := smallContrastUnitBallVolumePrice d
  let Pd : ℝ := unitCubeDirichletPoincareExplicit d
  let D : ℝ := vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad
  let F : ℝ := (1 - alpha)⁻¹ * vectorLpSizeOn (smallContrastUnitBall d)
    (schauderSourceExponent d alpha) f
  let G : ℝ := scalarLInfSizeOn (smallContrastUnitBall d) g
  have hH : 1 ≤ H := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    (by norm_num) (by norm_num) (by
      have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith only [hd0])
  have hgradNorm' : vectorNormalizedL2On (smallContrastUnitBall d) u.grad ≤ P * D := by
    dsimp only [P, D]
    simpa only [smallContrastUnitBall, Real.one_rpow, mul_one] using hgradNorm
  have hN : vectorNormalizedL2On (smallContrastUnitBall d) u.grad ≤ H * P * D := by
    have hPD : 0 ≤ P * D := mul_nonneg
      (smallContrastUnitBallVolumePrice_nonneg d) ENNReal.toReal_nonneg
    exact hgradNorm'.trans <| by
      simpa only [one_mul, mul_assoc] using
        mul_le_mul_of_nonneg_right hH hPD
  have hprice := zerothOrder_readout_price (d := d)
    (H := H) (P := P) (Pd := Pd) (D := D) (F := F) (G := G)
    (N := vectorNormalizedL2On (smallContrastUnitBall d) u.grad)
    hH (smallContrastUnitBallVolumePrice_nonneg d)
    (unitCubeDirichletPoincareExplicit_nonneg d)
    (show 0 ≤ D from ENNReal.toReal_nonneg)
    (show 0 ≤ F from
      mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr halpha.2.le)) ENNReal.toReal_nonneg)
    (show 0 ≤ G from ENNReal.toReal_nonneg) hN
  intro r hr hr1
  have hraw := hread r hr hr1.le
  exact hraw.trans <| by
    dsimp only [smallContrastZerothGradientConstant,
      smallContrastZerothGradientExtraConstant, smallContrastGradientConstant,
      smallContrastZerothOrderDataSize, smallContrastDataSize, H, P, Pd, D, F, G] at hprice ⊢
    convert hprice using 1
    all_goals try simp only [smallContrastUnitBall, Real.one_rpow, one_mul]
    all_goals first | rfl | ring

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
