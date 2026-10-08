/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.AffineLiouvilleLocal
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorNormalizedL2Bridge
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.MeanSquareDeviation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.AffineLiouvilleGrowth

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Continuous-radius Liouville growth under affine pullback

The normalized scalar norm is compared on a source ball enlarged by the fixed
matrix distortion.  Homothetic ball volume scaling makes the comparison
constant independent of the radius.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set _root_.Filter
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

private theorem matVecMul_smul_one (q : ℝ) (x : Vec d) :
    matVecMul (q • (1 : Mat d)) x = q • x := by
  rw [smul_matVecMul, matVecMul_one]

theorem matImage_smul_one_euclideanBall
    {q : ℝ} (hq : 0 < q) (R : ℝ) :
    matImage (q • (1 : Mat d)) (euclideanBall d R) =
      euclideanBall d (q * R) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [matVecMul_smul_one]
    have hx' : vecNormSq x < R ^ 2 := by
      simpa only [HCPolySupport.HighContrast.euclideanBall,
        euclideanBallAt, Set.mem_ofPred_eq, sub_zero] using hx
    have hscaled : vecNormSq (q • x) < (q * R) ^ 2 := by
      rw [HCPolySupport.vecNormSq_smul]
      simpa only [mul_pow] using
        (mul_lt_mul_of_pos_left hx' (sq_pos_of_pos hq))
    simpa only [HCPolySupport.HighContrast.euclideanBall,
      euclideanBallAt, Set.mem_ofPred_eq, sub_zero] using hscaled
  · intro hy
    let x : Vec d := q⁻¹ • y
    refine ⟨x, ?_, ?_⟩
    · have hy' : vecNormSq y < (q * R) ^ 2 := by
        simpa only [HCPolySupport.HighContrast.euclideanBall,
          euclideanBallAt, Set.mem_ofPred_eq, sub_zero] using hy
      have hx' : vecNormSq x < R ^ 2 := by
        dsimp only [x]
        rw [HCPolySupport.vecNormSq_smul]
        calc
          q⁻¹ ^ 2 * vecNormSq y < q⁻¹ ^ 2 * (q * R) ^ 2 :=
            mul_lt_mul_of_pos_left hy' (sq_pos_of_pos (inv_pos.mpr hq))
          _ = R ^ 2 := by field_simp [hq.ne']
      simpa only [HCPolySupport.HighContrast.euclideanBall,
        euclideanBallAt, Set.mem_ofPred_eq, sub_zero] using hx'
    · rw [matVecMul_smul_one]
      funext i
      simp [x, hq.ne']

theorem volume_euclideanBall_mul
    {q : ℝ} (hq : 0 < q) (R : ℝ) :
    volume (euclideanBall d (q * R)) =
      ENNReal.ofReal (q ^ d) * volume (euclideanBall d R) := by
  let L : Mat d := q • (1 : Mat d)
  have hdet : L.det = q ^ d := by
    dsimp only [L]
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  rw [← matImage_smul_one_euclideanBall hq R,
    volume_matImage L (euclideanBall d R), hdet,
    abs_of_pos (pow_pos hq d)]

private theorem volume_euclideanBall_pos {R : ℝ} (hR : 0 < R) :
    volume (euclideanBall d R) ≠ 0 := by
  exact (ENNReal.toReal_ne_zero.mp
    (Book.Ch01.volume_euclideanBall_toReal_ne_zero (0 : Vec d) hR)).1

private theorem volume_euclideanBall_ne_top (R : ℝ) :
    volume (euclideanBall d R) ≠ ⊤ :=
  Book.Ch01.volume_euclideanBall_ne_top (0 : Vec d) R

/-- The normalized pullback norm on a centered ball is bounded by a fixed
determinant-and-distortion factor times the source norm on the enlarged ball. -/
theorem normalizedL2Norm_affinePullback_ball_le
    {L : Mat d} (hL : IsUnit L.det) {R : ℝ} (hR : 0 < R)
    (v : Vec d → ℝ) :
    normalizedL2Norm (euclideanBall d R)
        (fun y ↦ v (matVecMul L y)) ≤
      (ENNReal.ofReal
          (|L.det|⁻¹ * affineBallFactor L ^ d)) ^ (1 / 2 : ℝ) *
        normalizedL2Norm
          (euclideanBall d (affineBallFactor L * R)) v := by
  let q := affineBallFactor L
  let U := euclideanBall d (q * R)
  let V := matImage L⁻¹ U
  have hq : 0 < q := zero_lt_one.trans_le (one_le_affineBallFactor L)
  have hqR : 0 < q * R := mul_pos hq hR
  have hU : MeasurableSet U := (isOpen_euclideanBall d (q * R)).measurableSet
  have hV : MeasurableSet V := measurableSet_affinePullback hL hU
  have hsub : euclideanBall d R ⊆ V := by
    simpa only [q, U, V] using euclideanBall_subset_affinePullback_scaled hL R
  have hBzero := volume_euclideanBall_pos (d := d) hR
  have hBtop := volume_euclideanBall_ne_top (d := d) R
  have hvolV : volume V =
      ENNReal.ofReal (|L.det|⁻¹ * q ^ d) * volume (euclideanBall d R) := by
    calc
      volume V = ENNReal.ofReal |(L⁻¹).det| * volume U :=
        volume_matImage L⁻¹ U
      _ = ENNReal.ofReal |L.det|⁻¹ * volume U := by
        rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_inv]
      _ = ENNReal.ofReal |L.det|⁻¹ *
          (ENNReal.ofReal (q ^ d) * volume (euclideanBall d R)) := by
        rw [volume_euclideanBall_mul hq R]
      _ = ENNReal.ofReal (|L.det|⁻¹ * q ^ d) *
          volume (euclideanBall d R) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg _))]
        ac_rfl
  have hVzero : volume V ≠ 0 := by
    rw [hvolV]
    exact mul_ne_zero
      ((ENNReal.ofReal_pos.2
        (mul_pos (inv_pos.mpr (abs_pos.mpr hL.ne_zero)) (pow_pos hq d))).ne')
      hBzero
  have hVtop : volume V ≠ ⊤ := by
    rw [hvolV]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop
  have hbase := normalizedL2Norm_mono_set_le_volumeRatio
    hsub hBzero hBtop hVzero hVtop (fun y ↦ v (matVecMul L y))
  have himage := normalizedL2Norm_matImage hL hV v
  rw [matImage_matImage_inv hL] at himage
  have hratio : volume V / volume (euclideanBall d R) =
      ENNReal.ofReal (|L.det|⁻¹ * q ^ d) := by
    rw [hvolV, ENNReal.mul_div_cancel_right hBzero hBtop]
  rw [hratio, ← himage] at hbase
  simpa only [q, U, V] using hbase

private theorem rpow_scaled_negative
    {q R : ℝ} (hq : 0 < q) (hR : 0 < R) (theta : ℝ) :
    R ^ (-(1 + theta)) =
      q ^ (1 + theta) * (q * R) ^ (-(1 + theta)) := by
  rw [Real.mul_rpow hq.le hR.le]
  rw [show -(1 + theta) = -(1 + theta) by rfl]
  calc
    R ^ (-(1 + theta)) =
        (q ^ (1 + theta) * q ^ (-(1 + theta))) *
          R ^ (-(1 + theta)) := by
      rw [Real.rpow_neg hq.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hq _).ne',
        one_mul]
    _ = q ^ (1 + theta) *
        (q ^ (-(1 + theta)) * R ^ (-(1 + theta))) := by ring

/-- Continuous-radius Liouville growth is preserved by a fixed invertible
affine pullback. -/
theorem liouvilleGrowth_affinePullback
    {L : Mat d} (hL : IsUnit L.det) {theta : ℝ}
    {v : Vec d → ℝ}
    (hgrowth : Tendsto
      (fun R : ℝ ↦ ENNReal.ofReal (R ^ (-(1 + theta))) *
        normalizedL2Norm (euclideanBall d R) v)
      atTop (nhds 0)) :
    Tendsto
      (fun R : ℝ ↦ ENNReal.ofReal (R ^ (-(1 + theta))) *
        normalizedL2Norm (euclideanBall d R)
          (fun y ↦ v (matVecMul L y)))
      atTop (nhds 0) := by
  let q := affineBallFactor L
  let A : ℝ≥0∞ :=
    (ENNReal.ofReal (|L.det|⁻¹ * q ^ d)) ^ (1 / 2 : ℝ)
  let K : ℝ≥0∞ := ENNReal.ofReal (q ^ (1 + theta)) * A
  have hq : 0 < q := zero_lt_one.trans_le (one_le_affineBallFactor L)
  have hscale : Tendsto (fun R : ℝ ↦ q * R) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hq).2 tendsto_id
  have hsource := hgrowth.comp hscale
  have hKtop : K ≠ ⊤ := by
    dsimp only [K, A]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have hright := ENNReal.Tendsto.const_mul hsource (Or.inr hKtop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (by simpa only [mul_zero] using hright)
  · filter_upwards with R
    exact bot_le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hnorm := normalizedL2Norm_affinePullback_ball_le hL hR v
    have hpow := rpow_scaled_negative hq hR theta
    rw [hpow, ENNReal.ofReal_mul (Real.rpow_nonneg hq.le _)]
    dsimp only [K, A, q]
    calc
      ENNReal.ofReal (q ^ (1 + theta)) *
          ENNReal.ofReal ((q * R) ^ (-(1 + theta))) *
          normalizedL2Norm (euclideanBall d R)
            (fun y ↦ v (matVecMul L y)) ≤
        ENNReal.ofReal (q ^ (1 + theta)) *
          ENNReal.ofReal ((q * R) ^ (-(1 + theta))) *
          ((ENNReal.ofReal (|L.det|⁻¹ * q ^ d)) ^ (1 / 2 : ℝ) *
            normalizedL2Norm (euclideanBall d (q * R)) v) := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_left
            (mul_le_mul_left hnorm
              (ENNReal.ofReal ((q * R) ^ (-(1 + theta)))))
            (ENNReal.ofReal (q ^ (1 + theta))))
      _ = (ENNReal.ofReal (q ^ (1 + theta)) *
          (ENNReal.ofReal (|L.det|⁻¹ * q ^ d)) ^ (1 / 2 : ℝ)) *
            (ENNReal.ofReal ((q * R) ^ (-(1 + theta))) *
              normalizedL2Norm (euclideanBall d (q * R)) v) := by ac_rfl

end

end Root
end HighContrast
end HCPolySupport
