/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.AdaptedMaximalCells
public import LeanPool.HighContrastHomogenization.Entry.Geometry.QuadraticForm
public import LeanPool.HighContrastHomogenization.Setup.SourceObjects
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# High-contrast homogenization: Entry.Geometry.AffineGridDistortion

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Relative distortion of two adapted grids

For two invertible adapted grids with `gridRatio q q' ≤ K₀`, the relative matrices `q⁻¹*q'`
and `q'⁻¹*q` have operator norm at most `K₀`; this yields two-sided determinant and adapted-cell
volume comparison, a relative inverse-norm bound used for the flat-face strips, and exact
cancellation of the affine Jacobian in ratios, with no absolute norm bound on either grid.
These are the relative cell-volume and inverse-norm estimates behind `l.two.grid.whitney` and
the relative operator-norm control in the fixed old-coordinate enlargement of
`p.two.grid.transport`.
-/

open HCPolySupport.HighContrast (gridRatio)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate centeredCube standardCell)
namespace HCPolySupport.HighContrast.Geometry

open MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

theorem norm_inv_mul_le_gridRatio_of_le {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d)
    (hK : gridRatio q q' ≤ K₀) :
    ‖q⁻¹ * q'‖ ≤ K₀ := by
  let base : ℝ := 1 + ‖q⁻¹ * q'‖ + ‖q'⁻¹ * q‖
  have hbase : 1 ≤ base := by
    dsimp [base]
    linarith only [norm_nonneg (q⁻¹ * q'), norm_nonneg (q'⁻¹ * q)]
  have hexp : (2 * d) ≠ 0 := by omega
  have hpow : base ≤ base ^ (2 * d) := le_self_pow₀ hbase hexp
  have hnorm : ‖q⁻¹ * q'‖ ≤ base := by
    dsimp [base]
    linarith only [norm_nonneg (q'⁻¹ * q)]
  exact hnorm.trans (hpow.trans (by simpa [gridRatio, base] using hK))

theorem norm_inv_mul_comm_le_gridRatio_of_le {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d)
    (hK : gridRatio q q' ≤ K₀) :
    ‖q'⁻¹ * q‖ ≤ K₀ := by
  let base : ℝ := 1 + ‖q⁻¹ * q'‖ + ‖q'⁻¹ * q‖
  have hbase : 1 ≤ base := by
    dsimp [base]
    linarith only [norm_nonneg (q⁻¹ * q'), norm_nonneg (q'⁻¹ * q)]
  have hexp : (2 * d) ≠ 0 := by omega
  have hpow : base ≤ base ^ (2 * d) := le_self_pow₀ hbase hexp
  have hnorm : ‖q'⁻¹ * q‖ ≤ base := by
    dsimp [base]
    linarith only [norm_nonneg (q⁻¹ * q')]
  exact hnorm.trans (hpow.trans (by simpa [gridRatio, base] using hK))

theorem vecNormSq_relative_comm_le_gridRatio {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d)
    (hK : gridRatio q q' ≤ K₀) (v : Vec d) :
    vecNormSq (Matrix.mulVec (q'⁻¹ * q) v) ≤ K₀ ^ 2 * vecNormSq v := by
  have hn := norm_inv_mul_comm_le_gridRatio_of_le hd hK
  have hsq : ‖q'⁻¹ * q‖ ^ 2 ≤ K₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  calc
    vecNormSq (Matrix.mulVec (q'⁻¹ * q) v) ≤ ‖q'⁻¹ * q‖ ^ 2 * vecNormSq v :=
      vecNormSq_mulVec_le_opNorm (q'⁻¹ * q) v
    _ ≤ K₀ ^ 2 * vecNormSq v := by
      exact mul_le_mul_of_nonneg_right hsq (vecNormSq_nonneg v)

theorem abs_entry_le_opNorm (A : Mat d) (i j : Fin d) :
    |A i j| ≤ ‖A‖ := by
  let e : Vec d := Pi.single j (1 : ℝ)
  have hcoord : (A i j) ^ 2 ≤ vecNormSq (Matrix.mulVec A e) := by
    rw [vecNormSq_eq_sum_sq]
    have hsingle :=
      Finset.single_le_sum
        (fun k _ => sq_nonneg ((Matrix.mulVec A e) k)) (Finset.mem_univ i)
    simpa [e, Matrix.mulVec, dotProduct, Pi.single_apply] using hsingle
  have hop := vecNormSq_mulVec_le_opNorm A e
  have he : vecNormSq e = 1 := by
    rw [vecNormSq_eq_sum_sq]
    simp [e, Pi.single_apply]
  have hsq : (A i j) ^ 2 ≤ ‖A‖ ^ 2 := by
    calc
      (A i j) ^ 2 ≤ vecNormSq (Matrix.mulVec A e) := hcoord
      _ ≤ ‖A‖ ^ 2 * vecNormSq e := hop
      _ = ‖A‖ ^ 2 := by rw [he, mul_one]
  exact abs_le_of_sq_le_sq hsq (norm_nonneg _)

theorem abs_det_le_factorial_mul_opNorm_pow (A : Mat d) :
    |A.det| ≤ (Nat.factorial d : ℝ) * ‖A‖ ^ d := by
  have h := Matrix.det_le (abv := AbsoluteValue.abs) (A := A) (x := ‖A‖)
    (abs_entry_le_opNorm A)
  simpa [Fintype.card_fin, nsmul_eq_mul] using h

theorem abs_det_inv_mul_le_gridRatio_of_le {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d)
    (hK : gridRatio q q' ≤ K₀) :
    |(q⁻¹ * q').det| ≤ (Nat.factorial d : ℝ) * K₀ ^ d := by
  have hn := norm_inv_mul_le_gridRatio_of_le hd hK
  calc
    |(q⁻¹ * q').det| ≤ (Nat.factorial d : ℝ) * ‖q⁻¹ * q'‖ ^ d :=
      abs_det_le_factorial_mul_opNorm_pow (q⁻¹ * q')
    _ ≤ (Nat.factorial d : ℝ) * K₀ ^ d := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn d)
        (Nat.cast_nonneg _)

theorem abs_det_inv_mul_comm_le_gridRatio_of_le {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d)
    (hK : gridRatio q q' ≤ K₀) :
    |(q'⁻¹ * q).det| ≤ (Nat.factorial d : ℝ) * K₀ ^ d := by
  have hn := norm_inv_mul_comm_le_gridRatio_of_le hd hK
  calc
    |(q'⁻¹ * q).det| ≤ (Nat.factorial d : ℝ) * ‖q'⁻¹ * q‖ ^ d :=
      abs_det_le_factorial_mul_opNorm_pow (q'⁻¹ * q)
    _ ≤ (Nat.factorial d : ℝ) * K₀ ^ d := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn d)
        (Nat.cast_nonneg _)

theorem abs_det_div_eq_abs_det_inv_mul_left {q q' : Mat d} (hq : IsUnit q) :
    |q'.det| / |q.det| = |(q⁻¹ * q').det| := by
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq
  calc
    |q'.det| / |q.det| = |q.det|⁻¹ * |q'.det| := by rw [div_eq_inv_mul]
    _ = |q⁻¹.det| * |q'.det| := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, abs_inv]
    _ = |(q⁻¹ * q').det| := by
      rw [Matrix.det_mul, abs_mul]

theorem abs_det_div_eq_abs_det_inv_mul_right {q q' : Mat d} (hq' : IsUnit q') :
    |q.det| / |q'.det| = |(q'⁻¹ * q).det| := by
  have hdet : IsUnit q'.det := (Matrix.isUnit_iff_isUnit_det q').mp hq'
  calc
    |q.det| / |q'.det| = |q'.det|⁻¹ * |q.det| := by rw [div_eq_inv_mul]
    _ = |q'⁻¹.det| * |q.det| := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, abs_inv]
    _ = |(q'⁻¹ * q).det| := by
      rw [Matrix.det_mul, abs_mul]

theorem abs_det_ratio_le_gridRatio_of_le_left {q q' : Mat d} {K₀ : ℝ}
    (hd : 2 ≤ d) (hq : IsUnit q) (hK : gridRatio q q' ≤ K₀) :
    |q'.det| / |q.det| ≤ (Nat.factorial d : ℝ) * K₀ ^ d := by
  rw [abs_det_div_eq_abs_det_inv_mul_left hq]
  exact abs_det_inv_mul_le_gridRatio_of_le hd hK

theorem abs_det_ratio_le_gridRatio_of_le_right {q q' : Mat d} {K₀ : ℝ}
    (hd : 2 ≤ d) (hq' : IsUnit q') (hK : gridRatio q q' ≤ K₀) :
    |q.det| / |q'.det| ≤ (Nat.factorial d : ℝ) * K₀ ^ d := by
  rw [abs_det_div_eq_abs_det_inv_mul_right hq']
  exact abs_det_inv_mul_comm_le_gridRatio_of_le hd hK

theorem volume_adaptedCell (q : Mat d) (r : ℤ) :
    volume (adaptedCell q r)
      = ENNReal.ofReal |q.det| * ENNReal.ofReal ((3 : ℝ) ^ r) ^ d := by
  unfold adaptedCell
  have h :
      matVecMul q '' centeredCube d r =
        (fun v : Vec d => (0 : Vec d) + matVecMul q v) '' centeredCube d r := by
    ext x
    simp
  rw [h, Transport.volume_image_affine, volume_centeredCube]

theorem volume_adaptedCell_toReal (q : Mat d) (r : ℤ) :
    (volume (adaptedCell q r)).toReal =
      |q.det| * ((3 : ℝ) ^ r) ^ d := by
  rw [volume_adaptedCell]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal]
  positivity

theorem volume_adaptedCellTranslate_toReal (q : Mat d) (j : ℤ) (y : Vec d) :
    (volume (adaptedCellTranslate q j y)).toReal =
      |q.det| * ((3 : ℝ) ^ j) ^ d := by
  rw [volume_adaptedCellTranslate]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal]
  positivity

theorem triadic_volume_scale_ratio (d : ℕ) (j r : ℤ) :
    ((3 : ℝ) ^ r) ^ d / ((3 : ℝ) ^ j) ^ d =
      (3 : ℝ) ^ (-(d : ℝ) * ((j : ℝ) - (r : ℝ))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [← Real.rpow_intCast (3 : ℝ) r, ← Real.rpow_intCast (3 : ℝ) j]
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (r : ℝ)) d,
    ← Real.rpow_natCast ((3 : ℝ) ^ (j : ℝ)) d]
  rw [← Real.rpow_mul h3.le (r : ℝ) (d : ℝ),
    ← Real.rpow_mul h3.le (j : ℝ) (d : ℝ)]
  rw [← Real.rpow_sub h3 ((r : ℝ) * (d : ℝ)) ((j : ℝ) * (d : ℝ))]
  congr 1
  ring

theorem adaptedCell_volume_ratio_eq
    {q q' : Mat d} (hq' : IsUnit q') (j r : ℤ) (y : Vec d) :
    (volume (adaptedCell q r)).toReal /
        (volume (adaptedCellTranslate q' j y)).toReal =
      (|q.det| / |q'.det|) *
        (3 : ℝ) ^ (-(d : ℝ) * ((j : ℝ) - (r : ℝ))) := by
  have hq'det : q'.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det q').mp hq')
  have h3j : ((3 : ℝ) ^ j) ^ d ≠ 0 := by positivity
  rw [volume_adaptedCell_toReal, volume_adaptedCellTranslate_toReal,
    ← triadic_volume_scale_ratio d j r]
  field_simp [abs_ne_zero.mpr hq'det, h3j]

theorem adaptedCell_volume_ratio_two_sided_of_gridRatio
    {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d) (hK₀ : 1 ≤ K₀)
    (hq : IsUnit q) (hq' : IsUnit q') (hK : gridRatio q q' ≤ K₀)
    (j r : ℤ) (y : Vec d) :
    let Cdet : ℝ := (Nat.factorial d : ℝ) * K₀ ^ d
    (Cdet)⁻¹ * (3 : ℝ) ^ (-(d : ℝ) * ((j : ℝ) - (r : ℝ))) ≤
        (volume (adaptedCell q r)).toReal /
          (volume (adaptedCellTranslate q' j y)).toReal ∧
      (volume (adaptedCell q r)).toReal /
          (volume (adaptedCellTranslate q' j y)).toReal ≤
        Cdet * (3 : ℝ) ^ (-(d : ℝ) * ((j : ℝ) - (r : ℝ))) := by
  dsimp
  let Cdet : ℝ := (Nat.factorial d : ℝ) * K₀ ^ d
  let scale : ℝ := (3 : ℝ) ^ (-(d : ℝ) * ((j : ℝ) - (r : ℝ)))
  have hCpos : 0 < Cdet := by
    dsimp [Cdet]
    positivity
  have hscalepos : 0 < scale := by
    dsimp [scale]
    positivity
  have hratio :
      (volume (adaptedCell q r)).toReal /
          (volume (adaptedCellTranslate q' j y)).toReal =
        (|q.det| / |q'.det|) * scale := by
    rw [adaptedCell_volume_ratio_eq hq' j r y]
  have hdetUpper : |q.det| / |q'.det| ≤ Cdet := by
    dsimp [Cdet]
    exact abs_det_ratio_le_gridRatio_of_le_right hd hq' hK
  have hdetLower : Cdet⁻¹ ≤ |q.det| / |q'.det| := by
    have hleft : |q'.det| / |q.det| ≤ Cdet := by
      dsimp [Cdet]
      exact abs_det_ratio_le_gridRatio_of_le_left hd hq hK
    have hqdetpos : 0 < |q.det| := by
      exact abs_pos.mpr (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det q).mp hq))
    have hq'detpos : 0 < |q'.det| := by
      exact abs_pos.mpr (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det q').mp hq'))
    rw [inv_le_iff_one_le_mul₀ hCpos]
    rw [div_eq_mul_inv]
    field_simp [ne_of_gt hqdetpos, ne_of_gt hq'detpos] at hleft ⊢
    linarith only [hleft]
  constructor
  · rw [hratio]
    exact mul_le_mul_of_nonneg_right hdetLower hscalepos.le
  · rw [hratio]
    exact mul_le_mul_of_nonneg_right hdetUpper hscalepos.le

/-- Relative inverse control in the squared Euclidean norm used by the strip theorem. -/
theorem inverseNormLE_relative_of_gridRatio {q q' : Mat d} {K₀ : ℝ}
    (hd : 2 ≤ d) (hq : IsUnit q) (hq' : IsUnit q')
    (hK : gridRatio q q' ≤ K₀) : InverseNormLE (q⁻¹ * q') K₀ := by
  intro v
  have hcancel : (q'⁻¹ * q) * (q⁻¹ * q') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc q q⁻¹ q',
      Matrix.mul_nonsing_inv q ((Matrix.isUnit_iff_isUnit_det q).mp hq),
      Matrix.one_mul,
      Matrix.nonsing_inv_mul q' ((Matrix.isUnit_iff_isUnit_det q').mp hq')]
  have hbound := vecNormSq_relative_comm_le_gridRatio hd hK
    (Matrix.mulVec (q⁻¹ * q') v)
  rw [Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec] at hbound
  exact hbound

/-- The Jacobian cancels in the relative volume of a cell and the affine target. -/
theorem adaptedCell_relVolume_eq_standard_preimage {q q' : Mat d}
    (hq : IsUnit q) (hq' : IsUnit q') (j r : ℤ) (y : Vec d) (w : Fin d → ℤ) :
    (volume (adaptedCell q r)).toReal / (volume (adaptedCellTranslate q' j y)).toReal =
      (volume (standardCell d r w)).toReal /
        (volume (adaptedCellTranslate (q⁻¹ * q') j (matVecMul q⁻¹ y))).toReal := by
  have hqdet : q.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det q).mp hq)
  have hq'det : q'.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det q').mp hq')
  rw [volume_adaptedCell_toReal, volume_adaptedCellTranslate_toReal,
    volume_adaptedCellTranslate_toReal, volume_standardCell,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 3 ^ r),
    Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, abs_mul, abs_inv]
  field_simp [abs_ne_zero.mpr hqdet, abs_ne_zero.mpr hq'det]

end HCPolySupport.HighContrast.Geometry
