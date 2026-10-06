/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.RoundedGridBasic
public import LeanPool.HighContrastHomogenization.Entry.Geometry.GeometryUpdateBounds
public import LeanPool.HighContrastHomogenization.Support.Ambient.MatrixOrderBridge
public import LeanPool.HighContrastHomogenization.Setup.SourceObjects

/-!
# High-contrast homogenization: Entry.Geometry.RoundedGridComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Rounded-grid comparison for bounded projective hops

This module contains the supporting geometric estimates for the rounded-grid comparison
used in `l.projective.step` (near `e.rounded.grid.bounds`, `s.geometry.transport`,
`l.projective.step`).
The standing source-scale condition near `e.source.lower.scale` belongs to the
main statement, not to these geometric estimates.
-/

open HCPolySupport.HighContrast (gridRatio matSqrt specBound)
namespace HCPolySupport.HighContrast.Geometry

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The exact standing threshold `2*d ≤ 3^jStar` gives the printed half-size
operator-norm rounding error. -/
theorem opNorm_roundingError_le_half
    {d : ℕ} (jStar : ℕ) (m : Mat d) (hj : 2 * d ≤ 3 ^ jStar) :
    ‖explicitRoundedGrid jStar m - unroundedGrid m‖ ≤ (1 / 2 : ℝ) :=
  (opNorm_roundingError_le jStar m).trans (mul_inv_pow_le_half hj)

/-- The unrounded grid `|m⁻¹|^{1/2} m^{1/2}` is positive definite on positive
matrices. -/
theorem unroundedGrid_posDef
    {d : ℕ} [NeZero d] {m : Mat d} (hm : m.PosDef) :
    (unroundedGrid m).PosDef := by
  have hnorm : 0 < ‖m⁻¹‖ := by
    rw [posDef_inv_l2_opNorm_eq_specMin_inv hm]
    exact inv_pos.mpr (specMin_pos hm)
  exact (posDef_sqrt hm).smul (Real.sqrt_pos.mpr hnorm)

/-- The squared norm of the noncommuting cross root is the upper relative
spectral threshold: multiply by the adjoint, preserving every factor's order. -/
theorem opNorm_matSqrt_inv_mul_sqrt_sq
    {d : ℕ} [NeZero d] {m m' : Mat d} (hm : m.PosDef) (hm' : m'.PosDef) :
    ‖matSqrt m⁻¹ * CFC.sqrt m'‖ ^ 2 = specBound (normalizedMat m m') := by
  have hS : star (matSqrt m⁻¹) = matSqrt m⁻¹ := (matSqrt_inv_posDef hm).isHermitian
  have hT : star (CFC.sqrt m') = CFC.sqrt m' := (posDef_sqrt hm').isHermitian
  rw [sq, ← CStarRing.norm_self_mul_star, StarMul.star_mul, hS, hT]
  have hprod : matSqrt m⁻¹ * CFC.sqrt m' * (CFC.sqrt m' * matSqrt m⁻¹) =
      normalizedMat m m' := by
    rw [normalizedMat, mul_assoc (matSqrt m⁻¹), ← mul_assoc (CFC.sqrt m'),
      sqrt_mul_sqrt hm', ← mul_assoc]
  rw [hprod, posDef_l2_opNorm_eq_specBound (normalizedMat_posDef hm hm')]

/-- Loewner comparison of a positive semidefinite real matrix controls its
Euclidean operator norm. -/
theorem opNorm_le_opNorm_of_matLoewnerLE
    {d : ℕ} {A B : Mat d} (hA : A.PosSemidef) (hAB : MatLoewnerLE A B) :
    ‖A‖ ≤ ‖B‖ := by
  apply opNorm_le_of_vecNormSq_mulVec_le (norm_nonneg B)
  apply vecNormSq_mulVec_le_of_dotProduct_le
    (transpose_eq_of_isHermitian hA.isHermitian)
    (dotProduct_mulVec_nonneg_of_posSemidef hA) (norm_nonneg B)
  intro v
  have hv : v ⬝ᵥ (A *ᵥ v) ≤ v ⬝ᵥ (B *ᵥ v) := by
    have h := hAB v
    change (1 / 2 : ℝ) * (v ⬝ᵥ (A *ᵥ v)) ≤ (1 / 2 : ℝ) * (v ⬝ᵥ (B *ᵥ v)) at h
    linarith only [h]
  exact hv.trans (dotProduct_mulVec_le_opNorm B v)

/-- Inverse order controls the scalar normalization ratio of the unrounded grids. -/
theorem opNorm_inv_le_of_relative_lower
    {d : ℕ} {m m' : Mat d} (hm : m.PosDef) (hm' : m'.PosDef)
    {L : ℝ} (hL : 0 < L) (hlow : MatLoewnerLE (L • m) m') :
    ‖m'⁻¹‖ ≤ L⁻¹ * ‖m⁻¹‖ := by
  have hinv := HCPolySupport.matLoewnerLE_inv_of_posDef (hm.smul hL) hm' hlow
  have hnorm := opNorm_le_opNorm_of_matLoewnerLE hm'.inv.posSemidef hinv
  rwa [HCPolySupport.nonsing_inv_smul L hL.ne'
      ((Matrix.isUnit_iff_isUnit_det m).mp hm.isUnit),
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)] at hnorm

/-- The inverse of the positive CFC square root is the matrix square root of
the inverse. This identity involves a single matrix. -/
theorem inv_sqrt_eq_matSqrt_inv
    {d : ℕ} {m : Mat d} (hm : m.PosDef) : (CFC.sqrt m)⁻¹ = matSqrt m⁻¹ := by
  rw [matSqrt_eq_cfc_sqrt hm.inv.posSemidef, eq_comm,
    CFC.sqrt_eq_iff _ _ hm.inv.posSemidef.nonneg
      (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg m)).inv.nonneg,
    ← sq, Matrix.inv_pow', CFC.sq_sqrt m]

/-- The unrounded cross map is controlled by the projective distance, without
any commutativity assumption on the two positive matrices. -/
theorem opNorm_unroundedGrid_cross_le
    {d : ℕ} [NeZero d] {m m' : Mat d} (hm : m.PosDef) (hm' : m'.PosDef) :
    ‖(unroundedGrid m)⁻¹ * unroundedGrid m'‖ ≤ Real.exp (projectiveDistance m m') := by
  obtain ⟨L, U, hL, hLU, hlow, _hupp, _hLdef, hUdef, hdist⟩ :=
    projectiveDistance_eq_log_relative_spread hm hm'
  have hU : 0 < U := hL.trans_le hLU
  have hn : 0 < ‖m⁻¹‖ := by
    rw [posDef_inv_l2_opNorm_eq_specMin_inv hm]
    exact inv_pos.mpr (specMin_pos hm)
  have hratio : ‖m'⁻¹‖ / ‖m⁻¹‖ ≤ L⁻¹ := by
    exact (div_le_iff₀ hn).2 (opNorm_inv_le_of_relative_lower hm hm' hL ((hlow L).2 le_rfl))
  have hsquare : ‖(unroundedGrid m)⁻¹ * unroundedGrid m'‖ ^ 2 =
      (‖m'⁻¹‖ / ‖m⁻¹‖) * U := by
    rw [unroundedGrid, unroundedGrid,
      HCPolySupport.nonsing_inv_smul (Real.sqrt ‖m⁻¹‖) (Real.sqrt_pos.mpr hn).ne'
        ((Matrix.isUnit_iff_isUnit_det _).mp (posDef_sqrt hm).isUnit),
      inv_sqrt_eq_matSqrt_inv hm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)),
      mul_pow, mul_pow, inv_pow, Real.sq_sqrt (norm_nonneg _),
      Real.sq_sqrt (norm_nonneg _), opNorm_matSqrt_inv_mul_sqrt_sq hm hm', ← hUdef]
    ring
  have hbound : ‖(unroundedGrid m)⁻¹ * unroundedGrid m'‖ ^ 2 ≤ U / L := by
    rw [hsquare]
    calc (‖m'⁻¹‖ / ‖m⁻¹‖) * U ≤ L⁻¹ * U :=
        mul_le_mul_of_nonneg_right hratio hU.le
      _ = U / L := by rw [div_eq_mul_inv, mul_comm]
  calc ‖(unroundedGrid m)⁻¹ * unroundedGrid m'‖ =
        Real.sqrt (‖(unroundedGrid m)⁻¹ * unroundedGrid m'‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (U / L) := Real.sqrt_le_sqrt hbound
    _ = Real.exp (projectiveDistance m m') := by
      rw [hdist, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (div_pos hU hL), mul_comm]

/-- Reversing a positive pair reverses the relative comparison constants, so
the projective distance cannot increase. -/
theorem projectiveDistance_reverse_le
    {d : ℕ} [NeZero d] {m m' : Mat d} (hm : m.PosDef) (hm' : m'.PosDef) :
    projectiveDistance m' m ≤ projectiveDistance m m' := by
  have hscale {A B : Mat d} {c : ℝ} (hc : 0 ≤ c) (h : MatLoewnerLE A B) :
      MatLoewnerLE (c • A) (c • B) := by
    intro v
    have hv := mul_le_mul_of_nonneg_left (h v) hc
    change (1 / 2 : ℝ) * vecDot v (matVecMul (c • A) v) ≤
      (1 / 2 : ℝ) * vecDot v (matVecMul (c • B) v)
    rw [smul_matVecMul, smul_matVecMul, vecDot_smul_right, vecDot_smul_right]
    linarith only [hv]
  obtain ⟨L, U, hL, hLU, hlow, hupp, _hLdef, _hUdef, hdist⟩ :=
    projectiveDistance_eq_log_relative_spread hm hm'
  obtain ⟨L', U', hL', hLU', hlow', hupp', _hLdef', _hUdef', hdist'⟩ :=
    projectiveDistance_eq_log_relative_spread hm' hm
  have hU : 0 < U := hL.trans_le hLU
  have hU' : 0 < U' := hL'.trans_le hLU'
  have hupper : U' ≤ L⁻¹ := by
    apply (hupp' _).1
    have h := hscale (inv_pos.mpr hL).le ((hlow L).2 le_rfl)
    simpa only [smul_smul, inv_mul_cancel₀ hL.ne', one_smul] using h
  have hlower : U⁻¹ ≤ L' := by
    apply (hlow' _).1
    have h := hscale (inv_pos.mpr hU).le ((hupp U).2 le_rfl)
    simpa only [smul_smul, inv_mul_cancel₀ hU.ne', one_smul] using h
  have hratio : U' / L' ≤ U / L := by
    calc U' / L' ≤ L⁻¹ / U⁻¹ := by gcongr
      _ = U / L := by rw [inv_div_inv, div_eq_mul_inv]
  rw [hdist, hdist']
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos hU' hL') hratio)
    (by norm_num)

/-- The projective distance is symmetric on positive matrices. -/
theorem projectiveDistance_symm
    {d : ℕ} [NeZero d] {m m' : Mat d} (hm : m.PosDef) (hm' : m'.PosDef) :
    projectiveDistance m m' = projectiveDistance m' m :=
  le_antisymm (projectiveDistance_reverse_le hm' hm) (projectiveDistance_reverse_le hm hm')

/-- The half-size rounding errors and the existing rounded inverse bound
transfer the unrounded cross comparison at the exact standing grid threshold. -/
theorem opNorm_roundedGrid_cross_le
    {d : ℕ} [NeZero d] (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar)
    {m m' : Mat d} (hm : m.PosDef) (hm' : m'.PosDef) :
    ‖(explicitRoundedGrid jStar m)⁻¹ * explicitRoundedGrid jStar m'‖ ≤
      2 * Real.exp (projectiveDistance m m') + 1 := by
  let A := unroundedGrid m
  let B := unroundedGrid m'
  let q := explicitRoundedGrid jStar m
  let q' := explicitRoundedGrid jStar m'
  have hq : ‖q⁻¹‖ ≤ 2 := opNorm_roundedGrid_inv_le hj hm
  have hE : ‖q - A‖ ≤ (1 / 2 : ℝ) := opNorm_roundingError_le_half jStar m hj
  have hE' : ‖q' - B‖ ≤ (1 / 2 : ℝ) := opNorm_roundingError_le_half jStar m' hj
  have hqinv : q⁻¹ * q = 1 := Matrix.nonsing_inv_mul q
    ((Matrix.isUnit_iff_isUnit_det q).mp (isUnit_roundedGrid hj hm))
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp (unroundedGrid_posDef hm).isUnit)
  have hqa : q⁻¹ * A = 1 - q⁻¹ * (q - A) := by rw [mul_sub, hqinv, sub_sub_cancel]
  have hqaBound : ‖q⁻¹ * A‖ ≤ 2 := by
    rw [hqa]
    calc ‖1 - q⁻¹ * (q - A)‖ ≤ ‖(1 : Mat d)‖ + ‖q⁻¹ * (q - A)‖ := norm_sub_le _ _
      _ ≤ 1 + 2 * (1 / 2 : ℝ) := by
        rw [norm_one]
        exact add_le_add le_rfl ((norm_mul_le _ _).trans
          (mul_le_mul hq hE (norm_nonneg _) (by norm_num)))
      _ = 2 := by norm_num
  have hfactor : q⁻¹ * q' = (q⁻¹ * A) * (A⁻¹ * B) + q⁻¹ * (q' - B) := by
    rw [mul_assoc q⁻¹ A, ← mul_assoc A A⁻¹ B, hAinv, one_mul, ← mul_add, add_sub_cancel]
  change ‖q⁻¹ * q'‖ ≤ _
  rw [hfactor]
  calc ‖q⁻¹ * A * (A⁻¹ * B) + q⁻¹ * (q' - B)‖ ≤
        ‖q⁻¹ * A * (A⁻¹ * B)‖ + ‖q⁻¹ * (q' - B)‖ := norm_add_le _ _
    _ ≤ (2 * Real.exp (projectiveDistance m m')) + 2 * (1 / 2 : ℝ) := by
      exact add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul hqaBound
          (opNorm_unroundedGrid_cross_le hm hm') (norm_nonneg _) (by norm_num)))
        ((norm_mul_le _ _).trans (mul_le_mul hq hE' (norm_nonneg _) (by norm_num)))
    _ = 2 * Real.exp (projectiveDistance m m') + 1 := by norm_num

/-- One positive constant depending only on the dimension controls both
orientations of every rounded hop of projective length at most one. -/
theorem gridRatio_roundedGrid_le_of_projectiveDistance_le
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
      ∀ (m m' : Mat d), m.PosDef → m'.PosDef →
        projectiveDistance m m' ≤ 1 →
          gridRatio (explicitRoundedGrid jStar m) (explicitRoundedGrid jStar m') ≤ C := by
  let : NeZero d := ⟨by omega⟩
  refine ⟨(3 + 4 * Real.exp 1) ^ (2 * d), by positivity, ?_⟩
  intro jStar hj m m' hm hm' hdist
  have hf := opNorm_roundedGrid_cross_le jStar hj hm hm'
  have hr := opNorm_roundedGrid_cross_le jStar hj hm' hm
  rw [projectiveDistance_symm hm' hm] at hr
  have he : Real.exp (projectiveDistance m m') ≤ Real.exp 1 := Real.exp_le_exp.mpr hdist
  unfold gridRatio
  apply pow_le_pow_left₀ (by positivity)
  calc 1 + ‖(explicitRoundedGrid jStar m)⁻¹ * explicitRoundedGrid jStar m'‖ +
        ‖(explicitRoundedGrid jStar m')⁻¹ * explicitRoundedGrid jStar m‖ ≤
        1 + (2 * Real.exp (projectiveDistance m m') + 1) +
          (2 * Real.exp (projectiveDistance m m') + 1) :=
      add_le_add (add_le_add le_rfl hf) hr
    _ ≤ 1 + (2 * Real.exp 1 + 1) + (2 * Real.exp 1 + 1) := by gcongr
    _ = 3 + 4 * Real.exp 1 := by ring

end

end HCPolySupport.HighContrast.Geometry
