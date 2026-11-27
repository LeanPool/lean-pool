/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CovarianceResolventPerturbation

/-!
# Relative trace norm along an actual covariance segment

The positive segment V+tΔ has a genuine inverse square root. Its
normalized tangent is a matrix sandwich of the tangent normalized at V.
The exact Gram matrix of that transport is (I+tY)⁻¹, giving the uniform
factor 1/(1-‖Y‖) used when integrating the source purity differential.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_inverse_one_sub_le_of_bound {Z : Matrix ι ι ℝ} {δ : ℝ}
    (hZ : Z.IsHermitian) (hδ : δ < 1) (hbound : ‖Z‖ ≤ δ) :
    ‖(1 - Z)⁻¹‖ ≤ (1 - δ)⁻¹ := by
  have hz : ‖Z‖ < 1 := hbound.trans_lt hδ
  have hc : ContinuousOn (fun x : ℝ => 1 - x) (spectrum ℝ Z) :=
    continuousOn_const.sub continuousOn_id
  have hn : ∀ x ∈ spectrum ℝ Z, 1 - x ≠ 0 :=
    fun x hx => (spectrum_one_sub_pos hZ hz hx).ne'
  have he : (1 - Z)⁻¹ = cfc (fun x : ℝ => (1 - x)⁻¹) Z := by
    symm
    rw [cfc_inv _ Z hn hc hZ.isSelfAdjoint, matrix_one_sub_cfc hZ,
      ← Matrix.nonsing_inv_eq_ringInverse]
  rw [he]
  apply norm_cfc_le (inv_nonneg.mpr (sub_pos.mpr hδ).le)
  intro x hx
  have hb : |x| ≤ δ := by
    have h := IsometricContinuousFunctionalCalculus.norm_spectrum_le Z hx hZ.isSelfAdjoint
    have hxnorm : |x| ≤ ‖Z‖ := by simpa only [Real.norm_eq_abs] using h
    exact hxnorm.trans hbound
  have hp : 0 < 1 - x := spectrum_one_sub_pos hZ hz hx
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos hp]
  simpa only [one_div] using one_div_le_one_div_of_le (sub_pos.mpr hδ)
    (show 1 - δ ≤ 1 - x by linarith [le_abs_self x])

/-- Covariance segment given by `V + t • Δ`. -/
def covarianceSegment (V Δ : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ := V + t • Δ

/-- Covariance segment transport given by `(CFC.sqrt (covarianceSegment V Δ t))⁻¹ * CFC.sqrt V`. -/
def covarianceSegmentTransport (V Δ : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  (CFC.sqrt (covarianceSegment V Δ t))⁻¹ * CFC.sqrt V

theorem covarianceSegment_factorization {V : Matrix ι ι ℝ} (hV : V.PosDef)
    (Δ : Matrix ι ι ℝ) (t : ℝ) :
    covarianceSegment V Δ t = CFC.sqrt V *
      (1 + t • relativeCovariancePerturbation V Δ) * CFC.sqrt V := by
  have h := covariance_gap_factorization hV (-(t • Δ))
  simpa only [covarianceSegment, sub_neg_eq_add, relativeCovariancePerturbation,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul] using h

theorem covarianceSegment_posDef {V Δ : Matrix ι ι ℝ}
    (hV : V.PosDef) (hΔ : Δ.IsHermitian) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hδ : ‖relativeCovariancePerturbation V Δ‖ < 1) :
    (covarianceSegment V Δ t).PosDef := by
  have hscale : ‖relativeCovariancePerturbation V (-(t • Δ))‖ ≤
      ‖relativeCovariancePerturbation V Δ‖ := by
    simp only [relativeCovariancePerturbation, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_smul, Matrix.smul_mul, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht₀]
    exact mul_le_of_le_one_left (norm_nonneg _) ht₁
  have h := covariance_gap_posDef_of_relative_norm hV
    ((hΔ.smul (IsSelfAdjoint.all t)).neg) (hscale.trans_lt hδ)
  simpa only [sub_neg_eq_add, covarianceSegment] using h

theorem covarianceSegmentTransport_gram {V Δ : Matrix ι ι ℝ} (hV : V.PosDef)
    {t : ℝ} (hW : (covarianceSegment V Δ t).PosDef) :
    (covarianceSegmentTransport V Δ t)ᵀ * covarianceSegmentTransport V Δ t =
      (1 + t • relativeCovariancePerturbation V Δ)⁻¹ := by
  let R := CFC.sqrt V
  let Q := CFC.sqrt (covarianceSegment V Δ t)
  have hR := matrix_sqrt_posDef hV
  have hQ := matrix_sqrt_posDef hW
  have hRt : Rᵀ = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  have hQit : (Q⁻¹)ᵀ = Q⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.inv.isHermitian.eq
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have hRiR : R⁻¹ * R = 1 := R.nonsing_inv_mul hRdet
  have hRRi : R * R⁻¹ = 1 := R.mul_nonsing_inv hRdet
  have hWi : (covarianceSegment V Δ t)⁻¹ = Q⁻¹ * Q⁻¹ := by
    rw [← CFC.sqrt_mul_sqrt_self (covarianceSegment V Δ t) hW.posSemidef.nonneg,
      Matrix.mul_inv_rev]
  change (Q⁻¹ * R)ᵀ * (Q⁻¹ * R) = _
  rw [Matrix.transpose_mul, hRt, hQit]
  calc
    _ = R * (Q⁻¹ * Q⁻¹) * R := by noncomm_ring
    _ = R * (covarianceSegment V Δ t)⁻¹ * R := by rw [hWi]
    _ = (R * R⁻¹) * (1 + t • relativeCovariancePerturbation V Δ)⁻¹ * (R⁻¹ * R) := by
      rw [covarianceSegment_factorization hV Δ t, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
      change R * (R⁻¹ * ((1 + t • relativeCovariancePerturbation V Δ)⁻¹ * R⁻¹)) * R = _
      noncomm_ring
    _ = _ := by rw [hRRi, hRiR, Matrix.one_mul, Matrix.mul_one]

theorem relativeCovariancePerturbation_segment_transport
    {V Δ : Matrix ι ι ℝ} (hV : V.PosDef) {t : ℝ}
    (hW : (covarianceSegment V Δ t).PosDef) :
    relativeCovariancePerturbation (covarianceSegment V Δ t) Δ =
      covarianceSegmentTransport V Δ t * relativeCovariancePerturbation V Δ *
        (covarianceSegmentTransport V Δ t)ᵀ := by
  let R := CFC.sqrt V
  let Q := CFC.sqrt (covarianceSegment V Δ t)
  have hR := matrix_sqrt_posDef hV
  have hQ := matrix_sqrt_posDef hW
  have hRt : Rᵀ = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  have hQit : (Q⁻¹)ᵀ = Q⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.inv.isHermitian.eq
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have hRiR : R⁻¹ * R = 1 := R.nonsing_inv_mul hRdet
  have hRRi : R * R⁻¹ = 1 := R.mul_nonsing_inv hRdet
  change Q⁻¹ * Δ * Q⁻¹ = (Q⁻¹ * R) * (R⁻¹ * Δ * R⁻¹) * (Q⁻¹ * R)ᵀ
  rw [Matrix.transpose_mul, hRt, hQit]
  calc
    _ = Q⁻¹ * (R * R⁻¹) * Δ * (R⁻¹ * R) * Q⁻¹ := by
      rw [hRRi, hRiR, Matrix.mul_one, Matrix.mul_one]
    _ = _ := by noncomm_ring

theorem norm_sq_covarianceSegmentTransport_le {V Δ : Matrix ι ι ℝ}
    (hV : V.PosDef) (hΔ : Δ.IsHermitian) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hδ : ‖relativeCovariancePerturbation V Δ‖ < 1) :
    ‖covarianceSegmentTransport V Δ t‖ ^ 2 ≤
      (1 - ‖relativeCovariancePerturbation V Δ‖)⁻¹ := by
  have hW := covarianceSegment_posDef hV hΔ ht₀ ht₁ hδ
  rw [pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self,
    Matrix.conjTranspose_eq_transpose_of_trivial, covarianceSegmentTransport_gram hV hW]
  have hZ := ((relativeCovariancePerturbation_isHermitian hV hΔ).smul
    (IsSelfAdjoint.all t)).neg
  have hn : ‖-(t • relativeCovariancePerturbation V Δ)‖ ≤
      ‖relativeCovariancePerturbation V Δ‖ := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht₀]
    exact mul_le_of_le_one_left (norm_nonneg _) ht₁
  simpa only [sub_neg_eq_add] using norm_inverse_one_sub_le_of_bound hZ hδ hn

/-- Uniform bound on the actual normalized tangent along the full segment. -/
theorem matrixTraceNorm_relativeCovariancePerturbation_segment_le
    {V Δ : Matrix ι ι ℝ} (hV : V.PosDef) (hΔ : Δ.IsHermitian)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hδ : ‖relativeCovariancePerturbation V Δ‖ < 1) :
    matrixTraceNorm (relativeCovariancePerturbation (covarianceSegment V Δ t) Δ) ≤
      (1 - ‖relativeCovariancePerturbation V Δ‖)⁻¹ *
        matrixTraceNorm (relativeCovariancePerturbation V Δ) := by
  rw [relativeCovariancePerturbation_segment_transport hV
    (covarianceSegment_posDef hV hΔ ht₀ ht₁ hδ)]
  exact (matrixTraceNorm_sandwich_le (relativeCovariancePerturbation_isHermitian hV hΔ)
    (covarianceSegmentTransport V Δ t)).trans
      (mul_le_mul_of_nonneg_right (norm_sq_covarianceSegmentTransport_le hV hΔ ht₀ ht₁ hδ)
        (matrixTraceNorm_nonneg _))

end VacuumBellSeparation.Gaussian
