/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixTraceNormSandwich

/-!
# Operator and trace-norm bounds for the actual covariance resolvent

For a symmetric matrix Z with ‖Z‖<1, the matrix I-Z is genuinely positive
definite. Its actual inverse satisfies the two estimates
‖(I-Z)⁻¹-I‖ ≤ ‖Z‖/(1-‖Z‖) and ‖(I-Z)⁻¹-I‖₁ ≤ ‖Z‖₁/(1-‖Z‖), which give the manuscript's
bounds (4.5). Finite spectral calculus proves both, including the empty
index case; no entrywise inverse or norm is used.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixTraceNorm_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    matrixTraceNorm (cfc f A) = ∑ i, |f (hA.eigenvalues i)| := by
  have hU : ((hA.eigenvectorUnitary : Matrix ι ι ℝ))ᵀ * hA.eigenvectorUnitary = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [matrixTraceNorm_orthogonal_conjugate _ hU, matrixTraceNorm_diagonal]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]

theorem real_resolvent_perturbation_bound {x δ : ℝ} (hδ : δ < 1) (hx : |x| ≤ δ) :
    |(1 - x)⁻¹ - 1| ≤ (1 - δ)⁻¹ * |x| := by
  have hx₁ : x < 1 := (le_abs_self x).trans_lt (hx.trans_lt hδ)
  have hden : 0 < 1 - x := sub_pos.mpr hx₁
  have hid : (1 - x)⁻¹ - 1 = x / (1 - x) := by
    field_simp [hden.ne']
    ring
  rw [hid, abs_div, abs_of_pos hden, ← div_eq_inv_mul]
  exact div_le_div_of_nonneg_left (abs_nonneg x) (sub_pos.mpr hδ)
    (by linarith [le_abs_self x])

/-- Matrix resolvent perturbation given by `(1 - Z)⁻¹ - 1`. -/
def matrixResolventPerturbation (Z : Matrix ι ι ℝ) : Matrix ι ι ℝ := (1 - Z)⁻¹ - 1

theorem spectrum_one_sub_pos {Z : Matrix ι ι ℝ} (hZ : Z.IsHermitian) (hδ : ‖Z‖ < 1)
    {x : ℝ} (hx : x ∈ spectrum ℝ Z) : 0 < 1 - x := by
  have hb : |x| ≤ ‖Z‖ := by
    simpa only [Real.norm_eq_abs] using
      IsometricContinuousFunctionalCalculus.norm_spectrum_le Z hx hZ.isSelfAdjoint
  linarith [le_abs_self x]

theorem matrix_one_sub_cfc {Z : Matrix ι ι ℝ} (hZ : Z.IsHermitian) :
    cfc (fun x : ℝ => 1 - x) Z = 1 - Z := by
  rw [cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => x) Z
    continuousOn_const continuousOn_id, cfc_const_one ℝ Z,
    cfc_id' ℝ Z hZ.isSelfAdjoint]

theorem matrix_one_sub_posDef_of_norm_lt_one
    {Z : Matrix ι ι ℝ} (hZ : Z.IsHermitian) (hδ : ‖Z‖ < 1) : (1 - Z).PosDef := by
  have hp : 0 ≤ 1 - Z := by
    rw [← matrix_one_sub_cfc hZ]
    exact cfc_nonneg (f := fun x : ℝ => 1 - x) (a := Z)
      fun x hx => (spectrum_one_sub_pos hZ hδ hx).le
  exact hp.posSemidef.posDef_iff_isUnit.mpr (isUnit_one_sub_of_norm_lt_one hδ)

theorem matrixResolventPerturbation_eq_cfc
    {Z : Matrix ι ι ℝ} (hZ : Z.IsHermitian) (hδ : ‖Z‖ < 1) :
    matrixResolventPerturbation Z = cfc (fun x : ℝ => (1 - x)⁻¹ - 1) Z := by
  have hc : ContinuousOn (fun x : ℝ => 1 - x) (spectrum ℝ Z) :=
    continuousOn_const.sub continuousOn_id
  have hn : ∀ x ∈ spectrum ℝ Z, 1 - x ≠ 0 :=
    fun x hx => (spectrum_one_sub_pos hZ hδ hx).ne'
  symm
  rw [cfc_sub (fun x : ℝ => (1 - x)⁻¹) (fun _ : ℝ => 1) Z
    (hc.inv₀ hn) continuousOn_const,
    cfc_inv (fun x : ℝ => 1 - x) Z hn hc hZ.isSelfAdjoint, cfc_const_one ℝ Z,
    matrix_one_sub_cfc hZ, ← Matrix.nonsing_inv_eq_ringInverse]
  rfl

theorem matrixResolventPerturbation_isHermitian
    {Z : Matrix ι ι ℝ} (hZ : Z.IsHermitian) : (matrixResolventPerturbation Z).IsHermitian :=
  (Matrix.isHermitian_one.sub hZ).inv.sub Matrix.isHermitian_one

theorem norm_matrixResolventPerturbation_le
    {Z : Matrix ι ι ℝ} (hZ : Z.IsHermitian) (hδ : ‖Z‖ < 1) :
    ‖matrixResolventPerturbation Z‖ ≤ ‖Z‖ / (1 - ‖Z‖) := by
  rw [matrixResolventPerturbation_eq_cfc hZ hδ]
  apply norm_cfc_le (div_nonneg (norm_nonneg _) (sub_pos.mpr hδ).le)
  intro x hx
  have hb : |x| ≤ ‖Z‖ := by
    simpa only [Real.norm_eq_abs] using
      IsometricContinuousFunctionalCalculus.norm_spectrum_le Z hx hZ.isSelfAdjoint
  rw [Real.norm_eq_abs, div_eq_inv_mul]
  exact (real_resolvent_perturbation_bound hδ hb).trans
    (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (sub_pos.mpr hδ).le))

theorem matrixTraceNorm_matrixResolventPerturbation_le
    {Z : Matrix ι ι ℝ} (hZ : Z.IsHermitian) (hδ : ‖Z‖ < 1) :
    matrixTraceNorm (matrixResolventPerturbation Z) ≤
      (1 - ‖Z‖)⁻¹ * matrixTraceNorm Z := by
  rw [matrixResolventPerturbation_eq_cfc hZ hδ, matrixTraceNorm_cfc hZ,
    matrixTraceNorm_eq_sum_abs_eigenvalues hZ, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply real_resolvent_perturbation_bound hδ
  simpa only [Real.norm_eq_abs] using
    IsometricContinuousFunctionalCalculus.norm_spectrum_le Z
      (hZ.eigenvalues_mem_spectrum_real i) hZ.isSelfAdjoint

end VacuumBellSeparation.Gaussian
