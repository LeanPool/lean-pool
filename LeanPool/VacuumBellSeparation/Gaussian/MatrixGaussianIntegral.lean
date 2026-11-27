/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.QuadratureMatrices
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# The genuine positive-definite matrix Gaussian integral

The positive CFC square root changes the actual matrix quadratic form to
a product of scalar Gaussians. Mathlib's determinant change of Lebesgue
measure and its scalar Gaussian integral give the determinant formula and
explicit integrability. Empty index types are included. This concerns an
ordinary scalar integral and assumes no Gaussian operator representation.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι]

/-- Matrix Gaussian given by `Real.exp (-(1 / 2) * (x ⬝ᵥ (P *ᵥ x)))`. -/
def matrixGaussian (P : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  Real.exp (-(1 / 2) * (x ⬝ᵥ (P *ᵥ x)))

theorem matrixGaussian_pos (P : Matrix ι ι ℝ) (x : ι → ℝ) : 0 < matrixGaussian P x :=
  Real.exp_pos _

theorem matrix_sqrt_posDef {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    open scoped Classical in (CFC.sqrt P).PosDef := by
  classical
  exact (CFC.sqrt_nonneg P).posSemidef.posDef_iff_isUnit.mpr
    ((CFC.isUnit_sqrt_iff P hP.posSemidef.nonneg).mpr hP.isUnit)

theorem matrix_sqrt_det [DecidableEq ι] {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    (CFC.sqrt P).det = Real.sqrt P.det := by
  have hS := matrix_sqrt_posDef hP
  have hsq : (CFC.sqrt P).det ^ 2 = P.det := by
    rw [pow_two, ← Matrix.det_mul]
    exact congrArg Matrix.det (by simpa only [pow_two] using CFC.sq_sqrt P hP.posSemidef.nonneg)
  rw [← hsq, Real.sqrt_sq hS.det_pos.le]

theorem matrixGaussian_eq_product_sqrt {P : Matrix ι ι ℝ} (hP : P.PosDef) (x : ι → ℝ) :
    open scoped Classical in
      matrixGaussian P x = ∏ i, Real.exp (-(1 / 2) * ((CFC.sqrt P *ᵥ x) i) ^ 2) := by
  classical
  let S := CFC.sqrt P
  have hSS : S * S = P := by
    simpa only [pow_two] using CFC.sq_sqrt P hP.posSemidef.nonneg
  have hSt : Sᵀ = S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (matrix_sqrt_posDef hP).isHermitian.eq
  have hquad : x ⬝ᵥ (P *ᵥ x) = ∑ i, (S *ᵥ x) i ^ 2 := by
    have h := dotProduct_congruence S (1 : Matrix ι ι ℝ) x x
    rw [hSt, one_mulVec, mul_one, hSS] at h
    simpa only [dotProduct, pow_two] using h.symm
  rw [matrixGaussian, ← Real.exp_sum, hquad, Finset.mul_sum]

private theorem integrable_standard_product_gaussian :
    Integrable (fun x : ι → ℝ => ∏ i, Real.exp (-(1 / 2) * (x i) ^ 2)) :=
  Integrable.fintype_prod fun _ => integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)

private theorem integral_standard_product_gaussian :
    (∫ x : ι → ℝ, ∏ i, Real.exp (-(1 / 2) * (x i) ^ 2)) =
      Real.sqrt (2 * Real.pi) ^ Fintype.card ι := by
  rw [integral_fintype_prod_volume_eq_prod
    (fun (_ : ι) (t : ℝ) => Real.exp (-(1 / 2) * t ^ 2))]
  have hhalf : Real.pi / (1 / 2) = 2 * Real.pi := by ring
  simp only [integral_gaussian, hhalf,
    Finset.prod_const, Finset.card_univ]

theorem integrable_matrixGaussian {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    Integrable (matrixGaussian P) := by
  classical
  let S := CFC.sqrt P
  let f : (ι → ℝ) → ℝ := fun x => ∏ i, Real.exp (-(1 / 2) * (x i) ^ 2)
  have hSmeas : Measurable (Matrix.toLin' S) :=
    (LinearMap.continuous_on_pi _).measurable
  have hdet : S.det ≠ 0 := (matrix_sqrt_posDef hP).det_pos.ne'
  have hf : Integrable f (Measure.map (Matrix.toLin' S) volume) := by
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet]
    exact integrable_standard_product_gaussian.smul_measure ENNReal.ofReal_ne_top
  have hcomp := hf.comp_measurable hSmeas
  have heq : f ∘ Matrix.toLin' S = matrixGaussian P := by
    funext x
    exact (matrixGaussian_eq_product_sqrt hP x).symm
  rwa [heq] at hcomp

/-- Actual Lebesgue integral of the full, non-diagonal matrix Gaussian. -/
theorem integral_matrixGaussian [DecidableEq ι] {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    (∫ x : ι → ℝ, matrixGaussian P x) =
      Real.sqrt (2 * Real.pi) ^ Fintype.card ι / Real.sqrt P.det := by
  let S := CFC.sqrt P
  let f : (ι → ℝ) → ℝ := fun x => ∏ i, Real.exp (-(1 / 2) * (x i) ^ 2)
  have hSmeas : Measurable (Matrix.toLin' S) :=
    (LinearMap.continuous_on_pi _).measurable
  have hdetpos : 0 < S.det := (matrix_sqrt_posDef hP).det_pos
  have hf : StronglyMeasurable f := by fun_prop
  have h := integral_map_of_stronglyMeasurable
    (μ := (volume : Measure (ι → ℝ))) hSmeas hf
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdetpos.ne', integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)] at h
  simp only [abs_inv, abs_of_pos hdetpos, smul_eq_mul] at h
  have heq : (fun x => f (Matrix.toLin' S x)) = matrixGaussian P := by
    funext x
    exact (matrixGaussian_eq_product_sqrt hP x).symm
  rw [heq] at h
  rw [show (∫ x, f x) = Real.sqrt (2 * Real.pi) ^ Fintype.card ι from
    integral_standard_product_gaussian, matrix_sqrt_det hP] at h
  exact h.symm.trans (by ring)

end VacuumBellSeparation.Gaussian
