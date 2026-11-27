/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixGaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Genuine Fourier integral of a positive matrix Gaussian

The actual positive square root changes coordinates, its determinant gives
the Lebesgue Jacobian, and the pinned Gaussian Fourier theorem supplies the
linear phase. The inverse covariance and determinant are actual matrix
operations justified by positive definiteness, including dimension zero.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix Gaussian Fourier given by `Complex.exp (((-(1 / 2) * (x ⬝ᵥ (P *ᵥ x)) : ℝ) : ℂ) +
Complex.I * ((y ⬝ᵥ x : ℝ) : ℂ))`. -/
def matrixGaussianFourier (P : Matrix ι ι ℝ) (y x : ι → ℝ) : ℂ :=
  Complex.exp (((-(1 / 2) * (x ⬝ᵥ (P *ᵥ x)) : ℝ) : ℂ) +
    Complex.I * ((y ⬝ᵥ x : ℝ) : ℂ))

private theorem standard_matrixGaussianFourier_eq (y x : ι → ℝ) :
    matrixGaussianFourier 1 y x =
      Complex.exp (-(1 / 2 : ℂ) * ∑ i, (x i : ℂ) ^ 2 +
        ∑ i, (Complex.I * (y i : ℂ)) * (x i : ℂ)) := by
  unfold matrixGaussianFourier
  rw [one_mulVec]
  congr 1
  simp only [dotProduct, ← pow_two, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_sum, Complex.ofReal_pow, Finset.mul_sum, mul_assoc]

private theorem integrable_standard_matrixGaussianFourier (y : ι → ℝ) :
    Integrable (matrixGaussianFourier 1 y) := by
  exact (GaussianFourier.integrable_cexp_neg_mul_sum_add
    (by norm_num : 0 < (1 / 2 : ℂ).re) (fun i => Complex.I * (y i : ℂ))).congr
      (Filter.Eventually.of_forall fun x => (standard_matrixGaussianFourier_eq y x).symm)

private theorem integral_standard_matrixGaussianFourier (y : ι → ℝ) :
    (∫ x : ι → ℝ, matrixGaussianFourier 1 y x) =
      ((Real.sqrt (2 * Real.pi) ^ Fintype.card ι : ℝ) : ℂ) *
        Complex.exp (((-(1 / 2) * (∑ i, y i ^ 2) : ℝ) : ℂ)) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sum_add
    (by norm_num : 0 < (1 / 2 : ℂ).re) (fun i => Complex.I * (y i : ℂ))
  have hz := GaussianFourier.integral_cexp_neg_mul_sum_add
    (by norm_num : 0 < (1 / 2 : ℂ).re) (fun _ : ι => (0 : ℂ))
  have he₀ : (fun x : ι → ℝ =>
      Complex.exp (-(1 / 2 : ℂ) * ∑ i, (x i : ℂ) ^ 2 + ∑ i, (0 : ℂ) * (x i : ℂ))) =
        fun x => (matrixGaussian (1 : Matrix ι ι ℝ) x : ℂ) := by
    funext x
    simp only [zero_mul, Finset.sum_const_zero, add_zero, matrixGaussian, one_mulVec,
      dotProduct, ← pow_two, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Complex.ofReal_sum, Complex.ofReal_pow]
  rw [he₀, integral_complex_ofReal, integral_matrixGaussian (Matrix.PosDef.one :
    (1 : Matrix ι ι ℝ).PosDef)] at hz
  simp only [Matrix.det_one, Real.sqrt_one, div_one, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero, zero_div, Complex.exp_zero, mul_one] at hz
  have hphase : (∑ i, (Complex.I * (y i : ℂ)) ^ 2) / (4 * (1 / 2 : ℂ)) =
      ((-(1 / 2) * (∑ i, y i ^ 2) : ℝ) : ℂ) := by
    simp only [mul_pow, Complex.I_sq, neg_one_mul, Finset.sum_neg_distrib,
      Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat, Complex.ofReal_sum, Complex.ofReal_pow]
    ring
  rw [hphase, ← hz] at h
  simpa only [standard_matrixGaussianFourier_eq] using h

theorem matrix_sqrt_fourier_linear {P : Matrix ι ι ℝ} (hP : P.PosDef) (y x : ι → ℝ) :
    (CFC.sqrt P)⁻¹ *ᵥ y ⬝ᵥ (CFC.sqrt P *ᵥ x) = y ⬝ᵥ x := by
  let S := CFC.sqrt P
  have hSi : S⁻¹ * S = 1 := S.nonsing_inv_mul
    ((Matrix.isUnit_iff_isUnit_det S).mp (matrix_sqrt_posDef hP).isUnit)
  have hSit : (S⁻¹)ᵀ = S⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (matrix_sqrt_posDef hP).inv.isHermitian.eq
  have h := Matrix.dotProduct_transpose_mulVec S⁻¹ (S *ᵥ x) y
  rw [hSit, Matrix.mulVec_mulVec, hSi, one_mulVec] at h
  exact (dotProduct_comm _ _).trans h

theorem matrix_sqrt_inverse_quadratic {P : Matrix ι ι ℝ} (hP : P.PosDef) (y : ι → ℝ) :
    (∑ i, ((CFC.sqrt P)⁻¹ *ᵥ y) i ^ 2) = y ⬝ᵥ (P⁻¹ *ᵥ y) := by
  let S := CFC.sqrt P
  have hSS : S * S = P := by simpa only [pow_two] using CFC.sq_sqrt P hP.posSemidef.nonneg
  have hSit : (S⁻¹)ᵀ = S⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (matrix_sqrt_posDef hP).inv.isHermitian.eq
  have h := dotProduct_congruence S⁻¹ (1 : Matrix ι ι ℝ) y y
  rw [hSit, one_mulVec, mul_one, ← Matrix.mul_inv_rev, hSS] at h
  simpa only [dotProduct, pow_two] using h

theorem matrixGaussianFourier_eq_sqrt {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (y x : ι → ℝ) :
    matrixGaussianFourier P y x =
      matrixGaussianFourier 1 ((CFC.sqrt P)⁻¹ *ᵥ y) (CFC.sqrt P *ᵥ x) := by
  let S := CFC.sqrt P
  have hSS : S * S = P := by simpa only [pow_two] using CFC.sq_sqrt P hP.posSemidef.nonneg
  have hSt : Sᵀ = S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (matrix_sqrt_posDef hP).isHermitian.eq
  have hq := dotProduct_congruence S (1 : Matrix ι ι ℝ) x x
  rw [hSt, one_mulVec, mul_one, hSS] at hq
  simp only [matrixGaussianFourier, one_mulVec, matrix_sqrt_fourier_linear hP]
  exact congrArg (fun t : ℝ => Complex.exp (((-(1 / 2) * t : ℝ) : ℂ) +
    Complex.I * ((y ⬝ᵥ x : ℝ) : ℂ))) hq.symm

omit [DecidableEq ι] in
theorem integrable_matrixGaussianFourier {P : Matrix ι ι ℝ} (hP : P.PosDef) (y : ι → ℝ) :
    Integrable (matrixGaussianFourier P y) := by
  classical
  let S := CFC.sqrt P
  let f := matrixGaussianFourier 1 (S⁻¹ *ᵥ y)
  have hSmeas : Measurable (Matrix.toLin' S) := (LinearMap.continuous_on_pi _).measurable
  have hf : Integrable f (Measure.map (Matrix.toLin' S) volume) := by
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (matrix_sqrt_posDef hP).det_pos.ne']
    exact (integrable_standard_matrixGaussianFourier _).smul_measure ENNReal.ofReal_ne_top
  have hcomp := hf.comp_measurable hSmeas
  have heq : f ∘ Matrix.toLin' S = matrixGaussianFourier P y := by
    funext x
    exact (matrixGaussianFourier_eq_sqrt hP y x).symm
  rwa [heq] at hcomp

/-- Actual Fourier integral, with inverse quadratic form and determinant
normalization justified by a genuine positive matrix square root. -/
theorem integral_matrixGaussianFourier {P : Matrix ι ι ℝ} (hP : P.PosDef) (y : ι → ℝ) :
    (∫ x : ι → ℝ, matrixGaussianFourier P y x) =
      ((Real.sqrt (2 * Real.pi) ^ Fintype.card ι / Real.sqrt P.det : ℝ) : ℂ) *
        Complex.exp (((-(1 / 2) * (y ⬝ᵥ (P⁻¹ *ᵥ y)) : ℝ) : ℂ)) := by
  let S := CFC.sqrt P
  let f := matrixGaussianFourier 1 (S⁻¹ *ᵥ y)
  have hSmeas : Measurable (Matrix.toLin' S) := (LinearMap.continuous_on_pi _).measurable
  have hdetpos : 0 < S.det := (matrix_sqrt_posDef hP).det_pos
  have hf : StronglyMeasurable f := by unfold f matrixGaussianFourier; fun_prop
  have h := integral_map_of_stronglyMeasurable (μ := (volume : Measure (ι → ℝ))) hSmeas hf
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdetpos.ne', integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)] at h
  simp only [abs_inv, abs_of_pos hdetpos, RCLike.real_smul_eq_coe_mul] at h
  have heq : (fun x => f (Matrix.toLin' S x)) = matrixGaussianFourier P y := by
    funext x
    exact (matrixGaussianFourier_eq_sqrt hP y x).symm
  rw [heq] at h
  change ((S.det⁻¹ : ℝ) : ℂ) * (∫ x, matrixGaussianFourier 1 (S⁻¹ *ᵥ y) x) = _ at h
  rw [integral_standard_matrixGaussianFourier,
    matrix_sqrt_inverse_quadratic hP, matrix_sqrt_det hP] at h
  exact h.symm.trans (by push_cast; ring)

end VacuumBellSeparation.Gaussian
