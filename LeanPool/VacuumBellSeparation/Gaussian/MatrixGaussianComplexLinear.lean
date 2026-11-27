/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixGaussianFourier
public import LeanPool.VacuumBellSeparation.Gaussian.QuantumWilliamson

/-!
# Matrix Gaussian integration with arbitrary complex linear coefficient

The real positive-definite quadratic form is integrated against a complex
linear exponential. Its actual integrability and value follow from the
positive square-root change of coordinates and the pinned complex scalar
Gaussian formula. This extends the imaginary-frequency calculation without
assuming a formal analytic continuation or an unproved Gaussian kernel.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix Gaussian complex linear given by `Complex.exp (((-(1 / 2) * (x ⬝ᵥ (P *ᵥ x)) : ℝ) : ℂ) +
a ⬝ᵥ (fun i => (x i : ℂ)))`. -/
def matrixGaussianComplexLinear (P : Matrix ι ι ℝ) (a : ι → ℂ) (x : ι → ℝ) : ℂ :=
  Complex.exp (((-(1 / 2) * (x ⬝ᵥ (P *ᵥ x)) : ℝ) : ℂ) +
    a ⬝ᵥ (fun i => (x i : ℂ)))

omit [DecidableEq ι] in
theorem complexifyMatrix_mulVec_real (P : Matrix ι ι ℝ) (x : ι → ℝ) :
    complexifyMatrix P *ᵥ (fun i => (x i : ℂ)) = fun i => ((P *ᵥ x) i : ℂ) := by
  funext i
  exact ((algebraMap ℝ ℂ).map_mulVec P x i).symm

omit [Fintype ι] [DecidableEq ι] in
theorem complexifyMatrix_transpose_bilinear (P : Matrix ι ι ℝ) :
    (complexifyMatrix P)ᵀ = complexifyMatrix Pᵀ := rfl

private theorem standard_matrixGaussianComplexLinear_eq (a : ι → ℂ) (x : ι → ℝ) :
    matrixGaussianComplexLinear 1 a x =
      Complex.exp (-(1 / 2 : ℂ) * ∑ i, (x i : ℂ) ^ 2 + ∑ i, a i * (x i : ℂ)) := by
  unfold matrixGaussianComplexLinear
  rw [one_mulVec]
  congr 1
  simp only [dotProduct, ← pow_two, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_sum, Complex.ofReal_pow]

private theorem integrable_standard_matrixGaussianComplexLinear (a : ι → ℂ) :
    Integrable (matrixGaussianComplexLinear 1 a) := by
  apply (GaussianFourier.integrable_cexp_neg_mul_sum_add
    (by norm_num : 0 < (1 / 2 : ℂ).re) a).congr
  exact Filter.Eventually.of_forall fun x =>
    (standard_matrixGaussianComplexLinear_eq a x).symm

private theorem integral_standard_matrixGaussianComplexLinear (a : ι → ℂ) :
    (∫ x : ι → ℝ, matrixGaussianComplexLinear 1 a x) =
      ((Real.sqrt (2 * Real.pi) ^ Fintype.card ι : ℝ) : ℂ) *
        Complex.exp ((1 / 2 : ℂ) * (a ⬝ᵥ a)) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sum_add
    (by norm_num : 0 < (1 / 2 : ℂ).re) a
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
  rw [he₀] at hz
  have hreal := integral_complex_ofReal
    (μ := (volume : Measure (ι → ℝ))) (f := matrixGaussian (1 : Matrix ι ι ℝ))
  rw [integral_matrixGaussian (Matrix.PosDef.one :
    (1 : Matrix ι ι ℝ).PosDef)] at hreal
  have hconstant := hreal.symm.trans hz
  simp only [Matrix.det_one, Real.sqrt_one, div_one, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero, zero_div, Complex.exp_zero, mul_one] at hconstant
  have hphase : (∑ i, a i ^ 2) / (4 * (1 / 2 : ℂ)) = (1 / 2 : ℂ) * (a ⬝ᵥ a) := by
    simp only [dotProduct, ← pow_two]
    ring
  rw [hphase, ← hconstant] at h
  simpa only [standard_matrixGaussianComplexLinear_eq] using h

theorem matrix_sqrt_complex_linear {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (a : ι → ℂ) (x : ι → ℝ) :
    (complexifyMatrix (CFC.sqrt P)⁻¹ *ᵥ a) ⬝ᵥ (fun i => ((CFC.sqrt P *ᵥ x) i : ℂ)) =
      a ⬝ᵥ (fun i => (x i : ℂ)) := by
  let S := CFC.sqrt P
  have hSi : S⁻¹ * S = 1 := S.nonsing_inv_mul
    ((Matrix.isUnit_iff_isUnit_det S).mp (matrix_sqrt_posDef hP).isUnit)
  have hSit : (S⁻¹)ᵀ = S⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (matrix_sqrt_posDef hP).inv.isHermitian.eq
  have h := Matrix.dotProduct_transpose_mulVec (complexifyMatrix S⁻¹)
    (complexifyMatrix S *ᵥ (fun i => (x i : ℂ))) a
  rw [complexifyMatrix_transpose_bilinear, hSit, Matrix.mulVec_mulVec,
    ← complexifyMatrix_mul, hSi, complexifyMatrix_one, one_mulVec] at h
  rw [← complexifyMatrix_mulVec_real]
  exact (dotProduct_comm _ _).trans h

theorem matrix_sqrt_complex_inverse_quadratic {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (a : ι → ℂ) :
    (complexifyMatrix (CFC.sqrt P)⁻¹ *ᵥ a) ⬝ᵥ (complexifyMatrix (CFC.sqrt P)⁻¹ *ᵥ a) =
      a ⬝ᵥ (complexifyMatrix P⁻¹ *ᵥ a) := by
  let S := CFC.sqrt P
  have hSS : S * S = P := by simpa only [pow_two] using CFC.sq_sqrt P hP.posSemidef.nonneg
  have hSit : (S⁻¹)ᵀ = S⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (matrix_sqrt_posDef hP).inv.isHermitian.eq
  have h := Matrix.dotProduct_transpose_mulVec (complexifyMatrix S⁻¹)
    (complexifyMatrix S⁻¹ *ᵥ a) a
  rw [complexifyMatrix_transpose_bilinear, hSit, Matrix.mulVec_mulVec,
    ← complexifyMatrix_mul, ← Matrix.mul_inv_rev, hSS] at h
  exact h

theorem matrixGaussianComplexLinear_eq_sqrt {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (a : ι → ℂ) (x : ι → ℝ) :
    matrixGaussianComplexLinear P a x =
      matrixGaussianComplexLinear 1 (complexifyMatrix (CFC.sqrt P)⁻¹ *ᵥ a) (CFC.sqrt P *ᵥ x) := by
  let S := CFC.sqrt P
  have hSS : S * S = P := by simpa only [pow_two] using CFC.sq_sqrt P hP.posSemidef.nonneg
  have hSt : Sᵀ = S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (matrix_sqrt_posDef hP).isHermitian.eq
  have hq := dotProduct_congruence S (1 : Matrix ι ι ℝ) x x
  rw [hSt, one_mulVec, mul_one, hSS] at hq
  simp only [matrixGaussianComplexLinear, one_mulVec, matrix_sqrt_complex_linear hP]
  exact congrArg (fun t : ℝ => Complex.exp (((-(1 / 2) * t : ℝ) : ℂ) +
    a ⬝ᵥ (fun i => (x i : ℂ)))) hq.symm

omit [DecidableEq ι] in
theorem integrable_matrixGaussianComplexLinear {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (a : ι → ℂ) : Integrable (matrixGaussianComplexLinear P a) := by
  classical
  let S := CFC.sqrt P
  let f := matrixGaussianComplexLinear 1 (complexifyMatrix S⁻¹ *ᵥ a)
  have hSmeas : Measurable (Matrix.toLin' S) := (LinearMap.continuous_on_pi _).measurable
  have hf : Integrable f (Measure.map (Matrix.toLin' S) volume) := by
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (matrix_sqrt_posDef hP).det_pos.ne']
    exact (integrable_standard_matrixGaussianComplexLinear _).smul_measure ENNReal.ofReal_ne_top
  have hcomp := hf.comp_measurable hSmeas
  have heq : f ∘ Matrix.toLin' S = matrixGaussianComplexLinear P a := by
    funext x
    exact (matrixGaussianComplexLinear_eq_sqrt hP a x).symm
  rwa [heq] at hcomp

/-- Genuine complex-linear Gaussian integral; the matrix inverse and the
quadratic form in the complex coefficient are bilinear, without conjugation. -/
theorem integral_matrixGaussianComplexLinear {P : Matrix ι ι ℝ} (hP : P.PosDef)
    (a : ι → ℂ) :
    (∫ x : ι → ℝ, matrixGaussianComplexLinear P a x) =
      ((Real.sqrt (2 * Real.pi) ^ Fintype.card ι / Real.sqrt P.det : ℝ) : ℂ) *
        Complex.exp ((1 / 2 : ℂ) * (a ⬝ᵥ (complexifyMatrix P⁻¹ *ᵥ a))) := by
  let S := CFC.sqrt P
  let f := matrixGaussianComplexLinear 1 (complexifyMatrix S⁻¹ *ᵥ a)
  have hSmeas : Measurable (Matrix.toLin' S) := (LinearMap.continuous_on_pi _).measurable
  have hdetpos : 0 < S.det := (matrix_sqrt_posDef hP).det_pos
  have hf : StronglyMeasurable f := by unfold f matrixGaussianComplexLinear; fun_prop
  have h := integral_map_of_stronglyMeasurable
    (μ := (volume : Measure (ι → ℝ))) hSmeas hf
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdetpos.ne', integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)] at h
  simp only [abs_inv, abs_of_pos hdetpos, RCLike.real_smul_eq_coe_mul] at h
  have heq : (fun x => f (Matrix.toLin' S x)) = matrixGaussianComplexLinear P a := by
    funext x
    exact (matrixGaussianComplexLinear_eq_sqrt hP a x).symm
  rw [heq] at h
  change ((S.det⁻¹ : ℝ) : ℂ) * (∫ x, matrixGaussianComplexLinear 1
    (complexifyMatrix S⁻¹ *ᵥ a) x) = _ at h
  rw [integral_standard_matrixGaussianComplexLinear,
    matrix_sqrt_complex_inverse_quadratic hP, matrix_sqrt_det hP] at h
  exact h.symm.trans (by push_cast; ring)

end VacuumBellSeparation.Gaussian
