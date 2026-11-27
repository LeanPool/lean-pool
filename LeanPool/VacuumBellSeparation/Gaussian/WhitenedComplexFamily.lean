/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianSourceCompressionBounds
public import LeanPool.VacuumBellSeparation.Gaussian.ComplexifiedOperator

/-!
# Actual whitening of a finite real Hilbert-space family

The complex synthesis map sends coordinate vectors to the canonical
complexifications of the given real vectors. Multiplication by the true
inverse covariance square root makes it isometric. Its compression of a
real operator's complexification is the normalized matrix of the actual
real bilinear form; no compression identity is an input.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix ContinuousLinearMap HilbertComplexification
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [DecidableEq ι] in
theorem euclideanCLM_eq_of_inner_coordinates
    {A B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (h : ∀ i j, inner ℂ (EuclideanSpace.basisFun ι ℂ i) (A (EuclideanSpace.basisFun ι ℂ j)) =
      inner ℂ (EuclideanSpace.basisFun ι ℂ i) (B (EuclideanSpace.basisFun ι ℂ j))) : A = B := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun ι ℂ).toBasis.ext
  intro j
  apply (EuclideanSpace.basisFun ι ℂ).repr.injective
  ext i
  change (EuclideanSpace.basisFun ι ℂ).repr (A (EuclideanSpace.basisFun ι ℂ j)) i =
    (EuclideanSpace.basisFun ι ℂ).repr (B (EuclideanSpace.basisFun ι ℂ j)) i
  simpa only [OrthonormalBasis.repr_apply_apply] using h i j

/-- Real family gram obtained from `Matrix.gram`. -/
def realFamilyGram (f : ι → E) : Matrix ι ι ℝ := Matrix.gram ℝ f

/-- Real family form given by `fun i j => inner ℝ (f i) (J (f j))`. -/
def realFamilyForm (f : ι → E) (J : E →L[ℝ] E) : Matrix ι ι ℝ :=
  fun i j => inner ℝ (f i) (J (f j))

/-- The complex-linear synthesis operator for a finite family, valued in its real Hilbert-space
complexification. -/
def complexFamilySynthesis (f : ι → E) :
    EuclideanSpace ℂ ι →L[ℂ] HilbertComplexification E :=
  ((EuclideanSpace.basisFun ι ℂ).toBasis.constr ℂ (fun i => ofReal (f i))).toContinuousLinearMap

omit [CompleteSpace E] [DecidableEq ι] in
theorem complexFamilySynthesis_basis (f : ι → E) (i : ι) :
    complexFamilySynthesis f (EuclideanSpace.basisFun ι ℂ i) = ofReal (f i) := by
  exact Module.Basis.constr_basis _ _ _ _

theorem complexFamilySynthesis_gram (f : ι → E) :
    (complexFamilySynthesis f).adjoint.comp (complexFamilySynthesis f) =
      realMatrixOperator (realFamilyGram f) := by
  apply euclideanCLM_eq_of_inner_coordinates
  intro i j
  rw [ContinuousLinearMap.comp_apply, adjoint_inner_right, complexFamilySynthesis_basis,
    complexFamilySynthesis_basis]
  rw [realMatrixOperator, euclidean_coordinate_inner_matrix]
  apply Complex.ext <;> simp [HilbertComplexification.inner_eq, realFamilyGram, Matrix.gram_apply]

theorem complexFamilySynthesis_form (f : ι → E) (J : E →L[ℝ] E) :
    (complexFamilySynthesis f).adjoint.comp ((complexify J).comp (complexFamilySynthesis f)) =
      realMatrixOperator (realFamilyForm f J) := by
  apply euclideanCLM_eq_of_inner_coordinates
  intro i j
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, adjoint_inner_right,
    complexFamilySynthesis_basis,
    complexFamilySynthesis_basis, complexify_ofReal]
  rw [realMatrixOperator, euclidean_coordinate_inner_matrix]
  apply Complex.ext <;> simp [HilbertComplexification.inner_eq, realFamilyForm]

/-- Whitened complex family map of type `EuclideanSpace ℂ ι →L[ℂ] HilbertComplexification E`. -/
def whitenedComplexFamilyMap (f : ι → E) :
    EuclideanSpace ℂ ι →L[ℂ] HilbertComplexification E :=
  (complexFamilySynthesis f).comp (realMatrixOperator ((CFC.sqrt (realFamilyGram f))⁻¹))

theorem realMatrixOperator_adjoint (A : Matrix ι ι ℝ) :
    (realMatrixOperator A).adjoint = realMatrixOperator Aᵀ := by
  simp only [realMatrixOperator, complexifyMatrix_transpose]
  exact (map_star Matrix.toEuclideanCLM (complexifyMatrix A)).symm

theorem whitenedComplexFamilyMap_gram (f : ι → E) (hf : LinearIndependent ℝ f) :
    (whitenedComplexFamilyMap f).adjoint.comp (whitenedComplexFamilyMap f) = 1 := by
  have hV : (realFamilyGram f).PosDef := Matrix.posDef_gram_of_linearIndependent hf
  have ht := matrix_inverse_sqrt_transpose hV
  have hroot := matrix_sqrt_posDef hV
  have hd := (Matrix.isUnit_iff_isUnit_det (CFC.sqrt (realFamilyGram f))).mp hroot.isUnit
  have hs : (CFC.sqrt (realFamilyGram f))⁻¹ * realFamilyGram f *
      (CFC.sqrt (realFamilyGram f))⁻¹ = 1 := by
    calc
      _ = (CFC.sqrt (realFamilyGram f))⁻¹ *
          (CFC.sqrt (realFamilyGram f) * CFC.sqrt (realFamilyGram f)) *
            (CFC.sqrt (realFamilyGram f))⁻¹ := by
        rw [CFC.sqrt_mul_sqrt_self _ hV.posSemidef.nonneg]
      _ = 1 := by
        rw [← mul_assoc, Matrix.nonsing_inv_mul _ hd, one_mul, Matrix.mul_nonsing_inv _ hd]
  rw [whitenedComplexFamilyMap, adjoint_comp, realMatrixOperator_adjoint, ht]
  calc
    _ = realMatrixOperator ((CFC.sqrt (realFamilyGram f))⁻¹) *
        ((complexFamilySynthesis f).adjoint.comp (complexFamilySynthesis f)) *
          realMatrixOperator ((CFC.sqrt (realFamilyGram f))⁻¹) := by
      simp only [mul_def, comp_assoc]
    _ = 1 := by
      rw [complexFamilySynthesis_gram, ← realMatrixOperator_mul,
        ← realMatrixOperator_mul, hs, realMatrixOperator_one]

/-- Linear isometry for the whitened complex family, of type `EuclideanSpace ℂ ι →ₗᵢ[ℂ]
HilbertComplexification E`. -/
def whitenedComplexFamily (f : ι → E) (hf : LinearIndependent ℝ f) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] HilbertComplexification E :=
  (whitenedComplexFamilyMap f).toLinearMap.isometryOfInner (by
    intro x y
    change inner ℂ (whitenedComplexFamilyMap f x) (whitenedComplexFamilyMap f y) =
      inner ℂ x y
    rw [← (whitenedComplexFamilyMap f).adjoint_inner_right]
    change inner ℂ x (((whitenedComplexFamilyMap f).adjoint.comp
      (whitenedComplexFamilyMap f)) y) = inner ℂ x y
    rw [whitenedComplexFamilyMap_gram f hf, one_apply_eq_self])

@[simp] theorem whitenedComplexFamily_toCLM (f : ι → E) (hf : LinearIndependent ℝ f) :
    (whitenedComplexFamily f hf).toContinuousLinearMap = whitenedComplexFamilyMap f := rfl

theorem compression_whitened_complexify (f : ι → E) (hf : LinearIndependent ℝ f)
    (J : E →L[ℝ] E) :
    compression (whitenedComplexFamily f hf) (complexify J) =
      realMatrixOperator (relativeCovariancePerturbation (realFamilyGram f)
        (realFamilyForm f J)) := by
  have hV : (realFamilyGram f).PosDef := Matrix.posDef_gram_of_linearIndependent hf
  rw [compression, whitenedComplexFamily_toCLM, whitenedComplexFamilyMap,
    adjoint_comp, realMatrixOperator_adjoint, matrix_inverse_sqrt_transpose hV]
  calc
    _ = realMatrixOperator ((CFC.sqrt (realFamilyGram f))⁻¹) *
        ((complexFamilySynthesis f).adjoint.comp ((complexify J).comp (complexFamilySynthesis f))) *
          realMatrixOperator ((CFC.sqrt (realFamilyGram f))⁻¹) := by
      simp only [mul_def, comp_assoc]
    _ = _ := by
      rw [complexFamilySynthesis_form, ← realMatrixOperator_mul, ← realMatrixOperator_mul]
      rfl

theorem compression_whitened_normalizedCommutation
    (f : ι → E) (hf : LinearIndependent ℝ f) (J : E →L[ℝ] E) :
    compression (whitenedComplexFamily f hf) (normalizedCommutation (complexify J)) =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (covarianceCommutationMatrix (realFamilyGram f)
        (realFamilyForm f J)) := by
  have hc : compression (whitenedComplexFamily f hf) (normalizedCommutation (complexify J)) =
      (Complex.I / 2) • compression (whitenedComplexFamily f hf) (complexify J) := by
    ext x
    simp [compression, normalizedCommutation]
  rw [hc, compression_whitened_complexify f hf J, covarianceCommutationMatrix,
    map_smul]
  rfl

end VacuumBellSeparation.Gaussian
