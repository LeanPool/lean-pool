/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
module

public import LeanPool.KLS.BrownianMotion.Auxiliary.ContinuousBilinForm
public import LeanPool.KLS.BrownianMotion.Auxiliary.MeasureTheory
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Covariance matrix

-/

@[expose] public section

open MeasureTheory InnerProductSpace NormedSpace WithLp
open scoped ENNReal NNReal Matrix

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

nonrec
lemma IsGaussian.covarianceBilin_apply [IsGaussian μ] [SecondCountableTopology E] [CompleteSpace E]
    (x y : E) :
    covarianceBilin μ x y = ∫ z, ⟪x, z - μ[id]⟫_ℝ * ⟪y, z - μ[id]⟫_ℝ ∂μ :=
  covarianceBilin_apply IsGaussian.memLp_two_id x y

lemma covarianceBilin_apply_prod {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (x y : WithLp 2 (ℝ × ℝ)) :
    covarianceBilin (μ.map (fun ω ↦ toLp 2 (X ω, Y ω))) x y =
      x.fst * y.fst * Var[X; μ] + (x.fst * y.snd + x.snd * y.fst) * cov[X, Y; μ] +
      x.snd * y.snd * Var[Y; μ] := by
  have := hX.aemeasurable
  have := hY.aemeasurable
  nth_rw 1 [covarianceBilin_apply_eq_cov, covariance_map_fun]
  · simp only [prod_inner_apply, ofLp_fst, RCLike.inner_apply', conj_trivial, ofLp_snd]
    rw [covariance_fun_add_left, covariance_fun_add_right, covariance_fun_add_right]
    · simp_rw [covariance_const_mul_left, covariance_const_mul_right]
      rw [covariance_comm X Y, covariance_self, covariance_self]
      · ring
      · exact hY.aemeasurable
      · exact hX.aemeasurable
    any_goals exact MemLp.const_mul (by assumption) _
    exact hX.const_mul _ |>.add <| hY.const_mul _
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2
      (MemLp.of_fst_of_snd_prodLp ⟨hX, hY⟩)

lemma isSymm_covarianceBilin :
    LinearMap.BilinForm.IsSymm (covarianceBilin μ).toBilinForm :=
 isPosSemidef_covarianceBilin.1

variable [FiniteDimensional ℝ E]

/-- Covariance matrix of a measure on a finite dimensional inner product space. -/
noncomputable
def covMatrix (μ : Measure E) : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  LinearMap.BilinForm.toMatrix (stdOrthonormalBasis ℝ E).toBasis (covarianceBilin μ).toBilinForm

lemma covMatrix_apply (μ : Measure E) (i j : Fin (Module.finrank ℝ E)) :
    covMatrix μ i j =
      covarianceBilin μ (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) := by
  simp [covMatrix]

lemma covMatrix_mulVec (x : Fin (Module.finrank ℝ E) → ℝ) :
    (covMatrix μ).mulVec x = fun i ↦
      covarianceBilin μ (stdOrthonormalBasis ℝ E i) (∑ j, x j • stdOrthonormalBasis ℝ E j) := by
  ext
  simp [covMatrix, Matrix.mulVec_eq_sum]

lemma dotProduct_covMatrix_mulVec (x y : Fin (Module.finrank ℝ E) → ℝ) :
    x ⬝ᵥ (covMatrix μ).mulVec y =
      covarianceBilin μ (∑ j, x j • stdOrthonormalBasis ℝ E j)
        (∑ j, y j • stdOrthonormalBasis ℝ E j) := by
  simp_rw [covMatrix, LinearMap.BilinForm.dotProduct_toMatrix_mulVec,
    Module.Basis.equivFun_symm_apply, OrthonormalBasis.coe_toBasis]
  simp

lemma covarianceBilin_eq_dotProduct_covMatrix_mulVec (x y : E) :
    covarianceBilin μ x y =
      ((stdOrthonormalBasis ℝ E).repr x) ⬝ᵥ
        ((covMatrix μ).mulVec ((stdOrthonormalBasis ℝ E).repr y)) := by
  rw [ContinuousBilinForm.apply_eq_dotProduct_toMatrix_mulVec _ (stdOrthonormalBasis ℝ E).toBasis]
  rfl

lemma covMatrix_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L : E →L[ℝ] F) (i j : Fin (Module.finrank ℝ F)) :
    covMatrix (μ.map L) i j =
      (stdOrthonormalBasis ℝ E).repr (L.adjoint (stdOrthonormalBasis ℝ F i)) ⬝ᵥ ((covMatrix μ) *ᵥ
        (stdOrthonormalBasis ℝ E).repr (L.adjoint (stdOrthonormalBasis ℝ F j))) := by
  rw [covMatrix_apply, covarianceBilin_map h, covarianceBilin_eq_dotProduct_covMatrix_mulVec]

lemma posSemidef_covMatrix : (covMatrix μ).PosSemidef := by
  rw [covMatrix, ← LinearMap.BilinForm.isPosSemidef_iff_posSemidef_toMatrix]
  exact isPosSemidef_covarianceBilin

end ProbabilityTheory
