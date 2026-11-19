/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixGaussianUnitaryInvariant.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.MatrixGaussianLSI
public import LeanPool.GinibrePoincare.Analysis.MatrixSchurDensity
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Matrix Gaussian unitary invariant

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixUnitaryConjugation_apply`, `matrixGaussianMeasure_unitary_conjugation`.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.Operator BigOperators NNReal
namespace GinibrePoincare
noncomputable section

@[simp] theorem matrixRealCoordinates_entry (n : ℕ) (x : MatrixRealIndex n → ℝ)
    (i j : Fin n) :
    matrixRealCoordinates n x i j = (x ⟨i, ⟨j, 0⟩⟩ : ℂ) +
      (x ⟨i, ⟨j, 1⟩⟩ : ℂ) * Complex.I := by
  simp [matrixRealCoordinates, gaussianCurryEquiv, ContinuousLinearEquiv.piCongrRight,
    LinearEquiv.piCurry, Equiv.piCurry, Sigma.curry, Complex.basisOneI,
    ]

theorem matrixRealCoordinates_HS (n : ℕ) (x : MatrixRealIndex n → ℝ) :
    matrixHSNormSq (matrixRealCoordinates n x) = ∑ p, (x p)^2 := by
  rw [matrixHSNormSq_eq_sum (matrixRealCoordinates n x)]
  simp_rw [matrixRealCoordinates_entry, Complex.normSq_apply]
  simp [Fintype.sum_sigma, Fin.sum_univ_two, pow_two]

/-- Unitary conjugation in actual real matrix entry coordinates. -/
def matrixUnitaryRealMap {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) :
    (MatrixRealIndex n → ℝ) →L[ℝ] (MatrixRealIndex n → ℝ) :=
  (matrixRealCoordinates n).symm.toContinuousLinearMap.comp
    ((((ContinuousLinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)).flip Uᴴ).comp
      ((ContinuousLinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)) U)).restrictScalars ℝ |>.comp
        (matrixRealCoordinates n).toContinuousLinearMap)

theorem matrixUnitaryRealMap_apply {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (x : MatrixRealIndex n → ℝ) :
    matrixUnitaryRealMap U x = (matrixRealCoordinates n).symm
      (U * Matrix.of (matrixRealCoordinates n x) * Uᴴ) := by
  simp only [matrixUnitaryRealMap, 
    ]
  rfl

theorem matrixUnitaryRealMap_sum_sq {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (x : MatrixRealIndex n → ℝ) :
    ∑ p, (matrixUnitaryRealMap U x p)^2 = ∑ p, (x p)^2 := by
  rw [← matrixRealCoordinates_HS n, matrixUnitaryRealMap_apply,
    ContinuousLinearEquiv.apply_symm_apply (matrixRealCoordinates n)
      (U * Matrix.of (matrixRealCoordinates n x) * Uᴴ),
    matrixHSNormSq_unitary_conjugation n _ U hU]
  exact matrixRealCoordinates_HS n x

/-- Unitary conjugation `A ↦ U A Uᴴ` in real entry coordinates, as a linear map on the Euclidean
space indexed by `MatrixRealIndex n`. -/
def matrixUnitaryEuclideanMap {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℝ (MatrixRealIndex n) →ₗ[ℝ] EuclideanSpace ℝ (MatrixRealIndex n) :=
  (WithLp.linearEquiv 2 ℝ (MatrixRealIndex n → ℝ)).symm.toLinearMap.comp
    ((matrixUnitaryRealMap U).toLinearMap.comp
      (WithLp.linearEquiv 2 ℝ (MatrixRealIndex n → ℝ)).toLinearMap)

/-- Conjugation by a unitary `U` in real entry coordinates, as a linear isometry. -/
def matrixUnitaryEuclideanIsometry {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    EuclideanSpace ℝ (MatrixRealIndex n) →ₗᵢ[ℝ] EuclideanSpace ℝ (MatrixRealIndex n) where
  toLinearMap := matrixUnitaryEuclideanMap U
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    exact matrixUnitaryRealMap_sum_sq U hU (WithLp.ofLp x)

/-- Conjugation by a unitary `U` in real entry coordinates, as a linear isometry equivalence. -/
def matrixUnitaryEuclideanEquiv {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    EuclideanSpace ℝ (MatrixRealIndex n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (MatrixRealIndex n) :=
  LinearIsometryEquiv.ofSurjective (matrixUnitaryEuclideanIsometry U hU)
    ((LinearMap.injective_iff_surjective).mp (matrixUnitaryEuclideanIsometry U hU).injective)

theorem matrixUnitaryEuclideanEquiv_stdGaussian {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (stdGaussian (EuclideanSpace ℝ (MatrixRealIndex n))).map
      (matrixUnitaryEuclideanEquiv U hU) = stdGaussian (EuclideanSpace ℝ (MatrixRealIndex n)) :=
  stdGaussian_map _

theorem matrixUnitaryRealMap_standard {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (Measure.pi (fun _ : MatrixRealIndex n => gaussianReal 0 1)).map
      (matrixUnitaryRealMap U) = Measure.pi (fun _ : MatrixRealIndex n => gaussianReal 0 1) := by
  let P := Measure.pi (fun _ : MatrixRealIndex n => gaussianReal 0 1)
  let E := matrixUnitaryEuclideanEquiv U hU
  have hm : ((P.map (WithLp.toLp 2)).map E).map WithLp.ofLp =
      P.map (matrixUnitaryRealMap U) := by
    rw [Measure.map_map E.continuous.measurable (by fun_prop),
      Measure.map_map (by fun_prop) (E.continuous.measurable.comp (by fun_prop))]
    rfl
  have hback : (stdGaussian (EuclideanSpace ℝ (MatrixRealIndex n))).map WithLp.ofLp = P := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
    change Measure.map id P = P
    exact Measure.map_id
  rw [map_pi_eq_stdGaussian, matrixUnitaryEuclideanEquiv_stdGaussian U hU, hback] at hm
  exact hm.symm

theorem matrixGaussianPi_scale (n : ℕ) (v : ℝ≥0) :
    MeasurePreserving (fun x : MatrixRealIndex n → ℝ => Real.sqrt (v : ℝ) • x)
      (Measure.pi (fun _ : MatrixRealIndex n => gaussianReal 0 1))
      (Measure.pi (fun _ : MatrixRealIndex n => gaussianReal 0 v)) := by
  have hp : MeasurePreserving (fun x : ℝ => Real.sqrt (v : ℝ) * x)
      (gaussianReal 0 1) (gaussianReal 0 v) := by
    refine ⟨by fun_prop, ?_⟩
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply NNReal.coe_injective
      simp [Real.sq_sqrt v.coe_nonneg]
  exact measurePreserving_pi _ _ (fun _ => hp)

theorem matrixUnitaryRealMap_gaussian {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (v : ℝ≥0) :
    (Measure.pi (fun _ : MatrixRealIndex n => gaussianReal 0 v)).map
      (matrixUnitaryRealMap U) = Measure.pi (fun _ : MatrixRealIndex n => gaussianReal 0 v) := by
  let P := Measure.pi (fun _ : MatrixRealIndex n => gaussianReal 0 1)
  let S := fun x : MatrixRealIndex n → ℝ => Real.sqrt (v : ℝ) • x
  have hscale := (matrixGaussianPi_scale n v).map_eq
  have he : matrixUnitaryRealMap U ∘ S = S ∘ matrixUnitaryRealMap U := by
    funext x
    exact (matrixUnitaryRealMap U).map_smul _ x
  rw [← hscale, Measure.map_map (matrixUnitaryRealMap U).continuous.measurable (by fun_prop),
    he, ← Measure.map_map (by fun_prop) (matrixUnitaryRealMap U).continuous.measurable,
    matrixUnitaryRealMap_standard U hU]

/-- Unitary conjugation `A ↦ U A Uᴴ` on matrix coordinates, as a continuous real-linear map. -/
def matrixUnitaryConjugation {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n → Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ) :=
  (matrixRealCoordinates n).toContinuousLinearMap.comp
    ((matrixUnitaryRealMap U).comp (matrixRealCoordinates n).symm.toContinuousLinearMap)

theorem matrixUnitaryConjugation_apply {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (A : Fin n → Fin n → ℂ) :
    matrixUnitaryConjugation U A = U * Matrix.of A * Uᴴ := by
  simp only [matrixUnitaryConjugation, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, matrixUnitaryRealMap_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  exact (matrixRealCoordinates n).apply_symm_apply (U * Matrix.of A * Uᴴ)

theorem matrixGaussianMeasure_unitary_conjugation {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (matrixGaussianMeasure n).map (matrixUnitaryConjugation U) = matrixGaussianMeasure n := by
  have hp := (matrixRealCoordinates_measurePreserving n).map_eq
  have he : matrixUnitaryConjugation U ∘ matrixRealCoordinates n =
      matrixRealCoordinates n ∘ matrixUnitaryRealMap U := by
    funext x
    simp [matrixUnitaryConjugation]
  change (matrixGaussianMeasure n : Measure (Fin n → Fin n → ℂ)).map
    (matrixUnitaryConjugation U) = _
  rw [← hp]
  erw [Measure.map_map (matrixUnitaryConjugation U).continuous.measurable
    (matrixRealCoordinates n).continuous.measurable]
  rw [he, ← Measure.map_map (matrixRealCoordinates n).continuous.measurable
      (matrixUnitaryRealMap U).continuous.measurable,
    matrixUnitaryRealMap_gaussian U hU]
  rfl

end
end GinibrePoincare
