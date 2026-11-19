/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixGaussianLSI.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixGaussianMeasure
public import LeanPool.GinibrePoincare.Analysis.GaussianBlockLSI

/-!
# Matrix Gaussian LSI

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixRealCoordinates_direction`, `matrixGaussian_lsi_compactLipschitz`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Indices `(i, j, c)` of the real coordinates of an `n × n` complex matrix: row, column, and
real (`0`) or imaginary (`1`) part. -/
abbrev MatrixRealIndex (n : ℕ) := Σ _ : Fin n, Σ _ : Fin n, Fin 2

/-- The real-linear identification of real coordinate vectors indexed by `MatrixRealIndex n`
with `n × n` complex matrices, reading coordinates as real and imaginary parts of entries. -/
def matrixRealCoordinates (n : ℕ) :
    (MatrixRealIndex n → ℝ) ≃L[ℝ] (Fin n → Fin n → ℂ) :=
  (gaussianCurryEquiv (Fin n) (fun _ => Σ _ : Fin n, Fin 2)).trans
    (ContinuousLinearEquiv.piCongrRight (fun _ : Fin n =>
      (gaussianCurryEquiv (Fin n) (fun _ => Fin 2)).trans
        (ContinuousLinearEquiv.piCongrRight (fun _ : Fin n =>
          Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm))))

theorem matrixRealCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (matrixRealCoordinates n)
      (Measure.pi (fun _ : MatrixRealIndex n => gaussianReal 0 (realCoordinateVariance n)))
      (matrixGaussianMeasure n) := by
  let v := realCoordinateVariance n
  have hcomplex : MeasurePreserving Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 v))
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
    refine ⟨Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm.continuous.measurable, ?_⟩
    unfold complexCoordinateGaussianProbability
    simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pi]
    rfl
  have hinner := (measurePreserving_pi _ _ (fun _ : Fin n => hcomplex)).comp
    (gaussianCurry_measurePreserving (Fin n) (fun _ => Fin 2) v)
  exact (measurePreserving_pi _ _ (fun _ : Fin n => hinner)).comp
    (gaussianCurry_measurePreserving (Fin n) (fun _ => Σ _ : Fin n, Fin 2) v)

/-- The squared gradient norm of `F`, summing the squared derivatives of `F` along all real
matrix coordinate directions. -/
def matrixRealGradientEnergy (n : ℕ) (F : (Fin n → Fin n → ℂ) → ℝ) :
    (Fin n → Fin n → ℂ) → ℝ :=
  directionalEnergy (fun i : MatrixRealIndex n => matrixRealCoordinates n (Pi.single i 1)) F

theorem matrixRealCoordinates_direction (n : ℕ) (i j : Fin n) (k : Fin 2) :
    matrixRealCoordinates n (Pi.single ⟨i, ⟨j, k⟩⟩ 1) =
      Pi.single i (Pi.single j (if k = 0 then (1 : ℂ) else Complex.I)) := by
  classical
  funext a b
  fin_cases k <;>
    by_cases ha : a = i <;> by_cases hb : b = j <;>
    simp [matrixRealCoordinates, gaussianCurryEquiv, ContinuousLinearEquiv.piCongrRight,
      LinearEquiv.piCurry, Equiv.piCurry, Sigma.curry, ha, hb,
      Complex.basisOneI]

/-- Sharp LSI for the actual Gaussian matrix ensemble and compactly supported Lipschitz
matrix observables, in its real entry coordinates. -/
theorem matrixGaussian_lsi_compactLipschitz (n : ℕ) (hn : 0 < n)
    (F : (Fin n → Fin n → ℂ) → ℝ) {K : ℝ≥0}
    (hF : LipschitzWith K F) (hc : HasCompactSupport F) :
    squareEntropy (matrixGaussianMeasure n) F ≤
      (1 / (n : ℝ)) * ∫ A, matrixRealGradientEnergy n F A ∂matrixGaussianMeasure n := by
  classical
  let : Nonempty (MatrixRealIndex n) := ⟨⟨⟨0, hn⟩, ⟨⟨0, hn⟩, 0⟩⟩⟩
  let T := matrixRealCoordinates n
  have hp := matrixRealCoordinates_measurePreserving n
  have he := gaussianFiniteIndex_lsi_compactLipschitz (MatrixRealIndex n)
    (realCoordinateVariance n) (F ∘ T) (hF.comp T.lipschitzWith)
    (hc.comp_homeomorph T.toHomeomorph)
  have hent : squareEntropy (matrixGaussianMeasure n) F =
      squareEntropy (Measure.pi (fun _ : MatrixRealIndex n => gaussianReal 0
        (realCoordinateVariance n))) (F ∘ T) := by
    rw [← hp.map_eq]
    exact squareEntropy_map _ _ T.continuous.measurable.aemeasurable F
      (hF.continuous.pow 2).aestronglyMeasurable
      (continuous_square_mul_log hF.continuous).aestronglyMeasurable
  have hm : Measurable (matrixRealGradientEnergy n F) := by
    unfold matrixRealGradientEnergy directionalEnergy
    exact Finset.measurable_sum _ fun i _ => (measurable_fderiv_apply_const ℝ F _).pow_const 2
  have henergy (x : MatrixRealIndex n → ℝ) :
      directionalEnergy (fun i : MatrixRealIndex n => Pi.single i 1) (F ∘ T) x =
        matrixRealGradientEnergy n F (T x) := by
    unfold matrixRealGradientEnergy directionalEnergy
    rw [ContinuousLinearEquiv.comp_right_fderiv]
    rfl
  have hi : (∫ A, matrixRealGradientEnergy n F A ∂matrixGaussianMeasure n) =
      ∫ x, directionalEnergy (fun i : MatrixRealIndex n => Pi.single i 1) (F ∘ T) x
        ∂Measure.pi (fun _ : MatrixRealIndex n => gaussianReal 0 (realCoordinateVariance n)) := by
    change (∫ A : Fin n → Fin n → ℂ, matrixRealGradientEnergy n F A
      ∂(matrixGaussianMeasure n : Measure (Fin n → Fin n → ℂ))) = _
    rw [← hp.map_eq]
    erw [integral_map T.continuous.measurable.aemeasurable hm.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (henergy x).symm)
  have hv : 2 * (realCoordinateVariance n : ℝ) = 1 / (n : ℝ) := by
    simp [realCoordinateVariance, NNReal.coe_inv, NNReal.coe_mul]
    field_simp
  rw [hent, hi, ← hv]
  exact he

end
end GinibrePoincare
