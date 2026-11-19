/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSymmetricLift.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixLabelPermutation
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralLaw
public import LeanPool.GinibrePoincare.Analysis.MatrixLiftEnergy

/-!
# Matrix symmetric lift

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSymmetricLift_differentiableAt`,
`matrixSpectral_overlap_lsi_compactLipschitz`.
-/

@[expose] public section

open Filter Matrix MeasureTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The spectral lift `F ∘ matrixMeasurableEigenvalues n` of a function of the eigenvalues. -/
def matrixSymmetricLift (n : ℕ) (F : (Fin n → ℂ) → ℝ) : GinibreMatrixCoordinates n → ℝ :=
  F ∘ matrixMeasurableEigenvalues n

/-- Despite the measurable labeling's possible jumps, a symmetric spectral observable
has a genuine differentiable matrix lift at every simple-spectrum matrix. -/
theorem matrixSymmetricLift_differentiableAt (n : ℕ) (A : GinibreMatrixCoordinates n)
    (hs : (Matrix.of A).charpoly.Separable) (F : (Fin n → ℂ) → ℝ)
    (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    DifferentiableAt ℝ (matrixSymmetricLift n F) A := by
  obtain ⟨U, labels, ho, hA, hd, hr⟩ :=
    matrixSimpleSpectrum_exists_smooth_local_labeling n A hs
  have hdA : DifferentiableAt ℂ labels A :=
    ((hd A hA).contDiffAt (ho.mem_nhds hA)).differentiableAt (by norm_num)
  have heq : matrixSymmetricLift n F =ᶠ[nhds A] F ∘ labels := by
    filter_upwards [ho.mem_nhds hA] with B hB
    have hlabels := hr B hB
    have hsB := matrix_injective_full_roots_separable n (Matrix.of B) (labels B)
      hlabels.1 hlabels.2
    have hcanon := matrixMeasurableEigenvalues_spec n B hsB
    exact matrixSimpleSpectrum_symmetric_value n (Matrix.of B) hsB
      (matrixMeasurableEigenvalues n B) (labels B) hcanon.1 hlabels.1
      hcanon.2 hlabels.2 F hsym
  exact ((hF (labels A)).comp A (hdA.restrictScalars ℝ)).congr_of_eventuallyEq heq

/-- The overlap formula for the intrinsic lift, expressed in the chosen measurable labels. -/
theorem matrixSymmetricLift_energy (n : ℕ) (A : GinibreMatrixCoordinates n)
    (hs : (Matrix.of A).charpoly.Separable) (F : (Fin n → ℂ) → ℝ)
    (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    matrixRealGradientEnergy n (matrixSymmetricLift n F) A =
      4 * matrixOverlapEnergy
        (fun i => matrixEigenvalueProjector n A (matrixMeasurableEigenvalues n A i))
        (realDifferentialWirtinger (fderiv ℝ F (matrixMeasurableEigenvalues n A))) := by
  classical
  obtain ⟨U, labels, ho, hA, hd, hr⟩ :=
    matrixSimpleSpectrum_exists_smooth_local_labeling n A hs
  have hdA : DifferentiableAt ℂ labels A :=
    ((hd A hA).contDiffAt (ho.mem_nhds hA)).differentiableAt (by norm_num)
  have hcanon := matrixMeasurableEigenvalues_spec n A hs
  obtain ⟨e, he⟩ := matrixSimpleSpectrum_labels_permutation n (Matrix.of A) hs
    (labels A) (matrixMeasurableEigenvalues n A) (hr A hA).1 hcanon.1
    (hr A hA).2 hcanon.2
  let lab := fun B i => labels B (e i)
  have hbase : lab A = matrixMeasurableEigenvalues n A := funext fun i => (he i).symm
  have hdl : DifferentiableAt ℂ lab A := differentiableAt_pi.mpr
    fun i => (differentiableAt_pi.mp hdA) (e i)
  have hroot : ∀ᶠ B in nhds A, ∀ i, (Matrix.of B).charpoly.eval (lab B i) = 0 := by
    filter_upwards [ho.mem_nhds hA] with B hB
    exact fun i => (hr B hB).2 (e i)
  have heq : matrixSymmetricLift n F =ᶠ[nhds A] F ∘ lab := by
    filter_upwards [ho.mem_nhds hA] with B hB
    have hl := hr B hB
    have hsB := matrix_injective_full_roots_separable n (Matrix.of B) (labels B) hl.1 hl.2
    have hcB := matrixMeasurableEigenvalues_spec n B hsB
    exact matrixSimpleSpectrum_symmetric_value n (Matrix.of B) hsB
      (matrixMeasurableEigenvalues n B) (lab B) hcB.1 (hl.1.comp e.injective)
      hcB.2 (fun i => hl.2 (e i)) F hsym
  have hdEq := heq.fderiv_eq (𝕜 := ℝ)
  unfold matrixRealGradientEnergy directionalEnergy
  rw [hdEq]
  change matrixRealGradientEnergy n (F ∘ lab) A = _
  rw [matrixLocalSpectralLift_energy n A lab F hs hdl (hF (lab A)) hroot, hbase]

/-- The overlap energy at `A` built from the eigenprojectors of `A` at its labelled eigenvalues
and the Wirtinger coefficients of `DF` at the eigenvalue vector. -/
def matrixSpectralOverlapEnergy (n : ℕ) (F : (Fin n → ℂ) → ℝ)
    (A : GinibreMatrixCoordinates n) : ℝ :=
  matrixOverlapEnergy
    (fun i => matrixEigenvalueProjector n A (matrixMeasurableEigenvalues n A i))
    (realDifferentialWirtinger (fderiv ℝ F (matrixMeasurableEigenvalues n A)))

/-- The actual overlap LSI under the Gaussian matrix spectral pushforward. The matrix
lift has the ordinary regularity needed by the sharp Gaussian LSI. -/
theorem matrixSpectral_overlap_lsi_compactLipschitz (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    {K : ℝ≥0} (hLip : LipschitzWith K (matrixSymmetricLift n F))
    (hc : HasCompactSupport (matrixSymmetricLift n F)) :
    squareEntropy (matrixSpectralMeasure n) F ≤
      (4 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  have hg := matrixGaussian_lsi_compactLipschitz n hn (matrixSymmetricLift n F) hLip hc
  have hent : squareEntropy (matrixSpectralMeasure n) F =
      squareEntropy (matrixGaussianMeasure n) (matrixSymmetricLift n F) := by
    unfold matrixSpectralMeasure matrixSymmetricLift
    exact squareEntropy_map _ _ (matrixMeasurableEigenvalues_measurable n).aemeasurable F
      (hF.continuous.pow 2).aestronglyMeasurable
      (continuous_square_mul_log hF.continuous).aestronglyMeasurable
  have he : (∫ A, matrixRealGradientEnergy n (matrixSymmetricLift n F) A
      ∂matrixGaussianMeasure n) =
        4 * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
    erw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [matrixGaussian_charpoly_separable_ae n] with A hA
    exact matrixSymmetricLift_energy n A hA F hF hsym
  rw [hent]
  rw [he] at hg
  convert hg using 1
  ring

end
end GinibrePoincare
