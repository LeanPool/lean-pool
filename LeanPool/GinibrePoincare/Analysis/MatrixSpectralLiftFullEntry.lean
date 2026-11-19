/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralLiftFullEntry.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralLiftEntryAE
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevLift
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevLocalIntegrability

/-!
# Matrix spectral lift full entry

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixEntryFullSpectralLift_derivative_locallyIntegrable`.
-/

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The full symmetric spectral lift of `F`, read in the configuration coordinates given by the
entry labelling `e`. -/
def matrixEntryFullSpectralLift {n m : ℕ} (e : Fin m ≃ Fin n × Fin n)
    (F : (Fin n → ℂ) → ℝ) : Configuration m → ℝ :=
  fun x => matrixFullSymmetricSpectralLift n F (Matrix.of (matrixComplexEntryEquiv e x))

theorem matrixEntryFullSpectralLift_derivative_eq_simple {n m : ℕ}
    (e : Fin m ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (x : Configuration m) (hx : (Matrix.of (matrixComplexEntryEquiv e x)).charpoly.Separable)
    (i : Fin m × Fin 2) :
    fderiv ℝ (matrixEntryFullSpectralLift e F) x (ginibreCoordinateDirection i) =
      matrixEntryIntrinsicSpectralGradient e F x i := by
  have hf := matrixFullSymmetricSpectralLift_differentiableAt n (matrixComplexEntryEquiv e x) hx F
      hF hsym
  have hc := hf.hasFDerivAt.comp x (matrixComplexEntryEquiv e).hasFDerivAt
  change (fderiv ℝ ((fun A : MatrixRealSpace n => matrixFullSymmetricSpectralLift n F (Matrix.of A))
      ∘
    matrixComplexEntryEquiv e) x) (ginibreCoordinateDirection i) = _
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [matrixComplexEntryEquiv_direction]
  have he := (matrixFullSymmetricSpectralLift_eventually_eq_simple n (matrixComplexEntryEquiv e x)
      hx F hsym).fderiv_eq
    (𝕜 := ℝ)
  rw [he]
  rfl

theorem matrixEntryFullSpectralLift_derivative_ae {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z) (i : Fin m × Fin 2) :
    (fun x => fderiv ℝ (matrixEntryFullSpectralLift e F) x (ginibreCoordinateDirection i))
      =ᵐ[matrixEntryGaussianMeasure e] (fun x => matrixEntryIntrinsicSpectralGradient e F x i) := by
  filter_upwards [(matrixComplexEntryEquiv_gaussian_preserving hn e).quasiMeasurePreserving.ae
    (matrixGaussian_charpoly_separable_ae n)] with x hx
  exact matrixEntryFullSpectralLift_derivative_eq_simple e F hF hsym x hx i

theorem matrixEntryFullSpectralLift_derivative_memLp {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) (i : Fin m × Fin
        2) :
    MemLp (fun x => fderiv ℝ (matrixEntryFullSpectralLift e F) x (ginibreCoordinateDirection i)) 2
      (matrixEntryGaussianMeasure e) := by
  have hvec := matrixEntryIntrinsicSpectralGradient_memLp hn e F hF hsym hE
  have hscalar := (memLp_piLp_iff.mp hvec) i
  exact hscalar.ae_eq (matrixEntryFullSpectralLift_derivative_ae hn e F hF hsym i).symm

theorem matrixEntryFullSpectralLift_derivative_locallyIntegrable {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) (i : Fin m × Fin
        2) :
    LocallyIntegrable (fun x => fderiv ℝ (matrixEntryFullSpectralLift e F) x
        (ginibreCoordinateDirection i)) volume := by
  let := matrixEntryGaussianMeasure_isProbability hn e
  have hi := (matrixEntryFullSpectralLift_derivative_memLp hn e F hF hsym hE i).integrable (by
      norm_num)
  rw [matrixEntryGaussianMeasure_eq_real_density e] at hi
  exact positive_density_integrable_locallyIntegrable volume (matrixEntryGaussianDensityReal e) _
    (matrixEntryGaussianDensityReal_continuous e) (matrixEntryGaussianDensityReal_pos hn e) hi

end
end GinibrePoincare
