/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralLiftEntryLp.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralLiftGradientLp
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevDensityTransport
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevDirections

/-!
# Matrix spectral lift entry lp

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixEntryIntrinsicSpectralGradient_memLp`,
`matrixEntryIntrinsicSpectralValue_memLp`.
-/

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section

/-- The gradient of the spectral lift `matrixSymmetricLift n F`, read in the configuration
coordinates given by the entry labelling `e`, with one component per real matrix coordinate. -/
def matrixEntryIntrinsicSpectralGradient {n m : ℕ} (e : Fin m ≃ Fin n × Fin n)
    (F : (Fin n → ℂ) → ℝ) (x : Configuration m) : EuclideanSpace ℝ (Fin m × Fin 2) :=
  WithLp.toLp 2 (fun i => fderiv ℝ (matrixSymmetricLift n F) (matrixComplexEntryEquiv e x)
    (matrixRealCoordinates n (Pi.single (matrixEntryRealIndexEquiv e i) 1)))

theorem matrixEntryIntrinsicSpectralGradient_memLp {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) :
    MemLp (matrixEntryIntrinsicSpectralGradient e F) 2 (matrixEntryGaussianMeasure e) := by
  apply memLp_piLp_iff.mpr
  intro i
  exact (matrixSpectralLift_gradient_memLp F hF hsym hE (matrixEntryRealIndexEquiv e
      i)).comp_measurePreserving
    (matrixComplexEntryEquiv_gaussian_preserving hn e)

theorem matrixEntryIntrinsicSpectralValue_memLp {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Measurable F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (hFL2 : MemLp F 2 (ginibreMeasure n)) :
    MemLp (fun x => matrixSymmetricLift n F (matrixComplexEntryEquiv e x)) 2
      (matrixEntryGaussianMeasure e) :=
  ((matrixSpectralLift_memLp_two_iff hn F hF hsym).mpr hFL2).comp_measurePreserving
    (matrixComplexEntryEquiv_gaussian_preserving hn e)

end
end GinibrePoincare
