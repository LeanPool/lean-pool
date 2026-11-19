/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralLiftGradientLp.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralLiftLSITransport

/-!
# Matrix spectral lift gradient lp

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSpectralLift_gradient_memLp`.
-/

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section

/-- Finite actual overlap integral gives genuine L2 integrability of every real
matrix-entry derivative of the intrinsic spectral lift. -/
theorem matrixSpectralLift_gradient_memLp {n : ℕ}
    (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n))
    (i : MatrixRealIndex n) :
    MemLp (fun A : MatrixRealSpace n => fderiv ℝ (matrixSymmetricLift n F) A
      (matrixRealCoordinates n (Pi.single i 1))) 2 (matrixGaussianMeasure n) := by
  have hg : Integrable (matrixRealGradientEnergy n (matrixSymmetricLift n F))
      (matrixGaussianMeasure n) := by
    apply (hE.const_mul 4).congr
    filter_upwards [matrixGaussian_charpoly_separable_ae n] with A hA
    exact (matrixSymmetricLift_energy n A hA F hF hsym).symm
  have hd : Measurable (fun A : MatrixRealSpace n => fderiv ℝ (matrixSymmetricLift n F) A
      (matrixRealCoordinates n (Pi.single i 1))) := by
    have hm := measurable_fderiv ℝ (matrixSymmetricLift n F)
    fun_prop
  apply (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).mpr
  apply hg.mono' (hd.pow_const 2).aestronglyMeasurable
  apply ae_of_all (matrixGaussianMeasure n)
  intro A
  change ‖(fderiv ℝ (matrixSymmetricLift n F) A
    (matrixRealCoordinates n (Pi.single i 1))) ^ 2‖ ≤
      matrixRealGradientEnergy n (matrixSymmetricLift n F) A
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (fderiv ℝ (matrixSymmetricLift n F) A
    (matrixRealCoordinates n (Pi.single i 1))))]
  unfold matrixRealGradientEnergy directionalEnergy
  exact Finset.single_le_sum (fun j hj => sq_nonneg (fderiv ℝ (matrixSymmetricLift n F) A
    (matrixRealCoordinates n (Pi.single j 1)))) (Finset.mem_univ i)

end
end GinibrePoincare
