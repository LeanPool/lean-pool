/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralLiftPoincareFinite.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixOverlapGradientIntegrability
public import LeanPool.GinibrePoincare.Analysis.GinibreC1WeakPoincare

/-! # Poincaré from finite matrix overlap energy

First derive L² membership of the ordinary Ginibre gradient from the overlap
bound. Apply the symmetric C¹ finite-energy Poincaré theorem, then insert the
factor-four overlap bound. Multiplying by the Ginibre coefficient 1/(2n)
gives the matrix coefficient 2/n. This route passes through the Ginibre weak
domain; AlternativeMatrixPoincare gives the independent Gaussian matrix route.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The matrix-lift Poincaré inequality for every symmetric C¹ observable
with genuine finite L² value and finite overlap energy. The spectral law,
weak-domain membership, and overlap domination are derived internally. -/
theorem matrixSpectralLift_finite_overlap_poincare {n : ℕ} (hn : 0 < n)
    (F : Configuration n → ℝ) (hF : ContDiff ℝ 1 F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (hFL2 : MemLp F 2 (ginibreMeasure n))
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) :
    smoothGinibreVariance n F ≤
      (2 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  have hd := hF.differentiable (by norm_num)
  have hgl := matrixOverlap_finite_gradient_memLp hn F hd hsym hE
  have hpi := ginibre_C1_finite_energy_poincare hn F hF hsym hFL2 hgl
  have hgrad := (matrixOverlap_finite_gradient_energy hn F hd hsym hE).2
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  calc
    smoothGinibreVariance n F ≤
        (1 / (2 * (n : ℝ))) * ∫ z, realGradientNormSq F z ∂ginibreMeasure n := hpi
    _ ≤ (1 / (2 * (n : ℝ))) *
        (4 * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n) :=
      mul_le_mul_of_nonneg_left hgrad (by positivity)
    _ = _ := by field_simp; ring

end
end GinibrePoincare
