/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixRealDifferential.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralLiftDifferential

/-!
# Matrix real differential

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixLocalSpectralLift_wirtinger`.
-/

@[expose] public section

open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- The `i`-th Wirtinger coefficient `(L eᵢ - i L (i eᵢ)) / 2` of a real-linear functional `L`
on `ℂⁿ`. -/
def realDifferentialWirtinger {n : ℕ} (L : (Fin n → ℂ) →L[ℝ] ℝ) (i : Fin n) : ℂ :=
  ((L (Pi.single i 1) : ℂ) - Complex.I * (L (Pi.single i Complex.I) : ℂ)) / 2

/-- Every actual real differential on complex coordinates has the Wirtinger decomposition. -/
theorem realDifferentialWirtinger_apply {n : ℕ} (L : (Fin n → ℂ) →L[ℝ] ℝ)
    (z : Fin n → ℂ) : L z = 2 * (∑ i, realDifferentialWirtinger L i * z i).re := by
  classical
  have hz : z = ∑ i : Fin n,
      ((z i).re • (Pi.single i 1 : Fin n → ℂ) +
        (z i).im • (Pi.single i Complex.I : Fin n → ℂ)) := by
    ext j
    simp [Pi.single_apply, Complex.real_smul, Finset.sum_add_distrib]
  conv_lhs => rw [hz, map_sum]
  simp only [map_add, map_smul, smul_eq_mul, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [realDifferentialWirtinger, 
    Complex.mul_re, Complex.mul_im]
  ring

theorem matrixLocalSpectralLift_wirtinger (n : ℕ) (A H : GinibreMatrixCoordinates n)
    (labels : GinibreMatrixCoordinates n → Fin n → ℂ) (F : (Fin n → ℂ) → ℝ)
    (hs : (Matrix.of A).charpoly.Separable) (hd : DifferentiableAt ℂ labels A)
    (hF : DifferentiableAt ℝ F (labels A))
    (hr : ∀ᶠ B in nhds A, ∀ i, (Matrix.of B).charpoly.eval (labels B i) = 0) :
    fderiv ℝ (F ∘ labels) A H =
      2 * (∑ i, realDifferentialWirtinger (fderiv ℝ F (labels A)) i *
        Matrix.trace (matrixEigenvalueProjector n A (labels A i) * Matrix.of H)).re := by
  rw [matrixLocalSpectralLift_fderiv n A H labels F hs hd hF hr]
  exact realDifferentialWirtinger_apply _ _

end
end GinibrePoincare
