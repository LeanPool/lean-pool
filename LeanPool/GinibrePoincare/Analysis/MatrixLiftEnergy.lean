/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixLiftEnergy.lean.
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
public import LeanPool.GinibrePoincare.Analysis.MatrixRealDifferential

/-!
# Matrix lift energy

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixLocalSpectralLift_energy`.
-/

@[expose] public section

open Matrix
open scoped BigOperators Topology
namespace GinibrePoincare
noncomputable section

theorem matrixTrace_entry_direction {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) (z : ℂ) :
    trace (C * Matrix.of (Pi.single i (Pi.single j z))) = C j i * z := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, Pi.single_apply, ite_apply, eq_comm]

theorem matrixTrace_real_coordinate_energy (n : ℕ) (C : Matrix (Fin n) (Fin n) ℂ) :
    (∑ p : MatrixRealIndex n,
      (2 * (trace (C * Matrix.of (matrixRealCoordinates n (Pi.single p 1)))).re) ^ 2) =
      4 * matrixHSNormSq C := by
  classical
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma, Fin.sum_univ_two, matrixRealCoordinates_direction,
    matrixTrace_entry_direction]
  rw [matrixHSNormSq_eq_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [Complex.normSq_apply]
  ring

/-- The exact overlap energy of an actual differentiable spectral lift. -/
theorem matrixLocalSpectralLift_energy (n : ℕ) (A : GinibreMatrixCoordinates n)
    (labels : GinibreMatrixCoordinates n → Fin n → ℂ) (F : (Fin n → ℂ) → ℝ)
    (hs : (Matrix.of A).charpoly.Separable) (hd : DifferentiableAt ℂ labels A)
    (hF : DifferentiableAt ℝ F (labels A))
    (hr : ∀ᶠ B in nhds A, ∀ i, (Matrix.of B).charpoly.eval (labels B i) = 0) :
    matrixRealGradientEnergy n (F ∘ labels) A =
      4 * matrixOverlapEnergy (fun i => matrixEigenvalueProjector n A (labels A i))
        (realDifferentialWirtinger (fderiv ℝ F (labels A))) := by
  classical
  let P := fun i => matrixEigenvalueProjector n A (labels A i)
  let a := realDifferentialWirtinger (fderiv ℝ F (labels A))
  rw [matrixOverlapEnergy_eq_HS]
  unfold matrixRealGradientEnergy directionalEnergy
  have he (p : MatrixRealIndex n) :
      fderiv ℝ (F ∘ labels) A (matrixRealCoordinates n (Pi.single p 1)) =
        2 * (trace (matrixProjectorCombination P a *
          Matrix.of (matrixRealCoordinates n (Pi.single p 1)))).re := by
    rw [matrixLocalSpectralLift_wirtinger n A _ labels F hs hd hF hr]
    simp [P, a, matrixProjectorCombination, Matrix.sum_mul, 
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  simp_rw [he]
  exact matrixTrace_real_coordinate_energy n (matrixProjectorCombination P a)

end
end GinibrePoincare
