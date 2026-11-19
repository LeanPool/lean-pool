/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianGenerator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianLaplacian

/-! Exact Hamiltonian generator and the uniform Lyapunov generator bound. -/

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- Squared Euclidean gradient, in the actual real coordinate directions. -/
def ginibreHamiltonianGradientNormSq (n : ℕ) (z : Configuration n) : ℝ :=
  ∑ j : Fin n,
    ((fderiv ℝ (ginibreHamiltonian n) z (realCoordinateDirection j))^2 +
    (fderiv ℝ (ginibreHamiltonian n) z (imaginaryCoordinateDirection j))^2)

theorem ginibreHamiltonianGradientNormSq_nonneg (n : ℕ) (z : Configuration n) :
    0 ≤ ginibreHamiltonianGradientNormSq n z := by
  exact Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem ginibrePregenerator_hamiltonian {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z) :
    ginibrePregenerator n (ginibreHamiltonian n) z =
      4*(n : ℝ) - ginibreHamiltonianGradientNormSq n z/(n : ℝ) := by
  rw [ginibrePregenerator_eq_laplacian_sub_drift,
    ginibreHamiltonian_laplacian z hz]
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs : (∑ j : Fin n,
      (ginibreRealDriftCoordinate n j z *
        fderiv ℝ (ginibreHamiltonian n) z (realCoordinateDirection j) +
      ginibreImagDriftCoordinate n j z *
        fderiv ℝ (ginibreHamiltonian n) z (imaginaryCoordinateDirection j))) =
      ginibreHamiltonianGradientNormSq n z/(n : ℝ) := by
    unfold ginibreHamiltonianGradientNormSq
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    rw [fderiv_ginibreHamiltonian_realCoordinate hn z hz,
      fderiv_ginibreHamiltonian_imaginaryCoordinate hn z hz]
    field_simp [hne]
  rw [hs]
  congr 1
  field_simp [hne]

/-- The real generator at the paper's speed parameter. -/
def ginibreRealPaperSpeedGenerator (n : ℕ) (α : ℝ)
    (f : Configuration n → ℝ) (z : Configuration n) : ℝ :=
  (α/(n : ℝ))*ginibrePregenerator n f z

theorem ginibreRealPaperSpeedGenerator_hamiltonian {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) :
    ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n) z =
      4*α - (α/(n : ℝ)^2)*ginibreHamiltonianGradientNormSq n z := by
  unfold ginibreRealPaperSpeedGenerator
  rw [ginibrePregenerator_hamiltonian hn z hz]
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hne]

theorem ginibreRealPaperSpeedGenerator_hamiltonian_le {n : ℕ} (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (z : Configuration n) (hz : CollisionFree z) :
    ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n) z ≤ 4*α := by
  rw [ginibreRealPaperSpeedGenerator_hamiltonian hn α z hz]
  exact sub_le_self _ (mul_nonneg (div_nonneg hα (sq_nonneg _))
    (ginibreHamiltonianGradientNormSq_nonneg n z))

end
end GinibrePoincare
