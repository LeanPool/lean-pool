/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixUnitaryDiagonalPhase.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixUnitarySmallPhaseFactorization

/-!
# Matrix unitary diagonal phase

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixUnitary_diagonal_phase_small`.
-/

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

theorem matrixUnitaryPhaseParameter_diagonal_lower_zero (n : ℕ)
    (p : MatrixSkewCoordinates n)
    (hp : p.1 ∈ (matrixUnitaryLowerLocalChart n).source)
    (hd : ∀ i j, i ≠ j → matrixUnitaryPhaseParameter n p i j = 0) : p.1 = 0 := by
  let R := exp (matrixSkewDiagonalCLM n p.2)
  have hR : R = Matrix.diagonal (exp (fun i => (p.2 i : ℂ) * Complex.I)) := by
    dsimp only [R]
    rw [matrixSkewDiagonalCLM_apply, Matrix.exp_diagonal]
  have hunit : R ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    have hh := matrixUnitaryPhaseParameter_unitary n ((0 : SchurLowerIndex n → ℂ), p.2)
    simpa [matrixUnitaryPhaseParameter, ← schurSkewCLM_apply, map_zero, exp_zero] using hh
  have hRR : R * Rᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hunit
  have he : exp (schurSkewCombination p.1) = matrixUnitaryPhaseParameter n p * Rᴴ := by
    change _ = (exp (schurSkewCombination p.1) * R) * Rᴴ
    rw [Matrix.mul_assoc, hRR, Matrix.mul_one]
  apply matrixUnitaryLowerLocalChart_diagonal_iff_zero n p.1 hp
  intro i j hij
  rw [he, hR, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, hd i j hij, zero_mul]

/-- Diagonal unitary matrices near the identity have arbitrarily small diagonal phase
coordinates, with no residual lower skew coordinates. -/
theorem matrixUnitary_diagonal_phase_small (n : ℕ)
    (W : Set (Fin n → ℝ)) (hW : W ∈ 𝓝 0) :
    ∀ᶠ U : Matrix (Fin n) (Fin n) ℂ in 𝓝 1,
      U ∈ Matrix.unitaryGroup (Fin n) ℂ →
      (∀ i j, i ≠ j → U i j = 0) →
      ∃ d ∈ W, U = exp (matrixSkewDiagonalCLM n d) := by
  let N := (matrixUnitaryLowerLocalChart n).source ×ˢ W
  have hN : N ∈ 𝓝 (0 : MatrixSkewCoordinates n) :=
    prod_mem_nhds
      ((matrixUnitaryLowerLocalChart n).open_source.mem_nhds
        (matrixUnitaryLowerLocalChart_zero_mem_source n)) hW
  filter_upwards [matrixUnitary_local_phase_factorization_small n N hN] with U hU
  intro hunit hdiag
  obtain ⟨p, hp, he⟩ := hU hunit
  have hzero : p.1 = 0 := matrixUnitaryPhaseParameter_diagonal_lower_zero n p hp.1
    (by simpa only [he] using hdiag)
  refine ⟨p.2, hp.2, ?_⟩
  rw [← he, matrixUnitaryPhaseParameter, hzero]
  simp [← schurSkewCLM_apply, map_zero, exp_zero]

end
end GinibrePoincare
