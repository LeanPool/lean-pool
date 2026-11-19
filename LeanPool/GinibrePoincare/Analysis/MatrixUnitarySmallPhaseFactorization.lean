/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixUnitarySmallPhaseFactorization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixUnitaryCenteredPhaseFactorization

/-!
# Matrix unitary small phase factorization

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixUnitary_local_phase_factorization_small`, the identity-centered case
of `matrixUnitary_centered_phase_factorization`.
-/

@[expose] public section

open Matrix NormedSpace Filter
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

theorem matrixUnitary_local_phase_factorization_small (n : ℕ)
    (N : Set (MatrixSkewCoordinates n)) (hN : N ∈ 𝓝 0) :
    ∀ᶠ U : Matrix (Fin n) (Fin n) ℂ in 𝓝 1,
      U ∈ Matrix.unitaryGroup (Fin n) ℂ →
        ∃ p : MatrixSkewCoordinates n, p ∈ N ∧ matrixUnitaryPhaseParameter n p = U := by
  have hden : IsUnit (matrixUnitaryPhaseParameter n 0 + 1) := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ?_)
    rw [matrixUnitaryPhaseParameter_zero, ← two_smul ℂ (1 : Matrix (Fin n) (Fin n) ℂ),
      Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (by norm_num)
  have h := matrixUnitary_centered_phase_factorization n 0
    (matrixUnitaryPhaseLocalChart_zero_mem_source n) hden N hN
  rwa [matrixUnitaryPhaseParameter_zero] at h

end
end GinibrePoincare
