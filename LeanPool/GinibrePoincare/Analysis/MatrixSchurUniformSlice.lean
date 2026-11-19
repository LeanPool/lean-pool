/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurUniformSlice.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixUnitaryFlagSlice
public import LeanPool.GinibrePoincare.Analysis.MatrixSchurUniqueness

/-!
# Matrix Schur uniform slice

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSchur_uniform_ordered_slice`.
-/

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

/-- One unitary-coordinate neighborhood works for all triangular matrices and all
strict upper entries. This is stronger than an inverse-function neighborhood of one matrix. -/
theorem matrixSchur_uniform_ordered_slice (n : ℕ) :
    ∃ V : Set (SchurLowerIndex n → ℂ), V ∈ 𝓝 0 ∧
      ∀ x ∈ V, ∀ y ∈ V, ∀ A B : Matrix (Fin n) (Fin n) ℂ,
        (∀ i j, j < i → A i j = 0) → (∀ i j, j < i → B i j = 0) →
        (∀ i, A i i = B i i) → Function.Injective (fun i => A i i) →
        matrixSchurExponentialFrame n x * A * (matrixSchurExponentialFrame n x)ᴴ =
          matrixSchurExponentialFrame n y * B * (matrixSchurExponentialFrame n y)ᴴ →
        x = y ∧ A = B := by
  obtain ⟨V, hV, hflag⟩ := matrixUnitary_lower_flag_slice n
  refine ⟨V, hV, ?_⟩
  intro x hx y hy A B hA hB hd hinj he
  let Q := matrixSchurExponentialFrame n
  have hphase := schur_ordered_representation_unique_phases
    (Q x * A * (Q x)ᴴ) A B (Q x) (Q y)
    (matrixSchurExponentialFrame_unitary n x) (matrixSchurExponentialFrame_unitary n y)
    hA hB hd hinj rfl he
  have hxy : x = y := hflag x hx y hy (by
    intro i j hij
    rw [hphase]
    simp [hij])
  refine ⟨hxy, ?_⟩
  rw [← hxy] at he
  have h1 : (Q x)ᴴ * Q x = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (matrixSchurExponentialFrame_unitary n x)
  have hc : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      (Q x)ᴴ * (Q x * M * (Q x)ᴴ) * Q x = M := by
    intro M
    calc
      _ = ((Q x)ᴴ * Q x) * M * ((Q x)ᴴ * Q x) := by noncomm_ring
      _ = M := by rw [h1]; simp
  have hm := congrArg (fun M => (Q x)ᴴ * M * Q x) he
  rw [hc, hc] at hm
  exact hm

end
end GinibrePoincare
