/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurOrderedSlice.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurUniformSlice
public import LeanPool.GinibrePoincare.Analysis.MatrixSchurSpectralObservable
public import LeanPool.GinibrePoincare.Analysis.MatrixLabelPermutation
public import Mathlib.Order.WellFounded

/-!
# Matrix Schur ordered slice

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSchur_uniform_sorted_slice`.
-/

@[expose] public section

open Matrix NormedSpace Filter Set Order
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

/-- The diagonal entries of `A` are strictly increasing in the lexicographic order on
`(re, im)`. -/
def matrixSchurOrderedDiagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  StrictMono (fun i => toLex ((A i i).re, (A i i).im))

theorem matrixSchurOrderedDiagonal_injective {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : matrixSchurOrderedDiagonal A) : Function.Injective (fun i => A i i) := by
  intro i j hij
  apply hA.injective
  exact congrArg (fun z : ℂ => toLex (z.re, z.im)) hij

theorem matrixSchurOrderedDiagonal_eq_of_charpoly {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0)
    (hoA : matrixSchurOrderedDiagonal A) (hoB : matrixSchurOrderedDiagonal B)
    (hp : A.charpoly = B.charpoly) : ∀ i, A i i = B i i := by
  have ha := matrixSchurOrderedDiagonal_injective hoA
  have hb := matrixSchurOrderedDiagonal_injective hoB
  have hra : ∀ i, A.charpoly.eval (A i i) = 0 := schur_diagonal_roots A hA
  have hrb : ∀ i, A.charpoly.eval (B i i) = 0 := by
    rw [hp]
    exact schur_diagonal_roots B hB
  have hs := matrix_injective_full_roots_separable n A (fun i => A i i) ha hra
  obtain ⟨e, he⟩ := matrixSimpleSpectrum_labels_permutation n A hs
    (fun i => A i i) (fun i => B i i) ha hb hra hrb
  let a : Fin n → ℝ ×ₗ ℝ := fun i => toLex ((A i i).re, (A i i).im)
  let b : Fin n → ℝ ×ₗ ℝ := fun i => toLex ((B i i).re, (B i i).im)
  have hb' : b = a ∘ e := by
    funext i
    dsimp [a, b]
    rw [he i]
  have hrange : Set.range a = Set.range b := by
    rw [hb', Set.range_comp]
    simp
  have heq : a = b := Set.range_injOn_strictMono_of_wellFoundedLT hoA hoB hrange
  intro i
  have hi := congrFun heq i
  apply Complex.ext
  · exact congrArg (fun p : ℝ ×ₗ ℝ => (ofLex p).1) hi
  · exact congrArg (fun p : ℝ ×ₗ ℝ => (ofLex p).2) hi

/-- Uniform injectivity of the ordered Schur slice, with no restriction on eigenvalue
size or strictly upper triangular entries. -/
theorem matrixSchur_uniform_sorted_slice (n : ℕ) :
    ∃ V : Set (SchurLowerIndex n → ℂ), V ∈ 𝓝 0 ∧
      ∀ x ∈ V, ∀ y ∈ V, ∀ A B : Matrix (Fin n) (Fin n) ℂ,
        (∀ i j, j < i → A i j = 0) → (∀ i j, j < i → B i j = 0) →
        matrixSchurOrderedDiagonal A → matrixSchurOrderedDiagonal B →
        matrixSchurExponentialFrame n x * A * (matrixSchurExponentialFrame n x)ᴴ =
          matrixSchurExponentialFrame n y * B * (matrixSchurExponentialFrame n y)ᴴ →
        x = y ∧ A = B := by
  obtain ⟨V, hV, huni⟩ := matrixSchur_uniform_ordered_slice n
  refine ⟨V, hV, ?_⟩
  intro x hx y hy A B hA hB hoA hoB he
  have hpa := matrix_charpoly_unitary_conjugation A (matrixSchurExponentialFrame n x)
    (matrixSchurExponentialFrame_unitary n x)
  have hpb := matrix_charpoly_unitary_conjugation B (matrixSchurExponentialFrame n y)
    (matrixSchurExponentialFrame_unitary n y)
  have hchar : A.charpoly = B.charpoly := by
    rw [← hpa, ← hpb, he]
  exact huni x hx y hy A B hA hB
    (matrixSchurOrderedDiagonal_eq_of_charpoly A B hA hB hoA hoB hchar)
    (matrixSchurOrderedDiagonal_injective hoA) he

end
end GinibrePoincare
