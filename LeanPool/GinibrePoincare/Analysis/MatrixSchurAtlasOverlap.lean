/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurAtlasOverlap.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurAtlasCover

/-!
# Matrix Schur atlas overlap

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSchurExponentialUnitaryFrame_continuous`, `matrixSchurAtlas_overlap_flag`,
`matrixSchurAtlas_flag_overlap`.
-/

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

theorem matrixSortedSchur_overlap_phase {n : ℕ}
    (G A B U V : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0)
    (hoA : matrixSchurOrderedDiagonal A) (hoB : matrixSchurOrderedDiagonal B)
    (hGa : G = U * A * Uᴴ) (hGb : G = V * B * Vᴴ) :
    Vᴴ * U = Matrix.diagonal (fun i => (Vᴴ * U) i i) := by
  have hcA := matrix_charpoly_unitary_conjugation A U hU
  have hcB := matrix_charpoly_unitary_conjugation B V hV
  have hc : A.charpoly = B.charpoly := by
    rw [← hcA, ← hcB, ← hGa, ← hGb]
  exact schur_ordered_representation_unique_phases G A B U V hU hV hA hB
    (matrixSchurOrderedDiagonal_eq_of_charpoly A B hA hB hoA hoB hc)
    (matrixSchurOrderedDiagonal_injective hoA) hGa hGb

/-- The exponential Schur frame `matrixSchurExponentialFrame n x` as an element of the unitary
group. -/
def matrixSchurExponentialUnitaryFrame (n : ℕ) (x : SchurLowerIndex n → ℂ) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨matrixSchurExponentialFrame n x, matrixSchurExponentialFrame_unitary n x⟩

theorem matrixSchurExponentialUnitaryFrame_continuous (n : ℕ) :
    Continuous (matrixSchurExponentialUnitaryFrame n) :=
  (matrixSchurExponentialFrame_differentiable n).continuous.subtype_mk
    (matrixSchurExponentialFrame_unitary n)

/-- Membership in another ordered Schur chart depends solely on its angular flag,
not on eigenvalues or strict upper entries. -/
theorem matrixSchurAtlas_overlap_flag {n : ℕ}
    (V : Set (SchurLowerIndex n → ℂ))
    (C E : Matrix.unitaryGroup (Fin n) ℂ) (p q : SchurCoordinates n)
    (hp : p ∈ V ×ˢ matrixSchurSortedUpperDomain n)
    (hq : q ∈ V ×ˢ matrixSchurSortedUpperDomain n)
    (he : matrixSchurAtlasChart C p = matrixSchurAtlasChart E q) :
    ((E : Matrix (Fin n) (Fin n) ℂ)ᴴ *
      ((C : Matrix (Fin n) (Fin n) ℂ) * matrixSchurExponentialFrame n p.1)) ∈
        matrixUnitaryFlagSaturation n V := by
  let U : Matrix (Fin n) (Fin n) ℂ := (C : Matrix (Fin n) (Fin n) ℂ) * matrixSchurExponentialFrame n
      p.1
  let W : Matrix (Fin n) (Fin n) ℂ := (E : Matrix (Fin n) (Fin n) ℂ) * matrixSchurExponentialFrame n
      q.1
  have hUunit : U ∈ Matrix.unitaryGroup (Fin n) ℂ := (C * matrixSchurExponentialUnitaryFrame n
      p.1).property
  have hWunit : W ∈ Matrix.unitaryGroup (Fin n) ℂ := (E * matrixSchurExponentialUnitaryFrame n
      q.1).property
  let A := schurUpperCombination p.2
  let B := schurUpperCombination q.2
  have hGa : matrixSchurAtlasChart C p = (U : Matrix (Fin n) (Fin n) ℂ) * A * (U : Matrix (Fin n)
      (Fin n) ℂ)ᴴ := by
    simp only [matrixSchurAtlasChart, matrixSchurFrameChart, zero_add]
    dsimp only [U, A, matrixSchurExponentialUnitaryFrame]
    rw [Matrix.conjTranspose_mul]
    noncomm_ring
  have hGb : matrixSchurAtlasChart C p = (W : Matrix (Fin n) (Fin n) ℂ) * B * (W : Matrix (Fin n)
      (Fin n) ℂ)ᴴ := by
    rw [he]
    simp only [matrixSchurAtlasChart, matrixSchurFrameChart, zero_add]
    dsimp only [W, B, matrixSchurExponentialUnitaryFrame]
    rw [Matrix.conjTranspose_mul]
    noncomm_ring
  have hAlower : ∀ i j, j < i → A i j = 0 :=
    fun i j hij => schurUpperCombination_lower_zero p.2 i j hij
  have hBlower : ∀ i j, j < i → B i j = 0 :=
    fun i j hij => schurUpperCombination_lower_zero q.2 i j hij
  have hoA : matrixSchurOrderedDiagonal A := hp.2
  have hoB : matrixSchurOrderedDiagonal B := hq.2
  have hphase := @matrixSortedSchur_overlap_phase n (matrixSchurAtlasChart C p) A B U W
      hUunit hWunit hAlower hBlower hoA hoB hGa hGb
  let D : Matrix (Fin n) (Fin n) ℂ := Wᴴ * U
  have hDunit : D ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    (Matrix.unitaryGroup (Fin n) ℂ).mul_mem (Unitary.star_mem hWunit) hUunit
  have hD : D = Wᴴ * U := rfl
  refine ⟨q.1, hq.1, D, hDunit, ?_, ?_⟩
  · intro i j hij
    rw [hD, hphase]
    simp [hij]
  · have hQQ : matrixSchurExponentialFrame n q.1 * (matrixSchurExponentialFrame n q.1)ᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (matrixSchurExponentialFrame_unitary n q.1)
    rw [hD]
    dsimp only [W, U, matrixSchurExponentialUnitaryFrame]
    rw [Matrix.conjTranspose_mul]
    symm
    calc
      _ = (matrixSchurExponentialFrame n q.1 * (matrixSchurExponentialFrame n q.1)ᴴ) *
          ((E : Matrix (Fin n) (Fin n) ℂ)ᴴ * ((C : Matrix (Fin n) (Fin n) ℂ) *
              matrixSchurExponentialFrame n p.1)) := by
        noncomm_ring
      _ = _ := by rw [hQQ, Matrix.one_mul]

theorem matrixSchurAtlasChart_eq_conjugation {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℂ) (p : SchurCoordinates n) :
    matrixSchurAtlasChart C p =
      (C * matrixSchurExponentialFrame n p.1) * schurUpperCombination p.2 *
        (C * matrixSchurExponentialFrame n p.1)ᴴ := by
  simp only [matrixSchurAtlasChart, matrixSchurFrameChart, zero_add, Matrix.conjTranspose_mul]
  noncomm_ring

/-- Conversely, angular flag overlap transports every sorted triangular coordinate
into the other chart, so overlap sets are independent of all upper entries. -/
theorem matrixSchurAtlas_flag_overlap {n : ℕ}
    (V : Set (SchurLowerIndex n → ℂ))
    (C E : Matrix.unitaryGroup (Fin n) ℂ) (p : SchurCoordinates n)
    (hp : p.2 ∈ matrixSchurSortedUpperDomain n)
    (hflag : ((E : Matrix (Fin n) (Fin n) ℂ)ᴴ *
      ((C : Matrix (Fin n) (Fin n) ℂ) * matrixSchurExponentialFrame n p.1)) ∈
        matrixUnitaryFlagSaturation n V) :
    ∃ q ∈ V ×ˢ matrixSchurSortedUpperDomain n,
      matrixSchurAtlasChart C p = matrixSchurAtlasChart E q := by
  obtain ⟨x, hx, D, hD, hdiag, hphase⟩ := hflag
  let A := schurUpperCombination p.2
  let B := D * A * Dᴴ
  obtain ⟨hB, hBdiag⟩ := matrixDiagonalUnitary_schur_preserves D A hD hdiag
    (fun i j hij => schurUpperCombination_lower_zero _ i j hij)
  have hdB : ∀ i, B i i = A i i := hBdiag
  let y := (schurEntryCoordinates B).2
  have hy : schurUpperCombination y = B := schurUpperCombination_read_upper B hB
  have hysorted : y ∈ matrixSchurSortedUpperDomain n := by
    change matrixSchurOrderedDiagonal (schurUpperCombination y)
    rw [hy]
    intro i j hij
    change toLex ((B i i).re, (B i i).im) < toLex ((B j j).re, (B j j).im)
    rw [hdB, hdB]
    exact hp hij
  have hEE : (E : Matrix (Fin n) (Fin n) ℂ) * (E : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp E.property
  have hrep : (C : Matrix (Fin n) (Fin n) ℂ) * matrixSchurExponentialFrame n p.1 =
      (E : Matrix (Fin n) (Fin n) ℂ) * matrixSchurExponentialFrame n x * D := by
    calc
      _ = ((E : Matrix (Fin n) (Fin n) ℂ) * (E : Matrix (Fin n) (Fin n) ℂ)ᴴ) *
          ((C : Matrix (Fin n) (Fin n) ℂ) * matrixSchurExponentialFrame n p.1) := by
        rw [hEE, Matrix.one_mul]
      _ = (E : Matrix (Fin n) (Fin n) ℂ) *
          ((E : Matrix (Fin n) (Fin n) ℂ)ᴴ *
            ((C : Matrix (Fin n) (Fin n) ℂ) * matrixSchurExponentialFrame n p.1)) := by
                rw [Matrix.mul_assoc]
      _ = _ := by rw [hphase, ← Matrix.mul_assoc]
  refine ⟨(x, y), ⟨hx, hysorted⟩, ?_⟩
  rw [matrixSchurAtlasChart_eq_conjugation, matrixSchurAtlasChart_eq_conjugation,
    hrep, hy]
  simp only [Matrix.conjTranspose_mul]
  dsimp only [B, A]
  noncomm_ring

end
end GinibrePoincare
