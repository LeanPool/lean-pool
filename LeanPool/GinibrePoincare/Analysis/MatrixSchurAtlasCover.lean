/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurAtlasCover.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixUnitaryFlagAtlas

/-!
# Matrix Schur atlas cover

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSchurAtlas_countable_cover`, `matrixSchurAtlas_cover_of_unitary_cover`.
-/

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

theorem matrixDiagonalUnitary_schur_preserves {n : ℕ}
    (D T : Matrix (Fin n) (Fin n) ℂ)
    (hD : D ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hd : ∀ i j, i ≠ j → D i j = 0)
    (hT : ∀ i j, j < i → T i j = 0) :
    (∀ i j, j < i → (D * T * Dᴴ) i j = 0) ∧
      (∀ i, (D * T * Dᴴ) i i = T i i) := by
  have hdiag : D = Matrix.diagonal (fun i => D i i) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [hd i j hij, hij]
  have hentry (i j : Fin n) : (D * T * Dᴴ) i j = D i i * T i j * star (D j j) := by
    have hi := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => (A * T * Aᴴ) i j) hdiag
    exact hi.trans (by
      rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
      rfl)
  have hDD : D * Dᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hD
  have hnorm (i : Fin n) : D i i * star (D i i) = 1 := by
    have hi : ((Matrix.diagonal fun j => D j j) *
        (Matrix.diagonal fun j => D j j)ᴴ) i i = 1 := by
      rw [← hdiag, hDD, Matrix.one_apply_eq]
    simpa [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal] using hi
  refine ⟨?_, ?_⟩
  · intro i j hij
    rw [hentry, hT i j hij, mul_zero, zero_mul]
  · intro i
    rw [hentry]
    calc
      _ = T i i * (D i i * star (D i i)) := by ring
      _ = T i i := by rw [hnorm, mul_one]

theorem schurUpperCombination_read_upper {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) :
    schurUpperCombination (schurEntryCoordinates T).2 = T := by
  ext i j
  by_cases hij : j < i
  · rw [schurUpperCombination_lower_zero _ i j hij, hT i j hij]
  · exact schurUpperCombination_entry _ ⟨(i, j), le_of_not_gt hij⟩

/-- The Schur atlas chart centred at `C`: `(x, y) ↦ C Q(x) Y Q(x)ᴴ Cᴴ`, where `Q(x)` is
`matrixSchurExponentialFrame n x` and `Y` is the upper-triangular matrix with entries `y`. -/
def matrixSchurAtlasChart {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (p : SchurCoordinates n) : Matrix (Fin n) (Fin n) ℂ :=
  C * matrixSchurFrameChart (matrixSchurExponentialFrame n) 0 p * Cᴴ

/-- A genuine countable family of unbounded product Schur charts covers every simple
matrix. The angular coordinate domain is common to every chart. -/
theorem matrixSchurAtlas_countable_cover (n : ℕ) :
    ∃ V : Set (SchurLowerIndex n → ℂ), IsOpen V ∧ 0 ∈ V ∧
      ∃ C : ℕ → Matrix.unitaryGroup (Fin n) ℂ,
        ∀ G : Matrix (Fin n) (Fin n) ℂ, G.charpoly.Separable →
          ∃ k, ∃ p ∈ V ×ˢ matrixSchurSortedUpperDomain n,
            G = matrixSchurAtlasChart (C k) p := by
  obtain ⟨V, hV, h0, hinj, hsource, hden, hopen⟩ := matrixSchurAngularChart_exists n
  obtain ⟨C, hC⟩ := matrixUnitaryFlagSaturation_countable_cover n V h0 hopen
  refine ⟨V, hV, h0, C, ?_⟩
  intro G hs
  obtain ⟨U, T, hU, hT, hsorted, hG⟩ := matrixSimpleSpectrum_exists_sorted_unitary_schur n G hs
  obtain ⟨k, hk⟩ := hC ⟨U, hU⟩
  obtain ⟨x, hx, D, hD, hdiag, hphase⟩ := hk
  let B := D * T * Dᴴ
  obtain ⟨hB, hBdiag⟩ := matrixDiagonalUnitary_schur_preserves D T hD hdiag hT
  have hdB : ∀ i, B i i = T i i := hBdiag
  let y := (schurEntryCoordinates B).2
  have hy : schurUpperCombination y = B := schurUpperCombination_read_upper B hB
  have hysorted : y ∈ matrixSchurSortedUpperDomain n := by
    change matrixSchurOrderedDiagonal (schurUpperCombination y)
    rw [hy]
    intro i j hij
    change toLex ((B i i).re, (B i i).im) < toLex ((B j j).re, (B j j).im)
    rw [hdB, hdB]
    exact hsorted hij
  have hCC : (C k : Matrix (Fin n) (Fin n) ℂ) * (C k : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (C k).property
  have hUrep : U = (C k : Matrix (Fin n) (Fin n) ℂ) * matrixSchurExponentialFrame n x * D := by
    calc
      U = ((C k : Matrix (Fin n) (Fin n) ℂ) * (C k : Matrix (Fin n) (Fin n) ℂ)ᴴ) * U := by
        rw [hCC, Matrix.one_mul]
      _ = (C k : Matrix (Fin n) (Fin n) ℂ) *
          ((C k : Matrix (Fin n) (Fin n) ℂ)ᴴ * U) := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hphase, ← Matrix.mul_assoc]
  refine ⟨k, (x, y), ⟨hx, hysorted⟩, ?_⟩
  rw [hG, hUrep, matrixSchurAtlasChart, matrixSchurFrameChart, zero_add, hy]
  simp only [Matrix.conjTranspose_mul]
  dsimp only [B]
  noncomm_ring

/-- Coverage follows from a concrete flag atlas, so a chosen atlas can be reused for
its disjoint chart partition and integral formulas. -/
theorem matrixSchurAtlas_cover_of_unitary_cover (n : ℕ)
    (V : Set (SchurLowerIndex n → ℂ)) (C : ℕ → Matrix.unitaryGroup (Fin n) ℂ)
    (hC : ∀ U : Matrix.unitaryGroup (Fin n) ℂ, ∃ k,
      ((C k : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ)) ∈
        matrixUnitaryFlagSaturation n V) :
    ∀ G : Matrix (Fin n) (Fin n) ℂ, G.charpoly.Separable →
      ∃ k, ∃ p ∈ V ×ˢ matrixSchurSortedUpperDomain n,
        G = matrixSchurAtlasChart (C k) p := by
  intro G hs
  obtain ⟨U, T, hU, hT, hsorted, hG⟩ := matrixSimpleSpectrum_exists_sorted_unitary_schur n G hs
  obtain ⟨k, hk⟩ := hC ⟨U, hU⟩
  obtain ⟨x, hx, D, hD, hdiag, hphase⟩ := hk
  let B := D * T * Dᴴ
  obtain ⟨hB, hBdiag⟩ := matrixDiagonalUnitary_schur_preserves D T hD hdiag hT
  have hdB : ∀ i, B i i = T i i := hBdiag
  let y := (schurEntryCoordinates B).2
  have hy : schurUpperCombination y = B := schurUpperCombination_read_upper B hB
  have hysorted : y ∈ matrixSchurSortedUpperDomain n := by
    change matrixSchurOrderedDiagonal (schurUpperCombination y)
    rw [hy]
    intro i j hij
    change toLex ((B i i).re, (B i i).im) < toLex ((B j j).re, (B j j).im)
    rw [hdB, hdB]
    exact hsorted hij
  have hCC : (C k : Matrix (Fin n) (Fin n) ℂ) * (C k : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (C k).property
  have hUrep : U = (C k : Matrix (Fin n) (Fin n) ℂ) * matrixSchurExponentialFrame n x * D := by
    calc
      U = ((C k : Matrix (Fin n) (Fin n) ℂ) * (C k : Matrix (Fin n) (Fin n) ℂ)ᴴ) * U := by
        rw [hCC, Matrix.one_mul]
      _ = (C k : Matrix (Fin n) (Fin n) ℂ) *
          ((C k : Matrix (Fin n) (Fin n) ℂ)ᴴ * U) := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hphase, ← Matrix.mul_assoc]
  refine ⟨k, (x, y), ⟨hx, hysorted⟩, ?_⟩
  rw [hG, hUrep, matrixSchurAtlasChart, matrixSchurFrameChart, zero_add, hy]
  simp only [Matrix.conjTranspose_mul]
  dsimp only [B]
  noncomm_ring

end
end GinibrePoincare
