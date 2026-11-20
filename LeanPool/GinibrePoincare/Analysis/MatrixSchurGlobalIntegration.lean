/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurGlobalIntegration.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurAtlasIntegration
public import LeanPool.GinibrePoincare.Analysis.MatrixVolumeSimpleSpectrum

/-! # Global integration from disjoint Schur atlas pieces

A countable flag atlas is partitioned into measurable angular pieces whose
Schur images are disjoint. Sorted Schur decomposition covers the simple-spectrum
locus, and the remaining matrices form a volume-null set. Summing the local
product-integral formulas therefore gives the full matrix integral. Since each
piece has the same triangular integral, it factors out of the sum, leaving one
angular constant independent of the unitary-invariant observable. The final
theorem constructs the chart and countable cover internally.
-/

@[expose] public section

open Matrix NormedSpace MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
namespace GinibrePoincare
noncomputable section

theorem matrixSchurAtlasChart_continuous {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℂ) : Continuous (matrixSchurAtlasChart C) := by
  have he : matrixSchurAtlasChart C = matrixUnitaryConjugation C ∘
      matrixSchurFrameChart (matrixSchurExponentialFrame n) (0 : Matrix (Fin n) (Fin n) ℂ) :=
    funext fun p => (matrixUnitaryConjugation_apply C _).symm
  rw [he]
  exact (matrixUnitaryConjugation C).continuous.comp
    (matrixSchurExponentialChart_differentiable 0).continuous

theorem matrixSchurAtlasChart_injOn {n : ℕ}
    (C : Matrix.unitaryGroup (Fin n) ℂ) (s : Set (SchurCoordinates n))
    (hi : InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n)
      (0 : Matrix (Fin n) (Fin n) ℂ)) s) :
    InjOn (matrixSchurAtlasChart C) s := by
  intro p hp q hq he
  apply hi hp hq
  apply matrixUnitaryConjugation_injective (C : Matrix (Fin n) (Fin n) ℂ) C.property
  exact (matrixUnitaryConjugation_apply _ _).trans
    (he.trans (matrixUnitaryConjugation_apply _ _).symm)

/-- Global Schur integration obtained from a disjoint measurable flag atlas. The
angular constant is independent of the observable and all triangular entries. -/
theorem matrixSchur_global_integral_of_atlas {n : ℕ}
    (V : Set (SchurLowerIndex n → ℂ)) (hV : IsOpen V)
    (hinj : InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n) (0 : Matrix (Fin n) (Fin n)
        ℂ))
      (V ×ˢ matrixSchurSortedUpperDomain n))
    (hopen : IsOpen {U : Matrix.unitaryGroup (Fin n) ℂ |
      (U : Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V})
    (C : ℕ → Matrix.unitaryGroup (Fin n) ℂ)
    (hC : ∀ U : Matrix.unitaryGroup (Fin n) ℂ, ∃ k,
      ((C k : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ)) ∈
        matrixUnitaryFlagSaturation n V)
    (g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) (hg : Measurable g)
    (hInv : ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, g (U * A * Uᴴ) = g A) :
    ∫⁻ A, g A =
      (∑' k, ∫⁻ x in matrixSchurAtlasAngularPiece V C k,
        ENNReal.ofReal (matrixSchurAngularDensity n x)) *
      ∫⁻ y in matrixSchurSortedUpperDomain n,
        ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
          g (schurUpperCombination y) := by
  let : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))
  let angularPiece := fun k => matrixSchurAtlasAngularPiece V C k
  let matrixPiece := fun k => matrixSchurAtlasChart (C k) '' (angularPiece k ×ˢ
      matrixSchurSortedUpperDomain n)
  have hangularPiece_measurable : ∀ k, MeasurableSet (angularPiece k) :=
    fun k => measurableSet_matrixSchurAtlasAngularPiece V hV C hopen k
  have hi : ∀ k, InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n) 0)
      (angularPiece k ×ˢ matrixSchurSortedUpperDomain n) := by
    intro k
    apply hinj.mono
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  have hmatrixPiece_measurable : ∀ k, MeasurableSet (matrixPiece k) := by
    intro k
    exact ((hangularPiece_measurable k).prod (measurableSet_matrixSchurSortedUpperDomain
        n)).image_of_continuousOn_injOn
      (@matrixSchurAtlasChart_continuous n (C k)).continuousOn
      (@matrixSchurAtlasChart_injOn n (C k) (angularPiece k ×ˢ matrixSchurSortedUpperDomain n) (hi
          k))
  have hcover_ae : (⋃ k, matrixPiece k) =ᵐ[volume] (Set.univ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    filter_upwards [matrixVolume_charpoly_separable_ae n] with G hG
    obtain ⟨k, p, hp, he⟩ := matrixSchurAtlas_partition_cover V C hC G hG
    exact iff_true_intro (Set.mem_iUnion.mpr ⟨k, ⟨p, hp, he.symm⟩⟩)
  have hc := setLIntegral_congr hcover_ae (f := g)
  rw [setLIntegral_univ] at hc
  rw [← hc, lintegral_iUnion hmatrixPiece_measurable (matrixSchurAtlas_partition_pairwise_disjoint V
      C)]
  have ht : (∑' k, ∫⁻ A in matrixPiece k, g A) =
      ∑' k, (∫⁻ x in angularPiece k, ENNReal.ofReal (matrixSchurAngularDensity n x)) *
        ∫⁻ y in matrixSchurSortedUpperDomain n,
          ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
            g (schurUpperCombination y) := by
    apply tsum_congr
    intro k
    exact matrixSchurAtlas_product_integral (C k) (angularPiece k) (hangularPiece_measurable k) (hi
        k) g hg hInv
  rw [ht, ENNReal.tsum_mul_right]

/-- Actual global Schur integration, with one angular constant shared by every
measurable unitary-invariant observable. -/
theorem matrixSchur_global_integral (n : ℕ) :
    ∃ c : ℝ≥0∞, ∀ g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞, Measurable g →
      (∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, g (U * A * Uᴴ) = g A) →
      ∫⁻ A, g A = c * ∫⁻ y in matrixSchurSortedUpperDomain n,
        ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
          g (schurUpperCombination y) := by
  obtain ⟨V, hV, h0, hi, hsource, hden, hopen⟩ := matrixSchurAngularChart_exists n
  obtain ⟨C, hC⟩ := matrixUnitaryFlagSaturation_countable_cover n V h0 hopen
  refine ⟨∑' k, ∫⁻ x in matrixSchurAtlasAngularPiece V C k,
    ENNReal.ofReal (matrixSchurAngularDensity n x), ?_⟩
  intro g hg hInv
  exact matrixSchur_global_integral_of_atlas V hV hi hopen C hC g hg hInv

end
end GinibrePoincare
