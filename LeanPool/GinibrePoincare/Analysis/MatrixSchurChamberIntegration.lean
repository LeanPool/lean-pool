/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurChamberIntegration.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurChambers
public import LeanPool.GinibrePoincare.Analysis.GinibreCollisionCutoff
public import LeanPool.GinibrePoincare.Analysis.GinibreSmoothDistributionalGradient
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff

/-!
# Matrix Schur chamber integration

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSchur_ordered_density_integral`.
-/

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section

theorem schurDiagonalSpectralDensity_symmetric (n : ℕ)
    (e : Fin n ≃ Fin n) (z : Fin n → ℂ) :
    schurDiagonalSpectralDensity n (z ∘ e) = schurDiagonalSpectralDensity n z := by
  have hv : vandermondeWeight (z ∘ e) = vandermondeWeight z :=
    vandermondeWeight_symmetric n e z
  have hs : (∑ i, Complex.normSq ((z ∘ e) i)) = ∑ i, Complex.normSq (z i) :=
    Equiv.sum_comp e (fun i => Complex.normSq (z i))
  unfold schurDiagonalSpectralDensity
  rw [hv, hs]

theorem matrixSchurPermutationChamber_lintegral {n : ℕ}
    (e : Fin n ≃ Fin n) (f : (Fin n → ℂ) → ℝ≥0∞) (hf : Measurable f)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, f (z ∘ e) = f z) :
    ∫⁻ z in matrixSchurPermutationChamber e, f z =
      ∫⁻ z in matrixSchurOrderedConfigurations n, f z := by
  have hp : MeasurePreserving (fun z : Fin n → ℂ => z ∘ e) := by
    have h := measurePreserving_piCongrLeft (fun _ : Fin n => (volume : Measure ℂ)) e.symm
    have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℂ) e.symm :
        (Fin n → ℂ) → (Fin n → ℂ)) = (fun z => z ∘ e) := by
      funext z i
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    rw [he, ← volume_pi] at h
    exact h
  have hi := hp.setLIntegral_comp_preimage (measurableSet_matrixSchurOrderedConfigurations n) hf
  have he : (fun z : Fin n → ℂ => f (z ∘ e)) = f := funext (hsym e)
  rw [he] at hi
  exact hi

/-- The ordered chambers partition all collision-free configurations. On their
complement the Vandermonde density vanishes, so finite chamber summation is exact. -/
theorem matrixSchur_ordered_density_integral {n : ℕ}
    (F : (Fin n → ℂ) → ℝ≥0∞) (hF : Measurable F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    ∫⁻ z, schurDiagonalSpectralDensity n z * F z =
      (Fintype.card (Fin n ≃ Fin n) : ℝ≥0∞) *
        ∫⁻ z in matrixSchurOrderedConfigurations n, schurDiagonalSpectralDensity n z * F z := by
  classical
  let f := fun z : Fin n → ℂ => schurDiagonalSpectralDensity n z * F z
  let S := ⋃ e : Fin n ≃ Fin n, matrixSchurPermutationChamber e
  have hm : MeasurableSet S := MeasurableSet.iUnion measurableSet_matrixSchurPermutationChamber
  have hf : Measurable f := (measurable_schurDiagonalSpectralDensity n).mul hF
  have hfs : ∀ e : Fin n ≃ Fin n, ∀ z, f (z ∘ e) = f z := by
    intro e z
    exact congrArg₂ (fun a b : ℝ≥0∞ => a*b) (schurDiagonalSpectralDensity_symmetric n e z) (hsym e
        z)
  have hzero : ∀ z ∉ S, f z = 0 := by
    intro z hz
    have hzi : ¬Function.Injective z := by
      intro hi
      exact hz (by dsimp only [S]; rw [matrixSchurPermutationChamber_cover]; exact hi)
    have hv : vandermondeWeight z = 0 := by
      apply (vandermondeWeight_eq_zero_iff z).mpr
      by_contra hnot
      exact hzi ((collisionFree_iff_not_mem_collisionSet z).mpr hnot)
    simp only [f, schurDiagonalSpectralDensity, hv, ENNReal.ofReal_zero, zero_mul]
  have hind : S.indicator f = f := by
    funext z
    by_cases hz : z ∈ S
    · exact Set.indicator_of_mem hz f
    · rw [Set.indicator_of_notMem hz, hzero z hz]
  have hs : ∫⁻ z, f z = ∫⁻ z in S, f z := by
    rw [← lintegral_indicator hm, hind]
  rw [hs, lintegral_iUnion measurableSet_matrixSchurPermutationChamber
    (matrixSchurPermutationChamber_pairwise_disjoint n)]
  have he : (∑' e : Fin n ≃ Fin n, ∫⁻ z in matrixSchurPermutationChamber e, f z) =
      ∑' _e : Fin n ≃ Fin n, ∫⁻ z in matrixSchurOrderedConfigurations n, f z := by
    apply tsum_congr
    intro e
    exact matrixSchurPermutationChamber_lintegral e f hf hfs
  rw [he, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end
end GinibrePoincare
