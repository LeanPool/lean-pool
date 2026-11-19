/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianEntireDistance.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianEntireSpaceClosure

/-! # Entire representative distance for the complex Gaussian
The squared distance is the paper's infimum of actual integral errors.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

theorem continuous_gaussianL2_iff_memLp {n : ℕ} (g : Configuration n → ℂ)
    (hg : Continuous g) : IsGaussianL2 n g ↔ MemLp g 2 (complexGaussianMeasure n) := by
  rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable]
  simp only [IsGaussianL2, Complex.sq_norm]

theorem gaussianComplexError_eq_L2_norm_sq {n : ℕ}
    (u v : Lp ℂ 2 (complexGaussianMeasure n)) (g h : Configuration n → ℂ)
    (hu : g =ᵐ[complexGaussianMeasure n] u) (hv : h =ᵐ[complexGaussianMeasure n] v) :
    gaussianComplexError n g h = ‖u-v‖ ^ 2 := by
  rw [gaussianComplexError, ← integral_norm_sq_eq_L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [hu, hv, Lp.coeFn_sub u v] with z huz hvz hsub
  simp only [Pi.sub_apply] at hsub
  rw [huz, hvz, hsub, Complex.sq_norm]

theorem gaussianHolomorphicDistanceSq_eq_projectionNorm {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (g : Configuration n → ℂ)
    (hu : g =ᵐ[complexGaussianMeasure n] u) :
    gaussianHolomorphicDistanceSq n g =
      ‖u - (gaussianEntireClosedSpace n hn).starProjection u‖ ^ 2 := by
  let H := gaussianEntireClosedSpace n hn
  let P := H.starProjection
  have hmem : P u ∈ gaussianEntireL2 n := Submodule.starProjection_apply_mem H.toSubmodule u
  obtain ⟨h, hh, hrep⟩ := hmem
  have hml : MemLp h 2 (complexGaussianMeasure n) := (memLp_congr_ae hrep).mpr (Lp.memLp (P u))
  have hhL2 : IsGaussianL2 n h := (continuous_gaussianL2_iff_memLp h hh.continuous).mpr hml
  have herr : ‖u-P u‖ ^ 2 ∈ gaussianHolomorphicErrors n g := by
    refine ⟨h, hh, hhL2, ?_⟩
    exact (gaussianComplexError_eq_L2_norm_sq u (P u) g h hu hrep).symm
  have hb : BddBelow (gaussianHolomorphicErrors n g) := by
    refine ⟨0, ?_⟩
    rintro r ⟨a, _, _, rfl⟩
    exact integral_nonneg (fun _ => Complex.normSq_nonneg _)
  apply le_antisymm
  · exact csInf_le hb herr
  · apply le_csInf ⟨_, herr⟩
    rintro r ⟨a, ha, haL2, rfl⟩
    have haml := (continuous_gaussianL2_iff_memLp a ha.continuous).mp haL2
    let v := haml.toLp a
    have hv : IsGaussianEntireRepresentative v a := ⟨ha, haml.coeFn_toLp.symm⟩
    have hvm : v ∈ H := ⟨a, hv⟩
    rw [gaussianComplexError_eq_L2_norm_sq u v g a hu hv.2]
    have ho : inner ℂ (u-P u) (P u-v) = 0 :=
      Submodule.starProjection_inner_eq_zero u (P u-v)
        (H.sub_mem (Submodule.starProjection_apply_mem H.toSubmodule u) hvm)
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (u-P u) (P u-v) ho
    have he : (u-P u)+(P u-v) = u-v := by abel
    rw [he] at hpy
    simp only [pow_two]
    nlinarith [sq_nonneg ‖P u-v‖]

theorem gaussianRepresentative_norm_sq_eq_integral {n : ℕ}
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (g : Configuration n → ℂ)
    (hu : g =ᵐ[complexGaussianMeasure n] u) :
    ‖u‖ ^ 2 = ∫ z, Complex.normSq (g z) ∂complexGaussianMeasure n := by
  rw [← integral_norm_sq_eq_L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [hu] with z hz
  rw [hz, Complex.sq_norm]

/-- The literal representative-level Gaussian estimate used by the paper's
main proof. All analytic domain facts follow from its stated admissibility. -/
theorem gaussianDbarEstimateStatement : GaussianDbarEstimateStatement := by
  intro n hn g hg
  have hml := (continuous_gaussianL2_iff_memLp g hg.1.continuous).mp hg.2.1
  let u := hml.toLp g
  have hdml (j : Fin n) : MemLp (dbarComponent g j) 2 (complexGaussianMeasure n) :=
    (continuous_gaussianL2_iff_memLp _
      (continuous_dbarComponent (hg.1.of_le (by simp)) j)).mp (hg.2.2 j)
  let D := fun j : Fin n => (hdml j).toLp (dbarComponent g j)
  have hweak (j : Fin n) : IsGaussianSchwartzDbar n u (D j) j :=
    (gaussianSchwartzDbar_iff_weak hn u (D j) j).mpr
      (gaussian_smooth_weak_dbar hn j u (D j) g (hg.1.of_le (by simp))
        hml.coeFn_toLp (hdml j).coeFn_toLp)
  rw [gaussianHolomorphicDistanceSq_eq_projectionNorm hn u g hml.coeFn_toLp.symm]
  have hgap := gaussianSchwartzDbar_entire_gap hn u D hweak
  have he : (1 / (n : ℝ)) * ∑ j, ‖D j‖ ^ 2 = gaussianDbarEnergy n g := by
    unfold gaussianDbarEnergy dbarNormSq
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hg.2.2 j)]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact gaussianRepresentative_norm_sq_eq_integral (D j) _ (hdml j).coeFn_toLp.symm
  rwa [he] at hgap

end
end GinibrePoincare

