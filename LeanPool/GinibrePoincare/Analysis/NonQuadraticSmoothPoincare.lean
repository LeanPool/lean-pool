/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticSmoothPoincare.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-! # Smooth Poincaré inequality from the concrete weak-domain theorem -/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The entire smooth compact symmetric class is covered, including functions
whose support meets the collision locus. -/
theorem smoothGinibrePoincare_unconditional {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsSmoothCompactSymmetric f) :
    smoothGinibreVariance n f ≤ smoothGinibreEnergy n f / 2 := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have hv : MemLp f 2 (ginibreMeasure n) :=
    hf.1.continuous.memLp_of_hasCompactSupport hf.2.1
  have hg : MemLp (ginibreEuclideanGradient f) 2 (ginibreMeasure n) :=
    (continuous_ginibreEuclideanGradient f hf.1).memLp_of_hasCompactSupport
      (compactSupport_ginibreEuclideanGradient f hf.2.1)
  let u := hv.toLp f
  let g := hg.toLp (ginibreEuclideanGradient f)
  have hu : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f := hv.coeFn_toLp
  have hgrad : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[
      ginibreMeasure n] ginibreEuclideanGradient f := hg.coeFn_toLp
  have hweak := ginibre_smooth_distributional_gradient n hn u g f hf.1 hu hgrad
  have hs : IsGinibreSymmetricWeakPair (u, g) := by
    intro σ
    have hufix : ginibreRealPermutationL2 σ u = u := by
      apply Lp.ext
      have hucomp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp hu
      filter_upwards [ginibreRealPermutationL2_ae σ u, hucomp, hu] with z hσ hc hz
      simp only [Function.comp_apply] at hc
      rw [hσ, hc, hz]
      exact hf.2.2 σ z
    refine ⟨hufix, ?_⟩
    have hp := ginibreDistributionalGradient_permute hn σ u g hweak
    rw [hufix] at hp
    exact ginibre_distributional_gradient_unique n hn u _ g hp hweak
  have hi := ginibre_symmetric_weak_poincare hn u g hweak hs
  have hmean : ginibreL2Mean n u = smoothGinibreMean n f := by
    exact integral_congr_ae hu
  have hvar : ginibreL2Variance n hn u = smoothGinibreVariance n f := by
    rw [ginibreL2Variance, hmean, ← integral_square_eq_L2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub u (ginibreRealConstantL2 n hn (smoothGinibreMean n f)),
      hu, ginibreRealConstantL2_ae n hn (smoothGinibreMean n f)] with z hsub hz hc
    simp only [hsub, Pi.sub_apply, hz, hc]
  have henergy : ginibreWeakEnergy n g = smoothGinibreEnergy n f := by
    rw [ginibreWeakEnergy, ← integral_norm_sq_eq_L2_norm_sq]
    congr 1
    apply integral_congr_ae
    filter_upwards [hgrad] with z hz
    rw [hz, ginibreEuclideanGradient_norm_sq]
  rwa [hvar, henergy] at hi

end
end GinibrePoincare
