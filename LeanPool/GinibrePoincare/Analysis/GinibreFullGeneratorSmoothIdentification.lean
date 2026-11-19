/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullGeneratorSmoothIdentification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorVariational
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCoreIdentification
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroup
public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Ginibre full generator smooth identification

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreFullGenerator_smooth_graph`.
-/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory Filter
open scoped Topology ContDiff

/-- Smooth noncompact observables with their actual L² gradient and actual L²
pregenerator belong to the full weak generator. The extension uses the proved
collision-free core density, rather than a postulated weak Green equation. -/
theorem ginibreFullGenerator_smooth_graph {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f)
    (u v : ginibreFullSymmetricValues n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u.val g)
    (hs : IsGinibreSymmetricWeakPair (u.val, g))
    (huf : (u.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hvf : (v.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n] ginibrePregenerator n f) :
    (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph := by
  rw [ginibreFullGenerator_ofReal_variational_iff hn u v g hu hs]
  intro w h hw hsw
  obtain ⟨q, hq, hlim⟩ := ginibreSymmetricWeakPair_exists_core_sequence hn w h hw hsw
  have heq (m : ℕ) : (1 / (n : ℝ)) * inner ℝ g (q m).2 = -inner ℝ v.val (q m).1 := by
    obtain ⟨φ, hφ, hvalue, hgradient⟩ := hq m
    have hgq : (q m).2 = ginibreFullCoreGradient hn φ hφ := by
      apply Lp.ext
      exact hgradient.trans (ginibreFullCoreGradient_ae hn φ hφ).symm
    have hvq : (q m).1 = ginibreFullCoreValue hn φ hφ := by
      apply Lp.ext
      exact hvalue.trans (ginibreFullCoreValue_ae hn φ hφ).symm
    rw [hgq, hvq]
    have hgreen := ginibreFullGenerator_weak_core_green hn u.val g hu φ hφ
    have hmix : inner ℝ u.val (ginibreFullCorePregenerator hn φ hφ) =
        inner ℝ v.val (ginibreFullCoreValue hn φ hφ) := by
      rw [L2.inner_def, L2.inner_def]
      calc
        (∫ z, (ginibreFullCorePregenerator hn φ hφ) z * u.val z ∂ginibreMeasure n) =
            ∫ z, f z * ginibrePregenerator n φ z ∂ginibreMeasure n := by
          apply integral_congr_ae
          filter_upwards [huf, ginibreFullCorePregenerator_ae hn φ hφ] with z hz ha
          rw [hz, ha, mul_comm]
        _ = ∫ z, φ z * ginibrePregenerator n f z ∂ginibreMeasure n :=
          (ginibre_mixed_green_identity hn hφ hf).symm
        _ = ∫ z, (ginibreFullCoreValue hn φ hφ) z * v.val z ∂ginibreMeasure n := by
          apply integral_congr_ae
          filter_upwards [hvf, ginibreFullCoreValue_ae hn φ hφ] with z hz ha
          rw [hz, ha]
    rw [hmix] at hgreen
    exact hgreen
  have hl : Tendsto (fun p : GinibreFullValueL2 n × GinibreFullGradientL2 n =>
      (1 / (n : ℝ)) * inner ℝ g p.2) (𝓝 (w, h))
      (𝓝 ((1 / (n : ℝ)) * inner ℝ g h)) :=
    (continuous_const.mul (continuous_const.inner continuous_snd)).tendsto (w, h)
  have hr : Tendsto (fun p : GinibreFullValueL2 n × GinibreFullGradientL2 n =>
      -inner ℝ v.val p.1) (𝓝 (w, h)) (𝓝 (-inner ℝ v.val w)) :=
    (continuous_const.inner continuous_fst).neg.tendsto (w, h)
  exact tendsto_nhds_unique (hl.comp hlim) ((hr.comp hlim).congr (fun m => (heq m).symm))

end GinibrePoincare
