/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorInvariantLimit.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorErgodicity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
/-!
# Correspondence operator invariant limit

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperator_invariant_limit`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
/-- Strong L² convergence and a uniform observable bound transfer equilibrium
integrals to every absolutely continuous probability, without any L² assumption
on its density. Only a subsequence is needed. -/
theorem correspondenceOperator_invariant_limit {n : ℕ} (hn : 0 < n)
    (ρ : Measure (Configuration n)) [IsProbabilityMeasure ρ]
    (hρ : ρ ≪ ginibreMeasure n) (F : ℕ → GinibreFullValueL2 n)
    (v : ℕ → Configuration n → ℝ) (a b C : ℝ)
    (hF : Tendsto F atTop (𝓝 (ginibreRealConstantL2 n hn a)))
    (hrep : ∀ k, F k =ᵐ[ginibreMeasure n] v k)
    (hv : ∀ k, AEStronglyMeasurable (v k) ρ)
    (hbound : ∀ k, ∀ᵐ z ∂ρ, ‖v k z‖ ≤ C)
    (hInv : ∀ k, ∫ z, v k z ∂ρ = b) : b=a := by
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  have hae : ∀ᵐz∂ginibreMeasure n,
      Tendsto (fun k=>v (ns k) z) atTop (𝓝 a) := by
    filter_upwards [hlim, ae_all_iff.mpr hrep, ginibreRealConstantL2_ae n hn a]
      with z hz hr hc
    simpa only [hr, hc] using hz
  have hi : Tendsto (fun k=>∫z, v (ns k) z∂ρ) atTop (𝓝 a) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ : Configuration n=>C)
      (fun k=>hv (ns k)) (integrable_const C) (fun k=>hbound (ns k)) (hρ.ae_le hae)
    simpa using h
  simp only [hInv] at hi
  exact tendsto_nhds_unique tendsto_const_nhds hi
end
end GinibrePoincare
