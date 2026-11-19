/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGirsanovDensityLimit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGirsanovUniformIntegrability

/-!
# Brownian integral Girsanov density limit

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `nonnegativeDensities_limit_normalized_of_secondMoment_bound`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- True second-moment control plus actual convergence in probability preserves
normalization and gives L¹ convergence of nonnegative densities. -/
theorem nonnegativeDensities_limit_normalized_of_secondMoment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (f n)) (hp : ∀ n ω, 0 ≤ f n ω)
    (R : ℝ) (hR : 0 ≤ R)
    (h2 : ∀ n, (∫⁻ ω, ENNReal.ofReal (f n ω) ^ 2 ∂P) ≤ ENNReal.ofReal R)
    (h1 : ∀ n, (∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) = 1)
    (D : Ω → ℝ) (hlim : TendstoInMeasure P f atTop D) :
    Integrable D P ∧ (0≤ᵐ[P] D) ∧ (∫ ω, D ω ∂P)=1 ∧
      Tendsto (fun n => eLpNorm (f n-D) 1 P) atTop (𝓝 0) := by
  have hUI := nonnegativeDensities_uniformIntegrable_of_secondMoment_bound P f hm hp R hR h2
  have hDL := hUI.memLp_of_tendstoInMeasure hlim
  have hDi : Integrable D P := memLp_one_iff_integrable.mp hDL
  have hL := tendsto_Lp_finite_of_tendstoInMeasure (by norm_num : (1 : ℝ≥0∞)≤1)
    (by norm_num : (1 : ℝ≥0∞)≠∞) (fun n => (hm n).aestronglyMeasurable) hDL hUI.unifIntegrable hlim
  have hfn (n : ℕ) : Integrable (f n) P := memLp_one_iff_integrable.mp (hUI.memLp n)
  have hfi (n : ℕ) : (∫ ω, f n ω ∂P)=1 := by
    have hh := h1 n
    rw [← ofReal_integral_eq_lintegral_ofReal (hfn n) (Eventually.of_forall (hp n))] at hh
    have he := congrArg ENNReal.toReal hh
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (hp n)), ENNReal.toReal_one] using he
  have hInt := tendsto_integral_of_L1' D (Eventually.of_forall hfn) hL
  have hDe : (∫ ω, D ω ∂P)=1 := by
    have hConst : Tendsto (fun n : ℕ => ∫ ω, f n ω ∂P) atTop (𝓝 1) := by
      simpa only [hfi] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    exact tendsto_nhds_unique hInt hConst
  obtain ⟨s, hs, hsa⟩ := hlim.exists_seq_tendsto_ae
  have hDp : (0≤ᵐ[P] D) := by
    filter_upwards [hsa] with ω hω
    exact ge_of_tendsto hω (Eventually.of_forall (fun n => hp (s n) ω))
  exact ⟨hDi, hDp, hDe, hL⟩

end
end GinibrePoincare
