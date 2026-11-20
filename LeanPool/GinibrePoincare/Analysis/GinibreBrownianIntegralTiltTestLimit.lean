/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltTestLimit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralExponentialNatural
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Ginibre Brownian integral tilt test limit

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `actualDensity_bounded_test_error_tendsto`, `actualDensity_continuous_test_tendsto`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction
namespace GinibrePoincare
noncomputable section

/-- The subsequence criterion for actual convergence, without compactness assumptions. -/
theorem actualTendsto_of_subsequence_subsequence {E : Type*} [TopologicalSpace E]
    (f : ℕ → E) (x : E)
    (h : ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ms : ℕ → ℕ, StrictMono ms ∧
      Tendsto (fun k => f (ns (ms k))) atTop (𝓝 x)) : Tendsto f atTop (𝓝 x) := by
  by_contra hn
  obtain ⟨s, hs, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.mp hn
  obtain ⟨ns, hns, hnot⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ms, hms, hconv⟩ := h ns hns
  obtain ⟨k, hk⟩ := (hconv.eventually hs).exists
  exact hnot (ms k) hk

/-- L¹ density convergence controls actual integrals against arbitrary bounded
 measurable tests, even when the test changes with the approximation. -/
theorem actualDensity_bounded_test_error_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (D : ℕ → Ω → ℝ) (d : Ω → ℝ)
    (hDi : ∀ n, Integrable (D n) P) (hdi : Integrable d P)
    (hL : Tendsto (fun n => eLpNorm (D n - d) 1 P) atTop (𝓝 0))
    (b : ℕ → Ω → ℝ) (C : ℝ) (_ : 0 ≤ C)
    (hb : ∀ n ω, ‖b n ω‖ ≤ C) :
    Tendsto (fun n => ∫ ω, (D n ω-d ω)*b n ω ∂P) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun n => ∫ ω, ‖D n ω-d ω‖ ∂P) atTop (𝓝 0) := by
    have ht := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞)≠∞)).tendsto.comp hL
    have he (n : ℕ) : (∫ ω, ‖D n ω-d ω‖ ∂P) = (eLpNorm (D n-d) 1 P).toReal := by
      rw [eLpNorm_one_eq_lintegral_eNorm ((hDi n).sub hdi).aestronglyMeasurable]
      simpa only [Pi.sub_apply] using integral_norm_eq_lintegral_eNorm ((hDi n).sub
          hdi).aestronglyMeasurable
    simpa only [he, Function.comp_def, ENNReal.toReal_zero] using ht
  have hbound (n : ℕ) : ‖∫ ω, (D n ω-d ω)*b n ω ∂P‖ ≤ C*(∫ ω, ‖D n ω-d ω‖ ∂P) := by
    have hi := ((hDi n).sub hdi).norm.const_mul C
    have hh := norm_integral_le_of_norm_le (f := fun ω => (D n ω-d ω)*b n ω) hi
        (Eventually.of_forall (fun ω => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb n ω) (norm_nonneg _)).trans_eq (mul_comm _ _)))
    simpa only [integral_const_mul, Pi.sub_apply] using hh
  apply squeeze_zero_norm (fun n => hbound n)
  simpa only [mul_zero] using hnorm.const_mul C

/-- An integrable density times bounded continuous tests respects actual
 convergence in probability, with no uniform-integrability certificate. -/
theorem actualDensity_continuous_test_tendsto {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) (d : Ω → ℝ) (hdi : Integrable d P)
    (X : ℕ → Ω → E) (x : Ω → E) (hX : ∀ n, AEMeasurable (X n) P)
    (_ : AEMeasurable x P) (hl : TendstoInMeasure P X atTop x) (b : E →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, d ω*b (X n ω) ∂P) atTop (𝓝 (∫ ω, d ω*b (x ω) ∂P)) := by
  apply actualTendsto_of_subsequence_subsequence
  intro ns hns
  obtain ⟨ms, hms, hae⟩ := (hl.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms,?_⟩
  apply tendsto_integral_of_dominated_convergence (fun ω => ‖d ω‖*‖b‖)
  · intro n
    exact (hdi.aestronglyMeasurable.mul
      (b.continuous.measurable.comp_aemeasurable (hX _)).aestronglyMeasurable)
  · exact hdi.norm.mul_const _
  · intro n
    filter_upwards with ω
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (b.norm_coe_le_norm _) (norm_nonneg _)
  · filter_upwards [hae] with ω hω
    exact (b.continuous.tendsto _ |>.comp hω).const_mul _

end
end GinibrePoincare
