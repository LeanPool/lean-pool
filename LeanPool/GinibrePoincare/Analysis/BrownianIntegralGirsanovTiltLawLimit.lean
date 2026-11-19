/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralGirsanovTiltLawLimit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltDensityTest
public import LeanPool.GinibrePoincare.Analysis.BrownianIntegralGirsanovMeasure
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Brownian integral Girsanov tilt law limit

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `actualVaryingDensity_constantLaw_limit`,
`actualIdentDistrib_of_probability_limits`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction
namespace GinibrePoincare
noncomputable section

/-- Change-of-measure identity for a genuine nonnegative real density. -/
theorem actualRealDensity_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (d : Ω → ℝ) (hd : Integrable d P) (hp : 0 ≤ᵐ[P] d) (f : Ω → ℝ) :
    (∫ ω, f ω ∂P.withDensity (fun ω => ENNReal.ofReal (d ω))) =
      ∫ ω, d ω * f ω ∂P := by
  change (∫ ω, f ω ∂P.withDensity (ENNReal.ofReal ∘ d)) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (ENNReal.measurable_ofReal.comp_aemeasurable hd.aemeasurable)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hp] with ω hω
  simp [ENNReal.toReal_ofReal hω]

/-- Actual L¹ likelihood convergence and convergence in probability transfer
constant laws to the limiting tilted probability measure. This is a reusable
limit theorem, not an assertion of Girsanov without its approximation proofs. -/
theorem actualVaryingDensity_constantLaw_limit {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω)
    (D : ℕ → Ω → ℝ) (d : Ω → ℝ)
    (hDi : ∀ n, Integrable (D n) P) (hdi : Integrable d P)
    (hDp : ∀ n, 0 ≤ᵐ[P] D n) (hdp : 0 ≤ᵐ[P] d)
    (_ : ∀ n, (∫ ω, D n ω ∂P) = 1) (hdn : (∫ ω, d ω ∂P) = 1)
    (hL : Tendsto (fun n => eLpNorm (D n - d) 1 P) atTop (𝓝 0))
    (X : ℕ → Ω → E) (x : Ω → E) (hX : ∀ n, AEMeasurable (X n) P)
    (hx : AEMeasurable x P) (hl : TendstoInMeasure P X atTop x)
    (μ : Measure E) [IsProbabilityMeasure μ]
    (hlaw : ∀ n, HasLaw (X n) μ (P.withDensity (fun ω => ENNReal.ofReal (D n ω)))) :
    HasLaw x μ (P.withDensity (fun ω => ENNReal.ofReal (d ω))) := by
  let Q := P.withDensity (fun ω => ENNReal.ofReal (d ω))
  let : IsProbabilityMeasure Q := gaussianDensity_isProbabilityMeasure_of_integral_one P d hdi hdp
      hdn
  have hxm : AEMeasurable x Q := hx.mono_ac (withDensity_absolutelyContinuous P _)
  refine ⟨hxm, ?_⟩
  let : IsProbabilityMeasure (Q.map x) := (by infer_instance)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro b
  have ht := actualVaryingDensity_continuous_test_tendsto P D d hDi hdi hL X x hX hx hl b
  have he (n : ℕ) : (∫ ω, D n ω*b (X n ω) ∂P) = ∫ y, b y ∂μ := by
    rw [← actualRealDensity_integral P (D n) (hDi n) (hDp n)]
    exact (hlaw n).integral_comp b.continuous.aestronglyMeasurable
  simp_rw [he] at ht
  have heq := tendsto_nhds_unique ht tendsto_const_nhds
  rw [integral_map hxm b.continuous.aestronglyMeasurable]
  change (∫ ω, b (x ω) ∂P.withDensity (fun ω => ENNReal.ofReal (d ω))) = _
  rw [actualRealDensity_integral P d hdi hdp]
  exact heq

/-- Actual convergence in probability on two probability spaces preserves
identical distributions of the approximating random variables. -/
theorem actualIdentDistrib_of_probability_limits {Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → E) (Y : ℕ → Ω' → E) (x : Ω → E) (y : Ω' → E)
    (hi : ∀ n, IdentDistrib (X n) (Y n) P Q)
    (hx : TendstoInMeasure P X atTop x) (hy : TendstoInMeasure Q Y atTop y) :
    IdentDistrib x y P Q := by
  have hdX := hx.tendstoInDistribution (fun n => (hi n).aemeasurable_fst)
  have hdY := hy.tendstoInDistribution (fun n => (hi n).aemeasurable_snd)
  have hdXY : TendstoInDistribution X atTop y (fun _ => P) Q := by
    refine ⟨fun n => (hi n).aemeasurable_fst, hdY.aemeasurable_limit,?_⟩
    have he : (fun n : ℕ => (⟨P.map (X n), (by infer_instance)⟩ : ProbabilityMeasure E)) =
        (fun n : ℕ => (⟨Q.map (Y n), (by infer_instance)⟩ : ProbabilityMeasure E)) := by
      funext n
      apply Subtype.ext
      exact (hi n).map_eq
    rw [he]
    exact hdY.tendsto
  exact ⟨hdX.aemeasurable_limit, hdY.aemeasurable_limit, tendstoInDistribution_unique X hdX hdXY⟩

end
end GinibrePoincare
