/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorInvariantUniqueness.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorInvariantIntegral
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorInvariantLimit
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorRealErgodicity
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorStochasticSemigroup
/-!
# Correspondence operator invariant uniqueness

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperator_invariant_probability_unique`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
/-- Every bounded measurable observable has its Ginibre expectation under any
arbitrary invariant probability of the actual positive-speed diffusion. -/
theorem correspondenceOperator_invariant_bounded_integral
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (α : ℝ≥0) (hα : 0 < α) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (ν : Measure {z : Configuration n // CollisionFree z}) [IsProbabilityMeasure ν]
    (hInv : ∀ t, ginibreBrownianTransitionKernel hn α B P t ∘ₘ ν = ν.map Subtype.val)
    (v : Configuration n → ℝ) (hv : Measurable v) (C : ℝ) (hb : ∀ z, ‖v z‖ ≤ C) :
    (∫z, v z∂(ν.map Subtype.val))=∫z, v z∂ginibreMeasure n := by
  let := ginibreMeasure_isProbabilityMeasure hn
  let ρ := ν.map Subtype.val
  have hρ : ρ ≪ ginibreMeasure n :=
    correspondenceOperator_invariant_absolutelyContinuous_ginibre hn α hα B P hB hind 1
      (by norm_num) ν (hInv 1)
  have hvLp : MemLp v 2 (ginibreMeasure n) :=
    MemLp.of_bound hv.aestronglyMeasurable C (ae_of_all _ hb)
  let u := hvLp.toLp v
  let F := fun k : ℕ => ginibreOriginalStochasticL2Operator hn α P B hB hind (k : ℝ≥0) u
  let r := fun k : ℕ => fun z : Configuration n =>
    ginibreStationaryContinuousTransitionMean α B P v (k : ℝ≥0) z
  have hc : 0<α/(n : ℝ≥0) := div_pos hα (by exact_mod_cast hn)
  have ht : Tendsto (fun k : ℕ => (α/(n : ℝ≥0))*(k : ℝ≥0)) atTop atTop :=
    Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop
  have hlim := (correspondenceOperatorRealEvolution_ergodic hn u).comp ht
  have hmean : (∫z, u z∂ginibreMeasure n)=∫z, v z∂ginibreMeasure n :=
    integral_congr_ae hvLp.coeFn_toLp
  rw [hmean] at hlim
  have hF : Tendsto F atTop (𝓝 (ginibreRealConstantL2 n hn (∫z, v z∂ginibreMeasure n))) := by
    apply hlim.congr
    intro k
    exact (congrArg (fun L => L u) (correspondenceOperator_stochastic_semigroup_eq hn α P B hB hind
        (k : ℝ≥0))).symm
  have hr (k : ℕ) := ginibreOriginalStochasticL2Operator_bounded_representative hn α P B hB hind
    (k : ℝ≥0) u v hvLp.coeFn_toLp hv C hb
  apply correspondenceOperator_invariant_limit hn ρ hρ F r
    (∫z, v z∂ginibreMeasure n) (∫z, v z∂ρ) C hF
  · intro k; exact (hr k).2.2
  · intro k; exact (hr k).1.aestronglyMeasurable
  · intro k; exact ae_of_all _ (hr k).2.1
  · intro k
    exact correspondenceOperator_invariant_observable_integral hn α hα B P hB hind ν hρ
      (k : ℝ≥0) (hInv _) v hv C hb

/-- Uniqueness among all invariant probabilities, with no symmetry or density
integrability restriction. The endpoint is equality of actual configuration laws. -/
theorem correspondenceOperator_invariant_probability_unique
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (α : ℝ≥0) (hα : 0 < α) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (ν : Measure {z : Configuration n // CollisionFree z}) [IsProbabilityMeasure ν]
    (hInv : ∀ t, ginibreBrownianTransitionKernel hn α B P t ∘ₘ ν = ν.map Subtype.val) :
    ν.map Subtype.val=ginibreMeasure n := by
  let := ginibreMeasure_isProbabilityMeasure hn
  apply Measure.ext
  intro A hA
  have hv : Measurable (A.indicator (fun _ : Configuration n => (1 : ℝ))) :=
    measurable_const.indicator hA
  have hb : ∀z, ‖A.indicator (fun _ : Configuration n => (1 : ℝ)) z‖≤1 := by
    intro z; by_cases hz : z∈A <;> simp [hz]
  have he := correspondenceOperator_invariant_bounded_integral hn α hα B P hB hind ν hInv
    _ hv 1 hb
  simp only [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one, measureReal_def] at he
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp he
end
end GinibrePoincare
