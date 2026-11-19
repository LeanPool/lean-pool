/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionBoundedOperator.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionBoundedResolvent

/-!
# Ginibre stochastic transition bounded operator

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreOriginalStochasticL2Operator_bounded_representative`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
theorem actualL2_eq_toLp_of_pairings {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (u : Lp ℝ 2 μ) (r : E → ℝ) (hr : MemLp r 2 μ)
    (hp : ∀ g : Lp ℝ 2 μ, inner ℝ g u=∫ z, g z*r z ∂μ) : u=hr.toLp r := by
  apply ext_inner_left ℝ
  intro g
  rw [hp, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hr.coeFn_toLp] with z hz
  simp [hz, mul_comm]

private theorem ginibreOriginalStochasticL2Operator_eq_toLp_mean {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P]
    [P.IsComplete] (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f : Lp ℝ 2 (ginibreMeasure n)) (v : Configuration n → ℝ)
    (hf : (f : Configuration n → ℝ) =ᵐ[ginibreMeasure n] v)
    (hv : Measurable v) (C : ℝ) (hC : ∀ z, ‖v z‖ ≤ C)
    (hr : MemLp (fun z => ginibreStationaryContinuousTransitionMean α B P v (T : ℝ) z) 2
      (ginibreMeasure n)) :
    ginibreOriginalStochasticL2Operator hn α P B hB hiB T f = hr.toLp _ :=
  actualL2_eq_toLp_of_pairings (ginibreMeasure n) _ _ hr (fun g =>
    ginibreOriginalStochasticL2Operator_measurable_mean_pairing hn α P B hB hiB T g f v hf hv C hC)

private theorem ginibreStationaryContinuousTransitionMean_measurable_at {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P]
    [P.IsComplete] (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (T : ℝ≥0) (v : Configuration n → ℝ) (hv : Measurable v) :
    Measurable (fun z => ginibreStationaryContinuousTransitionMean α B P v (T : ℝ) z) := by
  have hbase := ginibreStationaryContinuousTransitionMean_joint_measurable hn α P B hB v hv
  have hparam : Measurable (fun z : Configuration n => ((T : ℝ), z)) :=
    measurable_const.prodMk measurable_id
  have h := hbase.comp hparam
  exact h

theorem ginibreOriginalStochasticL2Operator_bounded_representative {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f : Lp ℝ 2 (ginibreMeasure n)) (v : Configuration n → ℝ)
    (hf : (f : Configuration n → ℝ) =ᵐ[ginibreMeasure n] v)
    (hv : Measurable v) (C : ℝ) (hC : ∀ z, ‖v z‖ ≤ C) :
    let r := fun z => ginibreStationaryContinuousTransitionMean α B P v (T : ℝ) z
    Measurable r ∧ (∀ z, ‖r z‖≤C) ∧
      ((ginibreOriginalStochasticL2Operator hn α P B hB hiB T f : Lp ℝ 2 (ginibreMeasure n)) :
          Configuration n → ℝ)=ᵐ[ginibreMeasure n] r := by
  have := ginibreMeasure_isProbabilityMeasure hn
  intro r
  have hm : Measurable r :=
    ginibreStationaryContinuousTransitionMean_measurable_at hn α P B hB T v hv
  have hb (z : Configuration n) : ‖r z‖≤C := ginibreStationaryContinuousTransitionMean_bound α P B v
      C hC (T : ℝ) z
  have hr : MemLp r 2 (ginibreMeasure n) := MemLp.of_bound hm.aestronglyMeasurable C (ae_of_all _
      hb)
  have he := ginibreOriginalStochasticL2Operator_eq_toLp_mean hn α P B hB hiB T f v hf hv C hC hr
  refine ⟨hm, hb,?_⟩
  rw [he]
  exact hr.coeFn_toLp

end
end GinibrePoincare
