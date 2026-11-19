/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionL2Sampling.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionL2Operator
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionL2Continuity

/-!
# Ginibre stochastic transition L 2 sampling

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreOriginalStochasticL2Operator_strong_continuous`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance transitionSamplingFullPathMeasurable (n : ℕ) : MeasurableSpace C(ℝ, Configuration n)
    := borel _
local instance transitionSamplingFullPathBorel (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance transitionSamplingCompactPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance transitionSamplingCompactPathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- A single genuine stationary initial sampling measure for all original
Ginibre time horizons. -/
def ginibreOriginalStationarySamplingMeasure {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (P : Measure Ω) : Measure (((Fin n × Fin 2) → ℝ) × Ω) :=
  (ginibreNormalizingMass n)⁻¹ •
    ((Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))).prod P).withDensity
      (fun x => vandermondeDensity (ginibreHamiltonianOUCoordinateAssembly n x.1))

/-- The global canonical original path started from the collision-free normalization of the
configuration assembled from the real coordinates `x.1`, driven by the noise at `x.2`. -/
def ginibreOriginalStationarySamplePath {Ω : Type*} (n : ℕ) (α : ℝ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (x : ((Fin n × Fin 2) → ℝ) × Ω) :
    C(ℝ, Configuration n) := ginibreDrivenGlobalPathElement α
      (ginibreInitialCollisionNormalize n (ginibreHamiltonianOUCoordinateAssembly n x.1),
        ginibreBrownianFullContinuousNoise n B α x.2)

theorem ginibreOriginalStationarySamplePath_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (ginibreOriginalStationarySamplePath n α B) :=
  (ginibreDrivenGlobalPathElement_measurable hn α).comp
    (((ginibreInitialCollisionNormalize_measurable n).comp
      ((ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable.comp measurable_fst)).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB α).comp measurable_snd))

theorem ginibreOriginalStationarySamplingMeasure_horizon_map {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (P : Measure Ω) [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0) :
    (ginibreOriginalStationarySamplingMeasure n P).map (ginibreGaussianInitialOriginalPath n α T B)=
      ginibreOriginalEquilibriumPathLaw n α T P B := by
  rw [ginibreOriginalStationarySamplingMeasure, Measure.map_smul _
    (ginibreGaussianInitialOriginalPath_measurable hn α T B P hB).aemeasurable]
  rfl

theorem ginibreOriginalStationarySampleEndpoint_measurePreserving {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    MeasurePreserving (fun x => ginibreOriginalStationarySamplePath n α B x (T : ℝ))
      (ginibreOriginalStationarySamplingMeasure n P) (ginibreMeasure n) := by
  have hm := ginibreOriginalStationarySamplePath_measurable hn α B P hB
  refine ⟨(continuous_eval_const _).measurable.comp hm,?_⟩
  have h := ginibreOriginalEquilibriumPathLaw_terminal hn α P B hB hiB T
  rw [←ginibreOriginalStationarySamplingMeasure_horizon_map hn α P B hB T,
    Measure.map_map (continuous_eval_const _).measurable
      (ginibreGaussianInitialOriginalPath_measurable hn α T B P hB)] at h
  exact h

theorem ginibreOriginalStochasticL2Operator_sampling {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    ginibreOriginalStochasticL2Operator hn α P B hB hiB T=
      stationaryEndpointL2Operator (ginibreOriginalStationarySamplingMeasure n P) (ginibreMeasure n)
        (fun x => ginibreOriginalStationarySamplePath n α B x 0)
        (fun x => ginibreOriginalStationarySamplePath n α B x (T : ℝ))
        (by simpa only [NNReal.coe_zero] using
              ginibreOriginalStationarySampleEndpoint_measurePreserving hn α P B hB hiB 0)
        (ginibreOriginalStationarySampleEndpoint_measurePreserving hn α P B hB hiB T) := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℝ
  intro f
  rw [ginibreOriginalStochasticL2Operator_pairing, stationaryEndpointL2Operator_pairing,
    ←ginibreOriginalStationarySamplingMeasure_horizon_map hn α P B hB T]
  have hm : Measurable (fun x : C(Icc (0 : ℝ) (T : ℝ), Configuration n) =>
      f (x ⟨0, ⟨le_rfl, T.property⟩⟩)*g (x ⟨T, ⟨T.property, le_rfl⟩⟩)) :=
    ((Lp.stronglyMeasurable f).measurable.comp (continuous_eval_const _).measurable).mul
      ((Lp.stronglyMeasurable g).measurable.comp (continuous_eval_const _).measurable)
  rw [integral_map (ginibreGaussianInitialOriginalPath_measurable hn α T B P hB).aemeasurable
      hm.aestronglyMeasurable]
  rfl

theorem ginibreOriginalStationarySamplingMeasure_isProbability {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) :
    IsProbabilityMeasure (ginibreOriginalStationarySamplingMeasure n P) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have hm := ginibreOriginalStationarySampleEndpoint_measurePreserving hn α P B hB hiB 0
  let : IsProbabilityMeasure ((ginibreOriginalStationarySamplingMeasure n P).map
      (fun x => ginibreOriginalStationarySamplePath n α B x ((0 : ℝ≥0) : ℝ))) := by
    rw [hm.map_eq]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map hm.measurable.aemeasurable

/-- Genuine strong L² continuity of the actual original stochastic
transition operators, derived from their common stationary path sampling. -/
theorem ginibreOriginalStochasticL2Operator_strong_continuous {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (u : Lp ℝ 2 (ginibreMeasure n)) :
    Continuous (fun T : ℝ≥0 => ginibreOriginalStochasticL2Operator hn α P B hB hiB T u) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  let := ginibreOriginalStationarySamplingMeasure_isProbability hn α P B hB hiB
  apply continuous_iff_seqContinuous.mpr
  intro q T hq
  have hZ : MeasurePreserving (fun x => ginibreOriginalStationarySamplePath n α B x 0)
      (ginibreOriginalStationarySamplingMeasure n P) (ginibreMeasure n) := by
    simpa only [NNReal.coe_zero] using ginibreOriginalStationarySampleEndpoint_measurePreserving hn
        α P B hB hiB 0
  have hpoint : ∀ᵐ x ∂ginibreOriginalStationarySamplingMeasure n P,
      Tendsto (fun k => ginibreOriginalStationarySamplePath n α B x ((q k) : ℝ)) atTop
        (𝓝 (ginibreOriginalStationarySamplePath n α B x (T : ℝ))) := ae_of_all _ (fun x =>
      (ginibreOriginalStationarySamplePath n α B x).continuous.tendsto (T : ℝ) |>.comp
        (NNReal.continuous_coe.tendsto T |>.comp hq))
  have ht := stationaryEndpointL2Operator_tendsto (ginibreOriginalStationarySamplingMeasure n P)
    (ginibreMeasure n) _ hZ _ _
    (fun k => ginibreOriginalStationarySampleEndpoint_measurePreserving hn α P B hB hiB (q k))
    (ginibreOriginalStationarySampleEndpoint_measurePreserving hn α P B hB hiB T) hpoint u
  simpa only [Function.comp_def, ←ginibreOriginalStochasticL2Operator_sampling hn α P B hB hiB]
      using ht

end
end GinibrePoincare
