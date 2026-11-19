/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionContinuousMean.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionL2ProductPairing

/-!
# Ginibre stochastic transition continuous mean

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreStationaryContinuousTransitionMean_bound`,
`ginibreOriginalStochasticL2Operator_measurable_mean_pairing`,
`ginibreStationaryContinuousTransitionMean_sub`,
`ginibreStationaryContinuousTransitionMean_eq_original`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(ℝ, Configuration n)`. -/
local instance instBorelGinibreStochasticTransitionContinuousMean58 (n : ℕ) :
    MeasurableSpace C(ℝ, Configuration n) := borel _
local instance (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩

/-- Actual continuous canonical path version, with the fixed collision-free
fallback confined to the zero-measure exceptional initial configurations. -/
def ginibreStationaryContinuousTransitionMean {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (α : ℝ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (v : Configuration n → ℝ) (t : ℝ) (z : Configuration n) : ℝ :=
  ∫ ω, v (ginibreEquilibriumPath α (ginibreCollisionFreeDefault n).val
    (ginibreCollisionFreeDefault n).property B (z, ω) t) ∂P

theorem ginibreStationaryContinuousTransitionMean_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (v : Configuration n → ℝ) (hv : Measurable v) :
    Measurable (fun p : ℝ × Configuration n => ginibreStationaryContinuousTransitionMean α B P v p.1
        p.2) := by
  have hp := ginibreEquilibriumPath_measurable hn α (ginibreCollisionFreeDefault n).val
    (ginibreCollisionFreeDefault n).property B P hB
  have h : Measurable (fun q : (ℝ × Configuration n) × Ω =>
      v (ginibreEquilibriumPath α (ginibreCollisionFreeDefault n).val
        (ginibreCollisionFreeDefault n).property B (q.1.2, q.2) q.1.1)) :=
    hv.comp (continuous_eval.measurable.comp
      ((hp.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).prodMk
        (measurable_fst.comp measurable_fst)))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem ginibreStationaryContinuousTransitionMean_bound {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (α : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (v : Configuration n → ℝ)
    (C : ℝ) (hC : ∀ z, ‖v z‖ ≤ C) (t : ℝ) (z : Configuration n) :
    ‖ginibreStationaryContinuousTransitionMean α B P v t z‖≤C := by
  simpa [ginibreStationaryContinuousTransitionMean] using
    (norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => v (ginibreEquilibriumPath α (ginibreCollisionFreeDefault n).val
        (ginibreCollisionFreeDefault n).property B (z, ω) t))
      (ae_of_all P fun ω => hC _))

theorem ginibreStationaryContinuousTransitionMean_eq_original_ae {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (v : Configuration n → ℝ) :
    ∀ᵐ z ∂ginibreMeasure n, ∀ t : ℝ,
      ginibreStationaryContinuousTransitionMean α B P v t z=
        ∫ ω, v (ginibreBrownianMaximalProcess n α z B t.toNNReal ω) ∂P := by
  have h := Measure.ae_ae_of_ae_prod (ginibre_equilibrium_path_eq_original hn α
    (ginibreCollisionFreeDefault n).val (ginibreCollisionFreeDefault n).property B P hB hiB)
  filter_upwards [h] with z hz
  intro t
  apply integral_congr_ae
  exact hz.mono fun ω hω => congrArg v (hω t)

theorem ginibreOriginalStochasticL2Operator_measurable_mean_pairing {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f g : Lp ℝ 2 (ginibreMeasure n)) (v : Configuration n → ℝ)
    (hg : (g : Configuration n → ℝ) =ᵐ[ginibreMeasure n] v)
    (hv : Measurable v) (C : ℝ) (hC : ∀ z, ‖v z‖ ≤ C) :
    inner ℝ f (ginibreOriginalStochasticL2Operator hn α P B hB hiB T g)=
      ∫ z, f z * ginibreStationaryContinuousTransitionMean α B P v (T : ℝ) z ∂ginibreMeasure n := by
  rw [ginibreOriginalStochasticL2Operator_bounded_measurable_pairing hn α P B hB hiB T f g v hg hv C
      hC]
  apply integral_congr_ae
  filter_upwards [ginibreStationaryContinuousTransitionMean_eq_original_ae hn α P B hB hiB v] with z
      hz
  rw [hz (T : ℝ), Real.toNNReal_coe]

theorem ginibreStationaryContinuousTransitionMean_integrable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (v : Configuration n → ℝ) (hv : Measurable v) (C : ℝ) (hC : ∀ z, ‖v z‖ ≤ C)
    (t : ℝ) (z : Configuration n) :
    Integrable (fun ω => v (ginibreEquilibriumPath α (ginibreCollisionFreeDefault n).val
      (ginibreCollisionFreeDefault n).property B (z, ω) t)) P := by
  have hpath := (ginibreEquilibriumPath_measurable hn α (ginibreCollisionFreeDefault n).val
    (ginibreCollisionFreeDefault n).property B P hB).comp ((measurable_const (a := z)).prodMk
        measurable_id)
  apply (integrable_const C).mono'
    (hv.comp ((continuous_eval_const t).measurable.comp hpath)).aestronglyMeasurable
  exact ae_of_all _ fun ω => hC _

theorem ginibreStationaryContinuousTransitionMean_sub {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (v w : Configuration n → ℝ) (hv : Measurable v) (hw : Measurable w)
    (C D : ℝ) (hC : ∀ z, ‖v z‖ ≤ C) (hD : ∀ z, ‖w z‖ ≤ D) (t : ℝ) (z : Configuration n) :
    ginibreStationaryContinuousTransitionMean α B P (fun z => v z-w z) t z=
      ginibreStationaryContinuousTransitionMean α B P v t z-
        ginibreStationaryContinuousTransitionMean α B P w t z :=
  integral_sub (ginibreStationaryContinuousTransitionMean_integrable hn α P B hB v hv C hC t z)
    (ginibreStationaryContinuousTransitionMean_integrable hn α P B hB w hw D hD t z)

theorem ginibreStationaryContinuousTransitionMean_eq_original {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (v : Configuration n → ℝ)
    (z : Configuration n) (hz : CollisionFree z) (t : ℝ) :
    ginibreStationaryContinuousTransitionMean α B P v t z=
      ∫ ω, v (ginibreBrownianMaximalProcess n α z B t.toNNReal ω) ∂P := by
  have hfree : ginibreFreeInitialVersion (ginibreCollisionFreeDefault n).val
      (ginibreCollisionFreeDefault n).property z=⟨z, hz⟩ := by simp [ginibreFreeInitialVersion, hz]
  apply integral_congr_ae
  filter_upwards [ginibreBrownianMaximalLifetime_top_ae hn α z hz B P hB hiB] with ω hω
  apply congrArg v
  simp only [ginibreEquilibriumPath, hfree, ginibreDrivenGlobalPathElement,
    show ginibreDrivenMaximalLifetime n α (ginibreBrownianFullContinuousNoise n B α ω).val z=⊤ from
        hω,
    dite_eq_left True.intro, ContinuousMap.coe_mk, ginibreBrownianMaximalProcess]

end
end GinibrePoincare
