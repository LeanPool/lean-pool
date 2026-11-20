/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDynamicsStrongMarkov.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDynamicsStoppedPast
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDynamicsRestart
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDynamicsStoppedNoiseIndependence
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianConditionalMarkov
/-!
# Correspondence dynamics strong Markov

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `correspondence_ginibre_stopping_future_past_joint_law`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- Full conditional future law of the original process at any finite stopping
 time, tested against every stopped-past random variable. -/
theorem correspondence_ginibre_stopping_future_past_joint_law
    {Ω A : Type*} [mAmbient : MeasurableSpace Ω] [MeasurableSpace A]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z : {z : Configuration n // CollisionFree z})
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (t : ℝ≥0) (Y : Ω → A) (hY : @Measurable Ω A hτ.measurableSpace _ Y) :
    P.map (fun ω => (Y ω, ginibreBrownianStateProcess α z B (τ ω+t) ω)) =
      ((P.map (fun ω => (Y ω, ginibreBrownianStateProcess α z B (τ ω) ω))).prod
        (P.map (ginibreBrownianFullContinuousNoise n B α))).map
          (fun p => (p.1.1, ginibreCanonicalStateValue α t (p.1.2, p.2))) := by
  let Z := fun ω => (Y ω, ginibreBrownianStateProcess α z B (τ ω) ω)
  let N := fun ω => correspondenceNoiseShift n (τ ω) (ginibreBrownianFullContinuousNoise n B α ω)
  have hState : @Measurable Ω {z : Configuration n // CollisionFree z} hτ.measurableSpace _
      (fun ω => ginibreBrownianStateProcess α z B (τ ω) ω) :=
    (correspondence_ginibre_stopped_value_measurable hn α z.val z.property B P hB hind τ
        hτ).subtype_mk
  have hZpast : @Measurable Ω (A × {z : Configuration n // CollisionFree z}) hτ.measurableSpace _ Z
      :=
    hY.prodMk hState
  have hZa : Measurable Z := hZpast.mono hτ.measurableSpace_le le_rfl
  obtain ⟨hNa, hNLaw, hi⟩ := correspondenceBrownian_stopped_noise_independent n B P hB hind α τ hτ Z
      hZpast
  have hLaw := hi.symm.map_prod_eq_prod_map_map hZa.aemeasurable hNa.aemeasurable
  have hg : Measurable (fun p : (A × {z : Configuration n // CollisionFree z}) ×
      GinibreContinuousNoise n =>
      (p.1.1, ginibreCanonicalStateValue α t (p.1.2, p.2))) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((ginibreCanonicalStateValue_measurable hn α t).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  rw [← hNLaw,← hLaw, Measure.map_map hg (hZa.prodMk hNa)]
  apply Measure.map_congr
  filter_upwards [correspondence_ginibre_restart_all_times hn α z.val z.property B P hB hind] with ω
      hω
  apply congrArg (fun x => (Y ω, x))
  apply Subtype.ext
  exact ((hω (τ ω)).2 t).symm

end
end GinibrePoincare
