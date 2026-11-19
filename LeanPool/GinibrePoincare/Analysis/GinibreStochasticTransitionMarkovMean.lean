/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionMarkovMean.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMarkovLaw
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionContinuousMean

/-!
# Ginibre stochastic transition Markov mean

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreStationaryContinuousTransitionMean_semigroup`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_state_future_mean {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P)
    (z : {z : Configuration n // CollisionFree z}) (s t : ℝ≥0)
    (v : Configuration n → ℝ) (hv : Measurable v) (C : ℝ) (hC : ∀ z, ‖v z‖ ≤ C) :
    (∫ ω, v (ginibreBrownianStateProcess α z B (s+t) ω).val ∂P)=
      ∫ ω, (∫ N, v (ginibreCanonicalStateValue α t
        (ginibreBrownianStateProcess α z B s ω, N)).val
          ∂P.map (ginibreBrownianFullContinuousNoise n B α)) ∂P := by
  let S := {z : Configuration n // CollisionFree z}
  let ν := P.map (ginibreBrownianFullContinuousNoise n B α)
  have hN := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  let : IsProbabilityMeasure ν := (by infer_instance)
  let Z := fun ω => (Unit.unit, ginibreBrownianStateProcess α z B s ω)
  have hS (r : ℝ≥0) : Measurable (ginibreBrownianStateProcess α z B r) :=
    (ginibreBrownianStateProcess_adapted hn α z B P hB r).mono
      ((ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)).le r) le_rfl
  have hZ : Measurable Z := measurable_const.prodMk (hS s)
  let : IsProbabilityMeasure (P.map Z) := (by infer_instance)
  have hg : Measurable (fun p : Unit × S => v p.2.val) :=
    hv.comp (measurable_subtype_coe.comp measurable_snd)
  have hG : Measurable (fun p : (Unit × S) × GinibreContinuousNoise n =>
      v (ginibreCanonicalStateValue α t (p.1.2, p.2)).val) :=
    hv.comp (measurable_subtype_coe.comp ((ginibreCanonicalStateValue_measurable hn α t).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have hi : Integrable (fun p : (Unit × S) × GinibreContinuousNoise n =>
      v (ginibreCanonicalStateValue α t (p.1.2, p.2)).val) ((P.map Z).prod ν) :=
    (integrable_const C).mono' hG.aestronglyMeasurable (ae_of_all _ fun p => hC _)
  have hlaw := ginibreBrownian_future_past_joint_law hn α z B P hB hiB s t
    (fun _ => Unit.unit) measurable_const
  have he := congrArg (fun ρ : Measure (Unit × S) => ∫ p, v p.2.val ∂ρ) hlaw
  rw [integral_map (measurable_const.prodMk (hS (s+t))).aemeasurable hg.aestronglyMeasurable] at he
  have hF : Measurable (fun p : (Unit × S) × GinibreContinuousNoise n =>
      (p.1.1, ginibreCanonicalStateValue α t (p.1.2, p.2))) :=
    (measurable_fst.comp measurable_fst).prodMk ((ginibreCanonicalStateValue_measurable hn α t).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  rw [integral_map hF.aemeasurable hg.aestronglyMeasurable] at he
  change _=(∫ p : (Unit × S) × GinibreContinuousNoise n,
    v (ginibreCanonicalStateValue α t (p.1.2, p.2)).val ∂(P.map Z).prod ν) at he
  rw [integral_prod _ hi] at he
  have hk : StronglyMeasurable (fun p : Unit × S => ∫ N,
      v (ginibreCanonicalStateValue α t (p.2, N)).val ∂ν) :=
          hG.stronglyMeasurable.integral_prod_right'
  rw [integral_map hZ.aemeasurable hk.aestronglyMeasurable] at he
  exact he

theorem ginibreStationaryContinuousTransitionMean_semigroup {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P)
    (z : Configuration n) (hz : CollisionFree z) (s t : ℝ≥0)
    (v : Configuration n → ℝ) (hv : Measurable v) (C : ℝ) (hC : ∀ z, ‖v z‖ ≤ C) :
    ginibreStationaryContinuousTransitionMean α B P v ((s+t) : ℝ≥0) z=
      ginibreStationaryContinuousTransitionMean α B P
        (fun y => ginibreStationaryContinuousTransitionMean α B P v (t : ℝ) y) (s : ℝ) z := by
  rw [ginibreStationaryContinuousTransitionMean_eq_original hn α P B hB hiB v z hz,
    ginibreStationaryContinuousTransitionMean_eq_original hn α P B hB hiB
      (fun y => ginibreStationaryContinuousTransitionMean α B P v (t : ℝ) y) z hz,
    Real.toNNReal_coe, Real.toNNReal_coe]
  change (∫ ω, v (ginibreBrownianStateProcess α ⟨z, hz⟩ B (s+t) ω).val ∂P)=_
  rw [ginibreBrownian_state_future_mean hn α P B hB hiB ⟨z, hz⟩ s t v hv C hC]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    dsimp only
    have hm : Measurable (fun N : GinibreContinuousNoise n =>
        v (ginibreCanonicalStateValue α t (ginibreBrownianStateProcess α ⟨z, hz⟩ B s ω, N)).val) :=
      hv.comp (measurable_subtype_coe.comp ((ginibreCanonicalStateValue_measurable hn α t).comp
        (measurable_const.prodMk measurable_id)))
    rw [integral_map (ginibreBrownianFullContinuousNoise_measurable n B P hB α).aemeasurable
        hm.aestronglyMeasurable]
    change _=ginibreStationaryContinuousTransitionMean α B P v (t : ℝ)
      (ginibreBrownianStateProcess α ⟨z, hz⟩ B s ω).val
    rw [ginibreStationaryContinuousTransitionMean_eq_original hn α P B hB hiB v
        (ginibreBrownianStateProcess α ⟨z, hz⟩ B s ω).val
        (ginibreBrownianStateProcess α ⟨z, hz⟩ B s ω).property (t : ℝ), Real.toNNReal_coe]
    rfl

end
end GinibrePoincare
