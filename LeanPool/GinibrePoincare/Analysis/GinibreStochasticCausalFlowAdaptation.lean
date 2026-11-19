/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCausalFlowAdaptation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathClippedLocalFlow
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousPastPath

/-! Causal actual Brownian path selections are adapted to the genuine augmented past. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_causal_flow_stronglyAdapted {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (α τ : ℝ) (hτ : 0 < τ)
    (Φ : C(Icc (-1 : ℝ) 1, Configuration n) → C(Icc 0 τ, Configuration n))
    (hMeas : @Measurable _ _ (borel C(Icc (-1 : ℝ) 1, Configuration n))
      (borel C(Icc 0 τ, Configuration n)) Φ)
    (hCausal : ∀ N Q (t : Icc 0 τ),
      (∀ u ∈ Icc 0 (t : ℝ), N (Set.projIcc (-1 : ℝ) 1 (by norm_num) u) =
        Q (Set.projIcc (-1 : ℝ) 1 (by norm_num) u)) → Φ N t = Φ Q t) :
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (fun s ω => Φ (ginibreConfigurationBrownianContinuousPath n B α ω) (Set.projIcc 0 τ hτ.le (s :
          ℝ))) := by
  intro s
  let t := Set.projIcc 0 τ hτ.le (s : ℝ)
  have hts : (t : ℝ) ≤ (s : ℝ) := by
    rw [show (t : ℝ) = max 0 (min τ (s : ℝ)) from rfl]
    exact max_le s.coe_nonneg (min_le_right _ _)
  have hPastMeas := ginibreConfigurationBrownianPastContinuousPath_measurable n B P hB α s
  have hAE₁ := ginibreConfigurationBrownianContinuousPath_ae n B P hB α
  have hAE₂ := ginibreConfigurationBrownianPastContinuousPath_ae n B P hB α s
  have hm := ginibreBrownianFamilyPastSpace_le B P (fun i => (hB i).toIsPreBrownianReal) s
  let mPast := ginibreBrownianFamilyPastSpace B s
  let mAug := ginibreNullAugmentation (mAmbient := mAmbient) P mPast
  have hAug := ginibreNullAugmentation_le (mAmbient := mAmbient) P mPast hm
  let μ := P.trim hAug
  have : μ.IsComplete := ginibreNullAugmentation_trim_complete (mAmbient := mAmbient) P mPast hm
  let : MeasurableSpace C(Icc 0 τ, Configuration n) := borel _
  let : BorelSpace C(Icc 0 τ, Configuration n) := ⟨rfl⟩
  have hEval : @Measurable C(Icc 0 τ, Configuration n) (Configuration n) (borel _) _ (fun f => f t)
      :=
    (continuous_eval_const t).measurable
  have hSelectedPast : @Measurable Ω (Configuration n) mAug _
      (fun ω => Φ (ginibreConfigurationBrownianPastContinuousPath n B α s ω) t) :=
    hEval.comp (hMeas.comp hPastMeas)
  have hEqual : (fun ω => Φ (ginibreConfigurationBrownianPastContinuousPath n B α s ω) t) =ᵐ[μ]
      (fun ω => Φ (ginibreConfigurationBrownianContinuousPath n B α ω) t) := by
    have hAE := ginibreNullAugmentation_ae_transfer (mAmbient := mAmbient) P mPast hm _ (hAE₁.and
        hAE₂)
    filter_upwards [hAE] with ω hω
    apply hCausal
    intro u hu
    rw [hω.2 _, hω.1 _]
    have hcu : ((Set.projIcc (-1 : ℝ) 1 (by norm_num) u) : ℝ) ≤ (s : ℝ) := by
      rw [Set.coe_projIcc]
      exact (max_le (by linarith [hu.1]) (min_le_right _ _)).trans (hu.2.trans hts)
    rw [min_eq_left hcu]
  exact ((aemeasurable_iff_measurable (μ := μ)).mp (hSelectedPast.aemeasurable.congr
      hEqual)).stronglyMeasurable

end
end GinibrePoincare
