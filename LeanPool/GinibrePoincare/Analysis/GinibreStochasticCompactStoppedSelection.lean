/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCompactStoppedSelection.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathCompactClippedFlow
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticAdaptedLocalSelection
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousConfigurationNoise

/-! The original singular Brownian equation holds up to a genuine positive stopping time. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_compact_stopped_local_solution_selection {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) (z : Configuration n) (hz : CollisionFree z) :
    ∃ τ : ℝ, ∃ hτ : τ > 0, ∃ K : Set (Configuration n),
      IsCompact K ∧ (∀ x ∈ K, CollisionFree x) ∧ ∃ X : Ω → C(Icc 0 τ, Configuration n), ∃ θ : Ω →
          ℝ≥0,
      @Measurable _ _ _ (borel C(Icc 0 τ, Configuration n)) X ∧
      (∀ ω, X ω ⟨0, ⟨le_rfl, hτ.le⟩⟩ = z) ∧
      (∀ ω t, X ω t ∈ K) ∧
      StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
        (fun s ω => X ω (Set.projIcc 0 τ hτ.le (s : ℝ))) ∧
      IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
        (fun ω => (θ ω : WithTop ℝ≥0)) ∧
      (∀ ω, 0 < θ ω ∧ (θ ω : ℝ) ≤ τ) ∧
      ∀ᵐ ω ∂P, ∀ t : Icc 0 τ, (t : ℝ) ≤ (θ ω : ℝ) →
        X ω t = z+ginibreConfigurationBrownianNoise n B α ω t+
          ∫ s in (0 : ℝ)..t, ginibreLangevinDrift n α (X ω (Set.projIcc 0 τ hτ.le s)) := by
  obtain ⟨δ, hδ, τ, hτ, K, hK, hKCF, Φ, hMeas, hZero, hCF, hEq, hCausal⟩ :=
    ginibreDrivenPath_compact_clipped_measurable_local_flow n α z hz
  let X := fun ω => Φ (ginibreConfigurationBrownianContinuousPath n B α ω)
  let U := ginibreConfigurationContinuousNoise n B α
  let r := drivenNoiseClipRadius δ
  have hr : 0 < r := drivenNoiseClipRadius_pos δ hδ
  let T : ℝ≥0 := min τ.toNNReal 1
  have hT : 0 < T := lt_min (Real.toNNReal_pos.mpr hτ) (by norm_num)
  let θ : Ω → ℝ≥0 := hittingBtwn U {x | r ≤ ‖x‖} 0 T
  have hθT (ω : Ω) : θ ω ≤ T := hittingBtwn_le (u := U) (s := {x | r ≤ ‖x‖}) (n := 0) (m := T) ω
  have hθ1 (ω : Ω) : θ ω ≤ 1 := (hθT ω).trans (min_le_right _ _)
  have hθτ (ω : Ω) : (θ ω : ℝ) ≤ τ := by
    have hh := (hθT ω).trans (min_le_left _ _)
    have hh' : (θ ω : ℝ) ≤ (τ.toNNReal : ℝ) := by exact_mod_cast hh
    simpa only [Real.coe_toNNReal _ hτ.le] using hh'
  have hθpos (ω : Ω) : 0 < θ ω := drivenContinuous_closed_hitting_pos U _
    (isClosed_le continuous_const continuous_norm) T hT ω
    (ginibreConfigurationContinuousNoise_continuous n B α ω)
    (by simpa [U, ginibreConfigurationContinuousNoise_zero] using not_le_of_gt hr)
  have hStop : IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB
      i).toIsPreBrownianReal))
      (fun ω => (θ ω : WithTop ℝ≥0)) := ginibreContinuous_norm_exit_isStoppingTime _ U
    (ginibreConfigurationContinuousNoise_stronglyAdapted n B P hB α)
    (ginibreConfigurationContinuousNoise_continuous n B α) r T
  refine ⟨τ, hτ, K, hK, hKCF, X, θ, hMeas.comp
      (ginibreConfigurationBrownianContinuousPath_measurable n B P hB α),
    fun ω => hZero _, fun ω t => hCF _ t,
    ginibreBrownian_causal_flow_stronglyAdapted n B P hB α τ hτ Φ hMeas hCausal,
    hStop, fun ω => ⟨hθpos ω, hθτ ω⟩,?_⟩
  filter_upwards [ginibreConfigurationBrownianContinuousPath_ae n B P hB α,
    ginibreConfigurationBrownianNoise_actual n B P hB α,
    ginibreConfigurationContinuousNoise_actual_ae n B P hB α] with ω hPath hNoise hActual
  intro t ht
  have htθ : (t : ℝ).toNNReal ≤ θ ω := Real.toNNReal_le_iff_le_coe.mpr ht
  have ht1 : (t : ℝ) ≤ 1 := ht.trans (by exact_mod_cast hθ1 ω)
  have hNorm : ‖ginibreConfigurationBrownianNoise n B α ω t‖ ≤ r := by
    have h := drivenContinuous_norm_le_until_hitting U r T ω
      (ginibreConfigurationContinuousNoise_continuous n B α ω)
      (by simp [U, ginibreConfigurationContinuousNoise_zero, hr.le]) (t : ℝ).toNNReal htθ
    dsimp only [U] at h
    rw [hActual _ (htθ.trans (hθ1 ω)), Real.coe_toNNReal _ t.property.1] at h
    exact h
  have hClip : drivenBoundedNoiseExtension (Configuration n)
      (drivenNoiseClipSmall δ hδ (ginibreConfigurationBrownianContinuousPath n B α ω)).val t =
      ginibreConfigurationBrownianNoise n B α ω t := by
    have htm : (t : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [t.property.1], ht1⟩
    change drivenNoiseClip r
      (ginibreConfigurationBrownianContinuousPath n B α ω (Set.projIcc (-1 : ℝ) 1 (by norm_num) t)-
        ginibreConfigurationBrownianContinuousPath n B α ω ⟨0, by norm_num⟩) = _
    rw [Set.projIcc_of_mem (by norm_num) htm, hPath ⟨t, htm⟩, hPath ⟨0, by norm_num⟩, hNoise.2,
        sub_zero]
    exact drivenNoiseClip_eq _ hr _ hNorm
  exact (hEq (ginibreConfigurationBrownianContinuousPath n B α ω) t).trans (by rw [hClip])

end
end GinibrePoincare
