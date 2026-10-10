/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.Inductive

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal ENNReal
namespace KamProject.Arnold1963
namespace InductiveResult
variable {n : ℕ} {G Ω : Set (ComplexSpace n)} {ρ β δ γ θ Θ : ℝ≥0} {K M : ℝ}
  {a : ComplexSpace n → ℂ} {f : AnalyticPhaseFunction n G ρ}
  (r : InductiveResult a f Ω β δ γ θ Θ K M)
include r

theorem delta_lt_one : δ < 1 := by
  have hh := r.lower_pos
  have ht := θ.coe_nonneg
  exact_mod_cast (show (δ : ℝ) < 1 by nlinarith)

theorem realSlice_nonempty_of_budget {L : ℝ≥0∞}
    (hloss : realVolume (G \ r.domain) ≤ L) (hL : L < realVolume G) :
    (realSlice r.domain).Nonempty :=
  realSlice_nonempty_of_realVolume_pos (realVolume_pos_of_loss_lt (hloss.trans_lt hL))

theorem nextInput {β₁ δ₁ γ₁ : ℝ≥0}
    (hb : IterationParameters n (ρ - 3 * γ) β₁ δ₁ γ₁ (θ * (1 - δ)) (Θ * (1 + δ))
      K (iterationRemainderBound n M δ β)) :
    IterationInput (Ω := erosion (nonresonantDomain Ω id K (fundamentalCutoff γ (2 * M)))
      ((5 + 7 * Θ) * β)) (f.averagedHamiltonian a) r.perturbation r.inverseFrequency
      β₁ δ₁ γ₁ (θ * (1 - δ)) (Θ * (1 + δ)) K (iterationRemainderBound n M δ β) where
  chart := r.chart
  analytic := r.analytic
  conj := r.conj
  lower := by
    intro p hp v
    simpa only [NNReal.coe_mul, NNReal.coe_sub r.delta_lt_one.le, NNReal.coe_one] using
      (r.derivative_bounds p hp v).1
  upper := by
    intro p hp
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one] using
      (r.derivative_bounds p hp v).2
  perturbation := r.bound.le
  budget := hb

end InductiveResult

namespace IterationInput
variable {n : ℕ} {G Ωbase : Set (ComplexSpace n)} {ρ β δ γ θ Θ : ℝ≥0}
  {K M N₀ D : ℝ} {a : ComplexSpace n → ℂ} {f : AnalyticPhaseFunction n G ρ}
  {g : ComplexSpace n → ComplexSpace n} (s : ResonanceDomainState n K N₀)
  (i : IterationInput (Ω := s.domain Ωbase) a f g β δ γ θ Θ K M)

theorem result_chart_next (hNN : N₀ ≤ fundamentalCutoff γ (2 * M)) :
    AnalyticFrequencyChart (actionFrequency (f.averagedHamiltonian a)) i.result.inverseFrequency
      i.result.domain
      ((s.next i.budget.fundamental.K_pos hNN ((5 + 7 * Θ) * β)).domain Ωbase) := by
  rw [s.next_domain]
  exact i.result.chart

theorem result_measure_budget (hD : TypeD Ωbase D) (hN₀ : 1 ≤ N₀)
    (hNN : N₀ ≤ fundamentalCutoff γ (2 * M)) :
    realVolume (G \ i.result.domain) ≤ ENNReal.ofReal ((θ : ℝ)⁻¹ ^ n) *
      (ENNReal.ofReal (resonanceLossConstant n * D *
        (K * newShellBudget N₀ (fundamentalCutoff γ (2 * M)) +
          (((6 + 7 * Θ) * β : ℝ≥0) : ℝ) * (fundamentalCutoff γ (2 * M)) ^ n)) *
        realVolume Ωbase) :=
  frequency_iteration_measure_budget s i.frequencyChange hD i.budget.dimension_pos
    i.budget.fundamental.K_pos hN₀ i.budget.cutoff_gt_one hNN

theorem result_measure_uniform {G₀ : Set (ComplexSpace n)}
    {A₀ g₀ : ComplexSpace n → ComplexSpace n}
    (c₀ : AnalyticFrequencyChart A₀ g₀ G₀ Ωbase) {θ₀ Θ₀ : ℝ}
    (hθ₀ : 0 < θ₀) (hθ : θ₀ / 2 ≤ (θ : ℝ)) (hΘ₀ : 0 ≤ Θ₀)
    (hupper : ∀ p ∈ G₀, ‖fderiv ℂ A₀ p‖ ≤ Θ₀)
    (hD : TypeD Ωbase D) (hN₀ : 1 ≤ N₀) (hNN : N₀ ≤ fundamentalCutoff γ (2 * M)) :
    realVolume (G \ i.result.domain) ≤ ENNReal.ofReal ((2 * Θ₀ / θ₀) ^ n) *
      (ENNReal.ofReal (resonanceLossConstant n * D *
        (K * newShellBudget N₀ (fundamentalCutoff γ (2 * M)) +
          (((6 + 7 * Θ) * β : ℝ≥0) : ℝ) * (fundamentalCutoff γ (2 * M)) ^ n)) * realVolume G₀) :=
  frequency_measure_to_uniform_action_budget c₀ hθ₀ hθ hΘ₀ hupper
    (i.result_measure_budget s hD hN₀ hNN)

end IterationInput
end KamProject.Arnold1963
