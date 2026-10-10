/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.FrequencyPreparation

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963

theorem realVolume_pos_of_loss_lt {n : ℕ} {G S : Set (ComplexSpace n)}
    (hloss : realVolume (G \ S) < realVolume G) : 0 < realVolume S := by
  by_contra hn
  have hz : realVolume S = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have hcover : realSlice G ⊆ realSlice (G \ S) ∪ realSlice S := by
    intro x hx
    by_cases hs : complexify x ∈ S
    · exact Or.inr hs
    · exact Or.inl ⟨hx, hs⟩
  have hh := (measure_mono (μ := realLebesgue n) hcover).trans (measure_union_le _ _)
  change realVolume G ≤ realVolume (G \ S) + realVolume S at hh
  rw [hz, add_zero] at hh
  exact (not_lt_of_ge hh) hloss

theorem realSlice_nonempty_of_realVolume_pos {n : ℕ} {G : Set (ComplexSpace n)}
    (hG : 0 < realVolume G) : (realSlice G).Nonempty :=
  nonempty_of_measure_ne_zero (ne_of_gt hG)

namespace FrequencyChangeInput
variable {n : ℕ} {A g Δ : ComplexSpace n → ComplexSpace n}
  {G Ω : Set (ComplexSpace n)} {β κ θ Θ : ℝ≥0}
  (h : FrequencyChangeInput A g Δ G Ω β κ θ Θ)
include h

theorem iterationE_nonempty_iff (K N : ℝ) :
    (h.iterationE K N).Nonempty ↔ (h.iterationDomain K N).Nonempty := by
  constructor
  · rintro ⟨_, p, hp, _⟩
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, p, hp, by simp⟩

theorem iteration_nonempty_of_measure_budget {K N : ℝ} {L : ℝ≥0∞}
    (hloss : realVolume (G \ h.iterationDomain K N) ≤ L) (hL : L < realVolume G) :
    (realSlice (h.iterationDomain K N)).Nonempty ∧ (h.iterationE K N).Nonempty := by
  have hp := realSlice_nonempty_of_realVolume_pos (realVolume_pos_of_loss_lt (hloss.trans_lt hL))
  refine ⟨hp, ?_⟩
  obtain ⟨x, hx⟩ := hp
  exact ⟨complexify x, complexify x, hx, by simp⟩

end FrequencyChangeInput

theorem frequency_measure_to_action_budget {n : ℕ} {G S G₀ Ω₀ : Set (ComplexSpace n)}
    {A₀ g₀ : ComplexSpace n → ComplexSpace n} (c₀ : AnalyticFrequencyChart A₀ g₀ G₀ Ω₀)
    {θ Θ₀ B : ℝ} (_hθ : 0 < θ) (hΘ₀ : 0 ≤ Θ₀)
    (hupper : ∀ p ∈ G₀, ‖fderiv ℂ A₀ p‖ ≤ Θ₀)
    (hloss : realVolume (G \ S) ≤ ENNReal.ofReal (θ⁻¹ ^ n) *
      (ENNReal.ofReal B * realVolume Ω₀)) :
    realVolume (G \ S) ≤ ENNReal.ofReal ((Θ₀ / θ) ^ n) *
      (ENNReal.ofReal B * realVolume G₀) := by
  calc
    _ ≤ ENNReal.ofReal (θ⁻¹ ^ n) *
        (ENNReal.ofReal B * (ENNReal.ofReal (Θ₀ ^ n) * realVolume G₀)) :=
      hloss.trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl (c₀.realVolume_image_le hΘ₀ hupper)))
    _ = _ := by
      rw [div_pow, div_eq_mul_inv, inv_pow, ENNReal.ofReal_mul (pow_nonneg hΘ₀ n)]
      ac_rfl

theorem frequency_measure_to_uniform_action_budget {n : ℕ}
    {G S G₀ Ω₀ : Set (ComplexSpace n)} {A₀ g₀ : ComplexSpace n → ComplexSpace n}
    (c₀ : AnalyticFrequencyChart A₀ g₀ G₀ Ω₀) {θ θ₀ Θ₀ B : ℝ}
    (hθ₀ : 0 < θ₀) (hθ : θ₀ / 2 ≤ θ) (hΘ₀ : 0 ≤ Θ₀)
    (hupper : ∀ p ∈ G₀, ‖fderiv ℂ A₀ p‖ ≤ Θ₀)
    (hloss : realVolume (G \ S) ≤ ENNReal.ofReal (θ⁻¹ ^ n) *
      (ENNReal.ofReal B * realVolume Ω₀)) :
    realVolume (G \ S) ≤ ENNReal.ofReal ((2 * Θ₀ / θ₀) ^ n) *
      (ENNReal.ofReal B * realVolume G₀) := by
  have hθp : 0 < θ := lt_of_lt_of_le (by positivity) hθ
  apply (frequency_measure_to_action_budget c₀ hθp hΘ₀ hupper hloss).trans
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (by positivity)
  calc
    Θ₀ / θ ≤ Θ₀ / (θ₀ / 2) := div_le_div_of_nonneg_left hΘ₀ (by positivity) hθ
    _ = 2 * Θ₀ / θ₀ := by ring

end KamProject.Arnold1963
