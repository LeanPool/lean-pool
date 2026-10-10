/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Iteration.Estimates
public import LeanPool.ArnoldKAM.Arnold1963.Iteration.LimitDomain

/-!
The actual infinite Hamiltonian iteration and its positive-measure limiting action domain.
Every stage is recursively constructed from initial data and its numerical threshold.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal ENNReal
namespace KamProject.Arnold1963
open Iteration

/-- The constructed infinite iteration and its canonical maps, estimates and measure bounds. -/
structure Theorem2Result {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0}
    {κ D : ℝ} (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
    (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D) : Prop where
  initial_domain : h.actionDomain b 0 = h.domain
  initial_hamiltonian : ∀ z, h.hamiltonian b 0 z = h.integrable z.1 + h.perturbation.toFun z
  phase_buffer : ∀ s, h.phase b (s + 1) ⊆ erosion (h.phase b s) (beta δ₁ s)
  width : ∀ s, (ρ₀ : ℝ) / 3 < (Iteration.width n ρ₀ δ₁ s : ℝ)
  phase_nonempty : ∀ s, (h.phase b s).Nonempty
  displacement : ∀ s, ∀ z ∈ h.phase b (s + 1),
    ‖(h.transformation b s).toFun z - z‖ < (beta δ₁ s : ℝ)
  derivative : ∀ s, ∀ z ∈ h.phase b (s + 1), ‖fderiv ℂ (h.transformation b s).toFun z‖ < 2
  identity : ∀ s z, h.integrable (h.cumulative b s z).1 +
    h.perturbation.toFun (h.cumulative b s z) = h.hamiltonian b s z
  perturbation : ∀ s, (h.state b (s + 1)).perturbation.uniformNorm <
    Iteration.perturbation n δ₁ (s + 1)
  first_derivative : ∀ s, ∀ z ∈ h.phase b (s + 1),
    ‖fderiv ℂ (h.state b (s + 1)).perturbation.toFun z‖ <
      (delta δ₁ s : ℝ) * beta δ₁ (s + 1)
  second_derivative : ∀ s, ∀ z ∈ h.phase b (s + 1), ∀ j k : Fin n ⊕ Fin n,
    ‖fderiv ℂ (fderiv ℂ (h.state b (s + 1)).perturbation.toFun) z
      (phaseBasis j) (phaseBasis k)‖ < (delta δ₁ s : ℝ)
  frequency_chart : ∀ s, AnalyticFrequencyChart
    (actionFrequency (h.state b s).integrable) (h.state b s).inverseFrequency
    (h.actionDomain b s) ((h.state b s).ar.domain Ω₀)
  frequency_bounds : ∀ s, ∀ p ∈ h.actionDomain b s, ∀ v,
    (θ₀ : ℝ) / 2 * ‖v‖ ≤ ‖fderiv ℂ (actionFrequency (h.state b s).integrable) p v‖ ∧
      ‖fderiv ℂ (actionFrequency (h.state b s).integrable) p v‖ ≤ 2 * (Θ₀ : ℝ) * ‖v‖
  frequency_displacement : ∀ s, ∀ p ∈ h.actionDomain b (s + 1),
    ‖actionFrequency (h.state b (s + 1)).integrable p -
      actionFrequency (h.state b s).integrable p‖ < (beta δ₁ s : ℝ) * delta δ₁ s
  finite_loss : ∀ s, realVolume (h.domain \ h.actionDomain b s) <
    ENNReal.ofReal κ * realVolume h.domain
  limit_loss : realVolume (h.domain \ h.limitDomain b) < ENNReal.ofReal κ * realVolume h.domain
  limit_volume : ENNReal.ofReal (1 - κ) * realVolume h.domain < realVolume (h.limitDomain b)
  limit_positive : 0 < realVolume (h.limitDomain b)
  limit_nonempty : (realSlice (h.limitDomain b)).Nonempty

theorem theorem2 {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
    (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
    (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D) : Theorem2Result b h where
  initial_domain := h.domain_zero b
  initial_hamiltonian := fun _ => rfl
  phase_buffer := h.phase_buffer b
  width := InitialData.width_gt_third b
  phase_nonempty := h.phase_nonempty b
  displacement := fun s _ hz => h.displacement_lt b s hz
  derivative := fun s => (h.transformation b s).derivative_bound
  identity := h.cumulative_identity b
  perturbation := h.perturbation_bound b
  first_derivative := fun s _ hz => h.remainder_derivative b s hz
  second_derivative := fun s _ hz j k => h.remainder_second_derivative b s hz j k
  frequency_chart := fun s => (h.state b s).input.chart
  frequency_bounds := fun s _ hp v => h.frequency_bounds b s hp v
  frequency_displacement := fun s _ hp => h.frequency_displacement b s hp
  finite_loss := h.finite_loss b
  limit_loss := h.limit_loss b
  limit_volume := h.limit_volume_gt b
  limit_positive := h.limit_volume_pos b
  limit_nonempty := h.limit_realSlice_nonempty b

end KamProject.Arnold1963
