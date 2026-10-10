/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Iteration.Construction
public import LeanPool.ArnoldKAM.Arnold1963.Iteration.DerivativeBudget

/-!
Uniform domain buffers, transformation estimates, and derivative bounds for the actual states.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

theorem phase_succ (s : ℕ) : h.phase b (s + 1) =
    phaseDomain (h.state b s).step.domain (width n ρ₀ δ₁ s - 3 * gamma n δ₁ s) := by
  simp only [phase, actionDomain, state_succ, State.next, width_succ]

theorem phase_buffer (s : ℕ) : h.phase b (s + 1) ⊆ erosion (h.phase b s) (beta δ₁ s) := by
  rw [h.phase_succ b]
  exact (h.state b s).step.phase_buffer

theorem displacement_lt (s : ℕ) {z : ComplexPhaseSpace n} (hz : z ∈ h.phase b (s + 1)) :
    ‖(h.transformation b s).toFun z - z‖ < (beta δ₁ s : ℝ) := by
  rw [h.phase_succ b] at hz
  exact (h.state b s).step.displacement_lt z hz

theorem transformation_periodic (s : ℕ) {z : ComplexPhaseSpace n}
    (hz : z ∈ h.phase b (s + 1)) (k : FourierIndex n) :
    (h.transformation b s).toFun (phaseShift k z) =
      phaseShift k ((h.transformation b s).toFun z) := by
  rw [h.phase_succ b] at hz
  exact (h.state b s).step.periodic z hz k

theorem transformation_real (s : ℕ) {z : ComplexPhaseSpace n}
    (hz : z ∈ h.phase b (s + 1)) :
    (h.transformation b s).toFun (conjPhase z) =
      conjPhase ((h.transformation b s).toFun z) := by
  rw [h.phase_succ b] at hz
  exact (h.state b s).step.conj_compatible z hz

include b in
theorem width_gt_third (s : ℕ) : (ρ₀ : ℝ) / 3 < (width n ρ₀ δ₁ s : ℝ) := by
  have hh := (uniform_bounds_of_threshold b.dimension_pos b.lower_pos
    (zero_lt_one.trans b.upper_gt_one) b.small s).2.2.1
  have hr : (0 : ℝ) < ρ₀ := b.width_pos
  linarith

theorem remainder_derivative (s : ℕ) {z : ComplexPhaseSpace n}
    (hz : z ∈ h.phase b (s + 1)) :
    ‖fderiv ℂ (h.state b (s + 1)).perturbation.toFun z‖ <
      (delta δ₁ s : ℝ) * beta δ₁ (s + 1) := by
  rw [h.phase_succ b] at hz
  have hh := (h.state b s).step.derivative z hz
  rw [remainder_eq_next_parameter b.delta_pos] at hh
  exact hh.trans (b.first_derivative_budget s)

theorem remainder_coordinate_derivative (s : ℕ) {z : ComplexPhaseSpace n}
    (hz : z ∈ h.phase b (s + 1)) (j : Fin n ⊕ Fin n) :
    ‖fderiv ℂ (h.state b (s + 1)).perturbation.toFun z (phaseBasis j)‖ <
      (delta δ₁ s : ℝ) * beta δ₁ (s + 1) := by
  have hh := (fderiv ℂ (h.state b (s + 1)).perturbation.toFun z).le_opNorm (phaseBasis j)
  rw [norm_phaseBasis, mul_one] at hh
  exact hh.trans_lt (h.remainder_derivative b s hz)

theorem remainder_second_derivative (s : ℕ) {z : ComplexPhaseSpace n}
    (hz : z ∈ h.phase b (s + 1)) (j k : Fin n ⊕ Fin n) :
    ‖fderiv ℂ (fderiv ℂ (h.state b (s + 1)).perturbation.toFun) z
      (phaseBasis j) (phaseBasis k)‖ < (delta δ₁ s : ℝ) := by
  rw [h.phase_succ b] at hz
  have hh := (h.state b s).step.second_derivative z hz j k
  rw [remainder_eq_next_parameter b.delta_pos] at hh
  exact hh.trans (b.second_derivative_budget s)

theorem frequency_bounds (s : ℕ) {p : ComplexSpace n} (hp : p ∈ h.actionDomain b s)
    (v : ComplexSpace n) :
    (θ₀ : ℝ) / 2 * ‖v‖ ≤ ‖fderiv ℂ (actionFrequency (h.state b s).integrable) p v‖ ∧
      ‖fderiv ℂ (actionFrequency (h.state b s).integrable) p v‖ ≤ 2 * (Θ₀ : ℝ) * ‖v‖ := by
  constructor
  · exact (mul_le_mul_of_nonneg_right (lower_gt_half b.lower_pos b.delta_quarter s).le
      (norm_nonneg v)).trans ((h.state b s).input.lower p hp v)
  · exact ((fderiv ℂ (actionFrequency (h.state b s).integrable) p).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (((h.state b s).input.upper p hp).trans
        (upper_lt_twice (zero_lt_one.trans b.upper_gt_one) b.delta_quarter s).le) (norm_nonneg v))

theorem frequency_displacement (s : ℕ) {p : ComplexSpace n}
    (hp : p ∈ h.actionDomain b (s + 1)) :
    ‖actionFrequency (h.state b (s + 1)).integrable p -
      actionFrequency (h.state b s).integrable p‖ < (beta δ₁ s : ℝ) * delta δ₁ s :=
  (h.state b s).step.frequency_displacement p hp

end KamProject.Arnold1963.Iteration.InitialData
