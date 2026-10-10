/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.NumericalBudget

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963

theorem mem_erosion_angleStrip {n : ℕ} {q : ComplexSpace n} {σ r : ℝ≥0}
    (hq : ‖imagPart q‖ + (r : ℝ) ≤ σ) : q ∈ erosion (angleStrip n σ) r := by
  intro q' hd
  apply (mem_angleStrip_iff _ _).2
  intro j
  have hv : |(q' j - q j).im| ≤ (r : ℝ) :=
    (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm (q' - q) j).trans
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hd))
  have hj : |(q j).im| ≤ ‖imagPart q‖ := norm_le_pi_norm (imagPart q) j
  have he : (q' j).im = (q' j - q j).im + (q j).im := by simp
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

namespace FundamentalParameters
variable {n : ℕ} {ρ β δ γ : ℝ≥0} {K M Θ : ℝ}
  (b : FundamentalParameters n ρ β δ γ K M Θ)
include b

theorem double_gamma_le : γ + γ ≤ ρ := by
  exact_mod_cast (show (γ : ℝ) + γ ≤ ρ by linarith [b.angle_width])

theorem beta_delta_le_gamma : β + δ ≤ γ := by
  have hδ := δ.coe_nonneg
  exact_mod_cast (show (β : ℝ) + δ ≤ γ by linarith [b.action_loss, b.angle_loss])

theorem triple_beta_le : β + β + β ≤ ρ - (δ + δ) := by
  rw [← NNReal.coe_le_coe, NNReal.coe_sub b.double_delta_le]
  simp only [NNReal.coe_add]
  linarith [b.action_loss, b.angle_loss, b.angle_width, δ.coe_nonneg]

theorem action_buffer_loss_lt :
    2 * (δ : ℝ) + (3 * β + δ) < 2 * γ := by
  have hδ : (0 : ℝ) < δ := b.delta_pos
  linarith [b.action_loss, b.angle_loss]

theorem target_angle_buffer {q : ComplexSpace n}
    (hq : q ∈ angleStrip n (ρ - (γ + γ))) :
    q ∈ erosion (angleStrip n (ρ - (δ + δ))) ((β + β + β) + δ) := by
  apply mem_erosion_angleStrip
  change ‖imagPart q‖ ≤ (↑(ρ - (γ + γ)) : ℝ) at hq
  rw [NNReal.coe_sub b.double_gamma_le, NNReal.coe_add] at hq
  rw [NNReal.coe_sub b.double_delta_le]
  simp only [NNReal.coe_add]
  linarith [b.action_buffer_loss_lt]

theorem target_subset (E : Set (ComplexSpace n)) :
    phaseDomain (erosion E (β + β)) (ρ - (γ + γ)) ⊆
      generatingTarget E (angleStrip n (ρ - (δ + δ))) β := by
  intro z hz
  exact ⟨hz.1, erosion_antitone_radius _ (show β + β + β ≤ (β + β + β) + δ
    from le_self_add) (b.target_angle_buffer hz.2)⟩

theorem shifted_angle_tail {q Q : ComplexSpace n}
    (hQ : Q ∈ angleStrip n (ρ - (γ + γ))) (hd : dist q Q ≤ β) :
    q ∈ angleStrip n (ρ - (δ + γ)) := by
  have hδγ : δ + γ ≤ γ + γ := by
    exact_mod_cast (show (δ : ℝ) + γ ≤ γ + γ by
      linarith [b.angle_loss, δ.coe_nonneg])
  have hδγρ := hδγ.trans b.double_gamma_le
  have hb : ‖imagPart Q‖ + (β : ℝ) ≤ ↑(ρ - (δ + γ)) := by
    change ‖imagPart Q‖ ≤ (↑(ρ - (γ + γ)) : ℝ) at hQ
    rw [NNReal.coe_sub b.double_gamma_le, NNReal.coe_add] at hQ
    rw [NNReal.coe_sub hδγρ, NNReal.coe_add]
    have hh : (β : ℝ) + δ ≤ γ := b.beta_delta_le_gamma
    linarith
  exact mem_erosion_angleStrip hb hd

end FundamentalParameters

theorem segment_subset_erosion_of_displacement {n : ℕ} {E : Set (ComplexSpace n)}
    {P p : ComplexSpace n} {β : ℝ≥0} (hP : P ∈ erosion E (β + β))
    (hp : ‖p - P‖ ≤ β) : segment ℝ P p ⊆ erosion E β := by
  have hs : segment ℝ P p ⊆ Metric.closedBall P (β : ℝ) :=
    (convex_closedBall P (β : ℝ)).segment_subset
      (Metric.mem_closedBall_self β.coe_nonneg)
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hp)
  exact fun _ hx => mem_erosion_of_dist_le hP (hs hx)

end KamProject.Arnold1963
