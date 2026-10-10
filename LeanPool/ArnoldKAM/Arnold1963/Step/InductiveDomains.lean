/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.AveragingConstruction
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.FrequencyChartCongr
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.PhaseCauchy

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace KamProject.Arnold1963
namespace IterationInput
variable {n : ℕ} {G Ω : Set (ComplexSpace n)} {ρ β δ γ θ Θ : ℝ≥0} {K M : ℝ}
  {a : ComplexSpace n → ℂ} {f : AnalyticPhaseFunction n G ρ}
  {g : ComplexSpace n → ComplexSpace n} (i : IterationInput (Ω := Ω) a f g β δ γ θ Θ K M)
include i

/-- The action domain retained by corrected frequency inversion and finite resonance removal. -/
def newDomain : Set (ComplexSpace n) :=
  i.frequencyChange.iterationDomain K (fundamentalCutoff γ (2 * M))

/-- The wider action domain used before the final inductive restriction. -/
def wideDomain : Set (ComplexSpace n) :=
  erosion (i.frequencyChange.iterationE K (fundamentalCutoff γ (2 * M))) (β + β)

theorem newDomain_subset : i.newDomain ⊆ erosion G β :=
  (subset_closedBallNeighborhood _ (3 * β)).trans (i.frequencyChange.iterationE_subset _ _)

theorem newChart : AnalyticFrequencyChart (actionFrequency i.newIntegrable)
    i.frequencyChange.newInverse i.newDomain
      (erosion (nonresonantDomain Ω id K (fundamentalCutoff γ (2 * M))) ((5 + 7 * Θ) * β)) :=
  (i.frequencyChange.iterationChart _ _).congr (fun _ hp =>
    i.frequency_eventually (erosion_subset _ _ (i.newDomain_subset hp)))

theorem new_derivative_bounds {p} (hp : p ∈ i.newDomain) (v : ComplexSpace n) :
    ((θ : ℝ) * (1 - (δ : ℝ))) * ‖v‖ ≤ ‖fderiv ℂ (actionFrequency i.newIntegrable) p v‖ ∧
    ‖fderiv ℂ (actionFrequency i.newIntegrable) p v‖ ≤ ((Θ : ℝ) * (1 + (δ : ℝ))) * ‖v‖ := by
  rw [(i.frequency_eventually (erosion_subset _ _ (i.newDomain_subset hp))).fderiv_eq]
  exact i.frequencyChange.iteration_derivative_bounds _ _ hp v

theorem frequency_displacement {p} (hp : p ∈ i.newDomain) :
    ‖actionFrequency i.newIntegrable p - actionFrequency a p‖ < (β : ℝ) * δ := by
  rw [(i.frequency_eventually (erosion_subset _ _ (i.newDomain_subset hp))).self_of_nhds,
    add_sub_cancel_left]
  exact ((f.frequencyShift_bound i.budget.beta_pos i.perturbation).norm_le
    (i.newDomain_subset hp)).trans_lt i.budget.mean_gradient_small

theorem new_width_pos : 0 < ρ - 3 * γ := by
  apply tsub_pos_of_lt
  exact_mod_cast i.budget.angle_width

theorem phase_buffer : phaseDomain i.newDomain (ρ - 3 * γ) ⊆
    erosion (phaseDomain i.wideDomain (ρ - (γ + γ))) β := by
  have hγ : 3 * γ ≤ ρ := by exact_mod_cast i.budget.angle_width.le
  have hg2 : γ + γ ≤ ρ := by nlinarith
  have hβ : β ≤ ρ - (γ + γ) := by
    apply (le_tsub_iff_right hg2).mpr
    nlinarith [i.budget.beta_lt_gamma]
  apply phaseDomain_buffer_of_neighborhood hβ
  · rw [tsub_tsub]
    exact tsub_le_tsub_left (by nlinarith [i.budget.beta_lt_gamma]) ρ
  · exact i.frequencyChange.iteration_target_buffer _ _

theorem phase_subset_wide : phaseDomain i.newDomain (ρ - 3 * γ) ⊆
    phaseDomain i.wideDomain (ρ - (γ + γ)) :=
  i.phase_buffer.trans (erosion_subset _ _)

theorem phase_subset_old_erosion : phaseDomain i.newDomain (ρ - 3 * γ) ⊆
    erosion (phaseDomain G ρ) β := by
  have hγ : 3 * γ ≤ ρ := by exact_mod_cast i.budget.angle_width.le
  have hβγ : β ≤ 3 * γ := by nlinarith [i.budget.beta_lt_gamma]
  apply Subset.trans (Set.prod_mono i.newDomain_subset
    (angleStrip_mono (tsub_le_tsub_left hβγ ρ)))
  exact phaseDomain_shrink_subset_erosion G (hβγ.trans hγ)

end IterationInput
end KamProject.Arnold1963
