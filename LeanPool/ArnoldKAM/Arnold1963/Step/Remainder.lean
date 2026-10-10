/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.Construction
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.FourierReconstruction

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963

/-- The sum of separate error estimates before applying the final remainder budget. -/
def fundamentalRawBound (n : ℕ) (M K Θ δ β : ℝ) : ℝ :=
  (1 / 2 : ℝ) * n ^ 2 * Θ * (homologicalBound n M K δ / δ) ^ 2 +
    (((2 * n : ℝ) / Real.exp 1) ^ n * M ^ 2 / δ ^ (n + 1)) +
    (n * M / β) * (homologicalBound n M K δ / δ)

namespace FundamentalInput
variable {n : ℕ} {G E : Set (ComplexSpace n)} {ρ β δ γ : ℝ≥0} {K M Θ : ℝ}
  {h : ComplexSpace n → ℂ} {f : AnalyticPhaseFunction n G ρ}
  (i : FundamentalInput (E := E) (β := β) (δ := δ) (γ := γ) (K := K) (M := M) (Θ := Θ) h f)

/-- The transformed total Hamiltonian minus the original integrable Hamiltonian. -/
def remainder (z : ComplexPhaseSpace n) : ℂ :=
  h (i.transform z).1 + f.toFun (i.transform z) - h z.1

include i

theorem first_variation_cancel {z : ComplexPhaseSpace n}
    (hz : z ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ))) :
    fderiv ℂ h z.1 ((i.transform z).1 - z.1) +
      fourierTruncation (f.fourierCoeff z.1) (fundamentalCutoff γ M) (i.transform z).2 = 0 := by
  have hP := erosion_subset E (β + β) hz.1
  have he := (i.generatingData.equations (i.budget.target_subset E hz)).1
  have hd : (i.transform z).1 - z.1 = qGradient i.generator.toFun (z.1, (i.transform z).2) := by
    change (i.transform z).1 = z.1 + qGradient i.generator.toFun (z.1, (i.transform z).2) at he
    rw [he, add_sub_cancel_left]
  rw [hd, fderiv_eq_actionFrequency h z.1]
  exact homological_equation (z := (z.1, (i.transform z).2))
    (ω := actionFrequency h) f (i.domain_subset hP)
    (analyticOnNhd_actionFrequency i.integrable.analytic _ (i.domain_subset hP))
    i.budget.K_pos (i.nonresonant z.1 hP) (zero_lt_one.trans i.budget.cutoff_gt_one)
    (i.mean_zero z.1 hP)

theorem taylor_bound {z : ComplexPhaseSpace n}
    (hz : z ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ))) :
    ‖h (i.transform z).1 - h z.1 - fderiv ℂ h z.1 ((i.transform z).1 - z.1)‖ ≤
      (1 / 2 : ℝ) * n ^ 2 * Θ * (homologicalBound n M K δ / δ) ^ 2 := by
  have he := norm_taylor_remainder_le_of_coordinate_bound
    ((i.action_segment hz).trans (erosion_subset G β)) i.integrable.analytic
    i.budget.theta_pos.le i.integrable.hessian_bound
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by have := i.budget.theta_pos; positivity)
  exact pow_le_pow_left₀ (norm_nonneg _) (i.action_displacement hz) 2

theorem tail_bound {z : ComplexPhaseSpace n}
    (hz : z ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ))) :
    ‖f.toFun (z.1, (i.transform z).2) -
      fourierTruncation (f.fourierCoeff z.1) (fundamentalCutoff γ M) (i.transform z).2‖ ≤
      (((2 * n : ℝ) / Real.exp 1) ^ n * M ^ 2 / (δ : ℝ) ^ (n + 1)) := by
  have hδγρ : δ + γ ≤ ρ := by
    have hh := i.budget.angle_loss
    have hh' := i.budget.angle_width
    have hδ := δ.coe_nonneg
    exact_mod_cast (show (δ : ℝ) + γ ≤ ρ by linarith)
  have he := f.norm_sub_fourierTruncation_le (N := fundamentalCutoff γ M)
    (i.domain_subset (erosion_subset E (β + β) hz.1)) i.budget.dimension_pos
    (show (0 : ℝ) < δ from i.budget.delta_pos) i.budget.delta_lt.le
    γ.coe_nonneg (show (↑(ρ - (δ + γ)) : ℝ) ≤ (ρ : ℝ) - ((δ : ℝ) + γ) by
      rw [NNReal.coe_sub hδγρ, NNReal.coe_add]) (i.transformed_angle hz)
  rw [i.budget.exp_cutoff] at he
  apply he.trans
  calc
    _ ≤ ((((2 * n : ℝ) / Real.exp 1) ^ n * M / (δ : ℝ) ^ (n + 1))) * M := by
      apply mul_le_mul_of_nonneg_right _ i.budget.perturbation_pos.le
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left i.perturbation_bound (by positivity)
    _ = _ := by ring

theorem perturbation_composition_bound {z : ComplexPhaseSpace n}
    (hz : z ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ))) :
    ‖f.toFun (i.transform z) - f.toFun (z.1, (i.transform z).2)‖ ≤
      (n * M / β) * (homologicalBound n M K δ / δ) := by
  let q := (i.transform z).2
  have hq : q ∈ angleStrip n ρ :=
    angleStrip_mono (tsub_le_self : ρ - (δ + γ) ≤ ρ) (i.transformed_angle hz)
  have hf : AnalyticOnNhd ℂ (fun p => f.toFun (p, q)) G := fun p hp =>
    (f.analytic (p, q) ⟨hp, hq⟩).comp (f := fun p => (p, q))
      (analyticAt_id.prod analyticAt_const)
  have hM : NormBoundOn (fun p => f.toFun (p, q)) G M :=
    ⟨i.budget.perturbation_pos.le, fun p hp =>
      (f.norm_le_iff.mp i.perturbation_bound).norm_le ⟨hp, hq⟩⟩
  have hD : NormBoundOn (fderiv ℂ (fun p => f.toFun (p, q))) (erosion G β) (M / β) :=
    ⟨div_nonneg i.budget.perturbation_pos.le β.coe_nonneg, fun p hp =>
      norm_fderiv_le_div_of_mem_erosion i.budget.beta_pos hf hM hp⟩
  have he := norm_sub_le_of_analytic_segment_bound (i.action_segment hz)
    (hf.mono (erosion_subset G β)) hD
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast i.budget.dimension_pos
  have hm : 0 ≤ M / (β : ℝ) := div_nonneg i.budget.perturbation_pos.le β.coe_nonneg
  have hc : M / (β : ℝ) ≤ n * M / β := by
    have hh := mul_le_mul_of_nonneg_right hn hm
    simpa only [one_mul, mul_div_assoc] using hh
  exact he.trans (mul_le_mul hc (i.action_displacement hz) (norm_nonneg _)
    (by have := i.budget.perturbation_pos; positivity))

theorem remainder_decomposition {z : ComplexPhaseSpace n}
    (hz : z ∈ phaseDomain (erosion E (β + β)) (ρ - (γ + γ))) :
    i.remainder z =
      (h (i.transform z).1 - h z.1 - fderiv ℂ h z.1 ((i.transform z).1 - z.1)) +
      (f.toFun (z.1, (i.transform z).2) -
        fourierTruncation (f.fourierCoeff z.1) (fundamentalCutoff γ M) (i.transform z).2) +
      (f.toFun (i.transform z) - f.toFun (z.1, (i.transform z).2)) := by
  have he := i.first_variation_cancel hz
  dsimp [remainder]
  linear_combination he

theorem remainder_norm_bound : NormBoundOn i.remainder
    (phaseDomain (erosion E (β + β)) (ρ - (γ + γ)))
    (fundamentalRawBound n M K Θ δ β) := by
  refine ⟨?_, fun z hz => ?_⟩
  · have := i.budget.theta_pos
    have := i.budget.perturbation_pos
    have := i.budget.K_pos
    have := constantL5_pos n
    dsimp [fundamentalRawBound, homologicalBound]
    positivity
  · rw [i.remainder_decomposition hz]
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (i.taylor_bound hz) (i.tail_bound hz)))
      (i.perturbation_composition_bound hz))

end FundamentalInput
end KamProject.Arnold1963
