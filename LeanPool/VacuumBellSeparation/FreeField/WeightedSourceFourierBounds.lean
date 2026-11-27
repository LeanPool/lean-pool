/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSourceFourierComponents

/-!
# Entire Fourier component bounds from the actual reserve wave estimate

The momentum estimate uses the actual displaced coordinate circle and
the maximum modulus principle for the entire momentum Fourier transform.
Thus its center may have zero complex energy.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian Metric Set

theorem weightedSource_fourier_bounds {b : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℝ) (hm : 0 < m) (T : ℝ) (_ : 0 < T)
        (U : Set (EuclideanSpace ℝ (Fin 3))), U ⊆ ball 0 T →
        ∀ (E : ℝ) (z : EuclideanSpace ℂ (Fin 3)), m + ‖z‖ ≤ E →
          ∀ x : ComplexSourceTestSpace hm U,
            ‖complexSourceFieldFourier hm U (WithLp.ofLp z) x‖ ≤
              (C / E * Real.exp (sourceMomentLambda b * T * E)) *
                ‖(sourceReserve hm U ^ b) (complexSourceTestInclusion hm U x)‖ ∧
            ‖complexSourceMomentumFourier hm U (WithLp.ofLp z) x‖ ≤
              (C / E ^ 2 * Real.exp (sourceMomentLambda b * T * E)) *
                ‖(sourceReserve hm U ^ b) (complexSourceTestInclusion hm U x)‖ := by
  obtain ⟨C, hC, hwave⟩ := weightedSource_reserveWave_bound hb hb1
  refine ⟨C, hC, ?_⟩
  intro m hm T hT U hU E z hz x
  have hmE : m ≤ E := by linarith [norm_nonneg z]
  have hE : 0 < E := hm.trans_le hmE
  let R : ℝ := ‖(sourceReserve hm U ^ b) (complexSourceTestInclusion hm U x)‖
  have hR : 0 ≤ R := norm_nonneg _
  have hRate : 0 < sourceEvaluationRate b := sourceEvaluationRate_pos hb hb1
  have hW (E' : ℝ) (hmE' : m ≤ E') (w : ComplexSpacetime)
      (hw : w ∈ complexShell m) (hsize : euclidSq w ≤ (2 * E') ^ 2) :
      ‖complexSourceTestWave hm U w x‖ ≤
        (C / E' * Real.exp (sourceEvaluationRate b * T * E')) * R := by
    obtain ⟨heq, hbound⟩ := hwave m hm T hT U hU E' hmE' w hw hsize
    rw [← heq x]
    exact hbound (complexSourceTestInclusion hm U x)
  have hfield : ‖complexSourceFieldFourier hm U (WithLp.ofLp z) x‖ ≤
      (C / E * Real.exp (sourceEvaluationRate b * T * E)) * R := by
    apply complexSourceFieldFourier_norm_bound hm U (spatialFourierEnergy m z)
    · exact hW E hmE _ (spatialFourierEnergy_pair_in_shell m z).1
        (actualSpatialEnergy_in_ball hm.le z hz (spatialFourierEnergy_sq m z))
    · exact hW E hmE _ (spatialFourierEnergy_pair_in_shell m z).2
        (actualSpatialEnergy_in_ball hm.le z hz (by rw [neg_sq, spatialFourierEnergy_sq]))
  have hmomentum : ‖complexSourceMomentumFourier hm U (WithLp.ofLp z) x‖ ≤
      (C / E ^ 2 * Real.exp (7 * sourceEvaluationRate b * T * E)) * R := by
    let f : ℂ → ℂ := fun ζ => complexSourceMomentumFourier hm U
      (WithLp.ofLp (spatialEnergyCircle z E ζ)) x
    have hcurve : Differentiable ℂ
        (fun ζ : ℂ => WithLp.ofLp (spatialEnergyCircle z E ζ)) := by
      apply differentiable_pi.mpr
      intro j
      simp only [spatialEnergyCircle, PiLp.add_apply, PiLp.single_apply]
      split_ifs <;> fun_prop
    have hf : Differentiable ℂ f :=
      (differentiable_complexSourceMomentumFourier hm U x).comp hcurve
    have hcircle : ∀ ζ ∈ frontier (ball (0 : ℂ) 1),
        ‖f ζ‖ ≤ (C / E ^ 2 * Real.exp (7 * sourceEvaluationRate b * T * E)) * R := by
      intro ζ hζ
      have hnζ : ‖ζ‖ = 1 := by
        simpa only [frontier_ball _ one_ne_zero, mem_sphere, dist_zero_right] using hζ
      let w := spatialEnergyCircle z E ζ
      let e := spatialFourierEnergy m w
      have he : e ^ 2 = spatialFourierEnergySquared m w := spatialFourierEnergy_sq m w
      obtain ⟨hebound, hene⟩ := spatialEnergyCircle_energy_norm_lower hm.le hE z hz hnζ he
      have h7 : m ≤ 7 * E := by linarith
      have hp := hW (7 * E) h7 (e, WithLp.ofLp w)
        (actualSpatialEnergy_shell m w he)
        (by have h := spatialEnergyCircle_shell_size hm.le hE z hz hnζ he
            convert h.le using 1; ring)
      have hn := hW (7 * E) h7 (-e, WithLp.ofLp w)
        (actualSpatialEnergy_shell m w (by rw [neg_sq, he]))
        (by have h := spatialEnergyCircle_shell_size hm.le hE z hz hnζ
              (show (-e) ^ 2 = spatialFourierEnergySquared m w by rw [neg_sq, he])
            convert h.le using 1; ring)
      have hcomp := complexSourceMomentumFourier_norm_bound hm U hene (WithLp.ofLp w) x hp hn
      have hdiv := div_le_div_of_nonneg_left
        (show 0 ≤ (C / (7 * E) * Real.exp (sourceEvaluationRate b * T * (7 * E))) * R by positivity)
        hE hebound
      have halg : ((C / (7 * E) * Real.exp (sourceEvaluationRate b * T * (7 * E))) * R) / E =
          (1 / 7 : ℝ) * ((C / E ^ 2 * Real.exp (7 * sourceEvaluationRate b * T * E)) * R) := by
        rw [show sourceEvaluationRate b * T * (7 * E) = 7 * sourceEvaluationRate b * T * E by ring]
        ring
      have hh := hcomp.trans hdiv
      rw [halg] at hh
      exact hh.trans (mul_le_of_le_one_left (by positivity) (by norm_num))
    have hzero := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      hf.diffContOnCl hcircle (subset_closure (by simp : (0 : ℂ) ∈ ball 0 1))
    have hc0 : spatialEnergyCircle z E 0 = z := by
      ext j
      simp [spatialEnergyCircle, PiLp.single_apply]
    simpa only [f, hc0] using hzero
  have hexp₁ : Real.exp (sourceEvaluationRate b * T * E) ≤
      Real.exp (sourceMomentLambda b * T * E) := by
    apply Real.exp_le_exp.mpr
    rw [sourceMomentLambda_eq]
    nlinarith [mul_pos (mul_pos hRate hT) hE]
  have hexp₇ : Real.exp (7 * sourceEvaluationRate b * T * E) ≤
      Real.exp (sourceMomentLambda b * T * E) := by
    apply Real.exp_le_exp.mpr
    rw [sourceMomentLambda_eq]
    nlinarith [mul_pos (mul_pos hRate hT) hE]
  constructor
  · exact hfield.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp₁ (by positivity)) hR)
  · exact hmomentum.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp₇ (by positivity)) hR)

end VacuumBellSeparation
