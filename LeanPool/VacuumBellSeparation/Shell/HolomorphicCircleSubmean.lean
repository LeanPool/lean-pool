/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# The squared-norm circle submean inequality

This combines the actual Cauchy mean formula with integral Jensen. It
uses the genuine angular probability average and is valid for vector
valued holomorphic functions as well as the scalar source wave.
-/

@[expose] public section

namespace VacuumBellSeparation

open Complex MeasureTheory Metric Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem circleAverage_norm_sq_le {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R)
    (hf₂ : CircleIntegrable (fun z => ‖f z‖ ^ 2) c R) :
    ‖circleAverage f c R‖ ^ 2 ≤ circleAverage (fun z => ‖f z‖ ^ 2) c R := by
  have hconv : ConvexOn ℝ (univ : Set E) (fun x => ‖x‖ ^ 2) :=
    (convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2
  have h₁ : IntegrableOn (fun θ => f (circleMap c R θ)) (Ioc 0 (2 * Real.pi)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).mp hf
  have h₂ : IntegrableOn (fun θ => ‖f (circleMap c R θ)‖ ^ 2) (Ioc 0 (2 * Real.pi)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).mp hf₂
  have hJ := hconv.map_set_average_le (by fun_prop) isClosed_univ
    (show volume (Ioc 0 (2 * Real.pi)) ≠ 0 by
      simpa only [Real.volume_Ioc, sub_zero, ne_eq, ENNReal.ofReal_eq_zero, not_le]
        using Real.two_pi_pos)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (Filter.Eventually.of_forall fun _ => mem_univ _) h₁ h₂
  simpa only [circleAverage_eq_intervalAverage, uIoc_of_le two_pi_pos.le] using hJ

theorem holomorphic_circle_submean_sq {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c R)) :
    ‖f c‖ ^ 2 ≤ circleAverage (fun z => ‖f z‖ ^ 2) c R := by
  have hc : ContinuousOn f (closedBall c R) := by
    simpa only [closure_ball c hR.ne'] using hf.continuousOn
  have hs := hc.mono sphere_subset_closedBall
  have hmean : circleAverage f c R = f c := by
    apply DiffContOnCl.circleAverage
    simpa only [abs_of_pos hR] using hf
  rw [← hmean]
  exact circleAverage_norm_sq_le (hs.circleIntegrable hR.le)
    ((hs.norm.pow 2).circleIntegrable hR.le)

end VacuumBellSeparation
