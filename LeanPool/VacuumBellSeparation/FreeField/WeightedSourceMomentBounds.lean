/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSourceMomentFunctional
public import LeanPool.VacuumBellSeparation.FreeField.WeightedSourceEntireGrowth
public import LeanPool.VacuumBellSeparation.Gaussian.EntireMomentCoefficientBound

/-!
# Actual weighted polynomial moment estimates

The exact Cauchy coefficient identity and the entire Fourier growth
bound give the manuscript base 5 Lambda and dimensional prefactors.
No moment representation or moment bound is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped BigOperators

theorem weightedSource_moment_bounds {b : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℝ) (hm : 0 < m) (T : ℝ) (_ : 0 < T)
        (U : Set (EuclideanSpace ℝ (Fin 3))), U ⊆ Metric.ball 0 T →
        ∀ (α : Fin 3 → ℕ) (x : ComplexSourceTestSpace hm U),
          ‖complexSourceFieldMoment hm U α x‖ ≤
            C * T / (1 + m * T) * Real.exp (sourceMomentLambda b * m * T) *
              (sourceMomentBase b * T) ^ (∑ j, α j) *
                ‖(sourceReserve hm U ^ b) (complexSourceTestInclusion hm U x)‖ ∧
          ‖complexSourceMomentumMoment hm U α x‖ ≤
            C * T ^ 2 / (1 + m * T) ^ 2 * Real.exp (sourceMomentLambda b * m * T) *
              (sourceMomentBase b * T) ^ (∑ j, α j) *
                ‖(sourceReserve hm U ^ b) (complexSourceTestInclusion hm U x)‖ := by
  obtain ⟨M, hM, hbound⟩ := weightedSource_entire_growth hb hb1
  refine ⟨Real.exp 1 * M, by positivity, ?_⟩
  intro m hm T hT U hU α x
  have ha : 0 < sourceMomentLambda b * T :=
    mul_pos (sourceMomentLambda_pos hb hb1) hT
  have hR : 0 < momentCauchyRadius (sourceMomentLambda b * T) α := by
    unfold momentCauchyRadius
    positivity
  let N := ‖(sourceReserve hm U ^ b) (complexSourceTestInclusion hm U x)‖
  have hf := entire_moment_coefficient_bound ha
    (show 0 ≤ M * T / (1 + m * T) * Real.exp (sourceMomentLambda b * m * T) * N by
      dsimp [N]; positivity)
    (fun z => complexSourceFieldFourier hm U z x) (fun z => ?_) α
  · have hg := entire_moment_coefficient_bound ha
      (show 0 ≤ M * T ^ 2 / (1 + m * T) ^ 2 *
        Real.exp (sourceMomentLambda b * m * T) * N by dsimp [N]; positivity)
      (fun z => complexSourceMomentumFourier hm U z x) (fun z => ?_) α
    · rw [polydiscCoefficient_complexSourceFieldFourier hm U hR,
        spatialMomentPhase_norm_cancel] at hf
      rw [polydiscCoefficient_complexSourceMomentumFourier hm U hR,
        spatialMomentPhase_norm_cancel] at hg
      constructor
      · convert hf using 1 <;>
          simp only [complexSourceFieldMoment_apply, N, sourceMomentBase]; ring
      · convert hg using 1 <;>
          simp only [complexSourceMomentumMoment_apply, N, sourceMomentBase]; ring
    · convert (hbound m hm T hT U hU z x).2 using 1; dsimp [N]; ring
  · convert (hbound m hm T hT U hU z x).1 using 1; dsimp [N]; ring

end VacuumBellSeparation
