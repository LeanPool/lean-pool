/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WeightedSourceWaveExtension

/-!
# Actual symmetric-reserve wave bounds

The two genuine modular estimates are combined by the already proved
bounded complementary-Gram partition. Both exponents have the same
sine, so the actual reserve estimate has the manuscript rate exactly.
No spectral projection or unbounded whole-space inverse is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian

/-- Source evaluation rate defined as `2048 / Real.sin (Real.pi * b)`. -/
noncomputable def sourceEvaluationRate (b : ℝ) : ℝ := 2048 / Real.sin (Real.pi * b)
/-- Source moment lambda defined as `2 ^ 15 / Real.sin (Real.pi * b)`. -/
noncomputable def sourceMomentLambda (b : ℝ) : ℝ := 2 ^ 15 / Real.sin (Real.pi * b)
/-- Source moment base given by `5 * sourceMomentLambda b`. -/
noncomputable def sourceMomentBase (b : ℝ) : ℝ := 5 * sourceMomentLambda b

theorem sourceMomentLambda_eq (b : ℝ) : sourceMomentLambda b = 16 * sourceEvaluationRate b := by
  unfold sourceMomentLambda sourceEvaluationRate
  norm_num
  ring

theorem sourceEvaluationRate_pos {b : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1) :
    0 < sourceEvaluationRate b := by
  apply div_pos (by norm_num)
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos Real.pi_pos (by linarith)
  · nlinarith [Real.pi_pos]

theorem sourceEvaluationRate_left (b : ℝ) :
    2048 / Real.sin (2 * Real.pi * ((1 - b) / 2)) = sourceEvaluationRate b := by
  rw [show 2 * Real.pi * ((1 - b) / 2) = Real.pi - Real.pi * b by ring, Real.sin_pi_sub]
  rfl

theorem sourceEvaluationRate_right (b : ℝ) :
    2048 / Real.sin (2 * Real.pi * (b / 2)) = sourceEvaluationRate b := by
  rw [show 2 * Real.pi * (b / 2) = Real.pi * b by ring]
  rfl

theorem weightedSource_reserveWave_bound {b : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℝ) (hm : 0 < m) (T : ℝ) (_ : 0 < T)
        (U : Set (EuclideanSpace ℝ (Fin 3))), U ⊆ Metric.ball 0 T →
        ∀ E : ℝ, m ≤ E → ∀ z : ComplexSpacetime,
          z ∈ complexShell m → euclidSq z ≤ (2 * E) ^ 2 →
          (∀ x : ComplexSourceTestSpace hm U,
            completedSourceWave hm U z (complexSourceTestInclusion hm U x) =
              complexSourceTestWave hm U z x) ∧
          ∀ x : ComplexSourceHilbert hm U, ‖completedSourceWave hm U z x‖ ≤
            (C / E * Real.exp (sourceEvaluationRate b * T * E)) *
              ‖(sourceReserve hm U ^ b) x‖ := by
  obtain ⟨C₁, hC₁, h₁⟩ := weightedSource_completedShell_evaluation
    (show 0 < (1 - b) / 2 by linarith) (show (1 - b) / 2 < 1 / 2 by linarith)
  obtain ⟨C₂, hC₂, h₂⟩ := weightedSource_completedShell_evaluation
    (show 0 < b / 2 by linarith) (show b / 2 < 1 / 2 by linarith)
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro m hm T hT U hU E hmE z hz hsize
  have hE : 0 < E := hm.trans_le hmE
  obtain ⟨heq, hbound₁⟩ := h₁ m hm T hT U hU E hmE z hz hsize
  obtain ⟨_, hbound₂⟩ := h₂ m hm T hT U hU E hmE z hz hsize
  rw [sourceEvaluationRate_left] at hbound₁
  rw [sourceEvaluationRate_right] at hbound₂
  refine ⟨heq, ?_⟩
  have h := sourceReserve_bound_of_two_modular_weights hm U
    (completedSourceWave hm U z).toLinearMap hb hb1.le
    (by positivity) (by positivity) hbound₁ hbound₂
  intro x
  convert h x using 1; ring

end VacuumBellSeparation
