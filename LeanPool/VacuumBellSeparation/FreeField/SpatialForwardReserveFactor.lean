/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialForwardDecay

/-!
# Mass-uniform forward factor on the actual pair source space

The same compact selfadjoint factor has both the genuine operator norm
and the full extended nuclear norm bounded by F_b/s². The constants are
independent of the mass and of the selected subregions of the unit balls.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped ENNReal

theorem exists_uniform_forward_source_factor {b : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1) :
    ∃ S F : ℝ, 0 < S ∧ 0 < F ∧
      ∀ (m : ℝ) (hm : 0 < m) (s : ℝ), S ≤ s →
        ∀ (U W : Set (EuclideanSpace ℝ (Fin 3))),
          U ⊆ Metric.ball 0 1 → W ⊆ Metric.ball (spatialAxisDisplacement s 0) 1 →
          ∃ Y : HilbertComplexification (WithLp 2 (SourceHilbert hm U × SourceHilbert hm W)) →L[ℂ]
              HilbertComplexification (WithLp 2 (SourceHilbert hm U × SourceHilbert hm W)),
            complexify (productSourceCovariancePerturbation hm U W) =
              reserve (normalizedCommutation
                (complexify (productSourceCommutation hm (UA := U) (UB := W)))) ^ b *
                Y * reserve (normalizedCommutation
                  (complexify (productSourceCommutation hm (UA := U) (UB := W)))) ^ b ∧
            IsCompactOperator Y ∧ IsSelfAdjoint Y ∧
            ‖Y‖ ≤ F / s ^ 2 ∧ operatorTraceNorm Y ≤ ENNReal.ofReal (F / s ^ 2) ∧
            operatorTraceNorm Y < ∞ := by
  obtain ⟨C, hC, hbound⟩ := exists_spatial_source_reserve_estimate hb hb1
  refine ⟨sourceForwardThreshold b, 2 * sourceForwardEnvelopeConstant C, ?_, ?_, ?_⟩
  · exact (by norm_num : (0 : ℝ) < 4).trans_le (le_max_left _ _)
  · unfold sourceForwardEnvelopeConstant
    positivity
  · intro m hm s hs U W hU hW
    have hsep : 16 * Real.sqrt 3 * (sourceMomentBase b * 1) ≤ s := by
      simpa only [mul_one] using
        (le_max_left (16 * Real.sqrt 3 * sourceMomentBase b) (2 * sourceForwardKappa b)).trans
          ((le_max_right _ _).trans hs)
    obtain ⟨Y, hfac, hc, hsa, hY, hY₁, hfin⟩ := hbound m hm 1 (by norm_num) s hsep U W hU hW
    have hd := spatialSourceFactorBound_one_le (C := C) hm hs
    have hconst : 0 ≤ sourceForwardEnvelopeConstant C / s ^ 2 := by
      unfold sourceForwardEnvelopeConstant
      positivity
    refine ⟨Y, hfac, hc, hsa, (hY.trans hd).trans ?_, hY₁.trans ?_, hfin⟩
    · calc
        _ ≤ 2 * (sourceForwardEnvelopeConstant C / s ^ 2) := by linarith
        _ = _ := by ring
    · apply ENNReal.ofReal_le_ofReal
      convert mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 2) using 1; ring

end VacuumBellSeparation
