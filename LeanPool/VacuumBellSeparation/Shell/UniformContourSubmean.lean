/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.UniformHolomorphicShellSubmean
public import LeanPool.VacuumBellSeparation.Shell.ActualContourShellMeasure

/-!
# Actual uniform contour submean on the normalized target

The genuine shell pushforward dominates the induced volume on one open
neighborhood. Combined with the derived uniform chart submean, this
removes every local chart and measure-domination hypothesis.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

theorem normalizedTarget_uniform_contour_submean {θ : ℝ} (hθ : 0 < Real.sin θ) :
    ∃ N : ℕ, 0 < N ∧ ∃ D : Fin N → ControlledContourPatch θ,
      IsProbabilityMeasure (contourMixtureProbability D) ∧
      ∃ C : ℝ≥0∞, 0 < C ∧ C < ∞ ∧
        ∀ t z, (t, z) ∈ normalizedTarget →
          ∀ F : ComplexSpacetime → ℂ, Differentiable ℂ F →
            ENNReal.ofReal (‖F z‖ ^ 2) ≤ C *
              ∫⁻ y, contourMixtureCutoffWeight t D
                (fun w => ENNReal.ofReal (‖F w‖ ^ 2)) y
                ∂(contourMixtureProbability D).prod (oneParticleMeasure t) := by
  obtain ⟨N, hN, D, hp, hV, hcover, k, hk, hkt, hdom⟩ :=
    normalizedTarget_uniform_contour_domination hθ
  obtain ⟨C, hC, hCt, hsub⟩ := normalizedTarget_uniform_holomorphic_submean hV hcover
  refine ⟨N, hN, D, hp, C * k⁻¹,
    bot_lt_iff_ne_bot.mpr (mul_ne_zero hC.ne' (ENNReal.inv_pos.mpr hkt.ne).ne'),
    lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hCt.ne (ENNReal.inv_lt_top.mpr hk).ne), ?_⟩
  intro t z hz F hF
  have hmeas : Measurable (fun w : ComplexSpacetime => ENNReal.ofReal (‖F w‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hF.continuous.norm.pow 2).measurable
  have hi := lintegral_mono' (hdom t)
    (f := fun w : complexShell t => ENNReal.ofReal (‖F w.1‖ ^ 2)) le_rfl
  rw [lintegral_smul_measure, contourMixtureShellMeasure_lintegral t D hmeas] at hi
  calc
    _ ≤ C * ∫⁻ w in {w : complexShell t | (t, w.1) ∈ contourMixtureNeighborhood D},
        ENNReal.ofReal (‖F w.1‖ ^ 2) ∂inducedRegularShellVolume t := hsub t z hz F hF
    _ = (C * k⁻¹) * (k * ∫⁻ w in
        {w : complexShell t | (t, w.1) ∈ contourMixtureNeighborhood D},
          ENNReal.ofReal (‖F w.1‖ ^ 2) ∂inducedRegularShellVolume t) := by
      rw [mul_assoc, ENNReal.inv_mul_cancel_left hk.ne' hkt.ne]
    _ ≤ _ := _root_.mul_le_mul_right hi _

end VacuumBellSeparation
