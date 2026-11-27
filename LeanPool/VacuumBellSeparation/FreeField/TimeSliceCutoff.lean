/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.PlanarEnergyWeight
public import Mathlib.Analysis.Calculus.Deriv.Support

/-! # An actual smooth time-slice switching function -/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology Set
open scoped ContDiff

/-- Time slice cutoff defined as `Real.smoothTransition ((t + ε) / (2 * ε))`. -/
noncomputable def timeSliceCutoff (ε t : ℝ) : ℝ :=
  Real.smoothTransition ((t + ε) / (2 * ε))

theorem contDiff_timeSliceCutoff (ε : ℝ) : ContDiff ℝ (∞ : ℕ∞ω) (timeSliceCutoff ε) :=
  Real.smoothTransition.contDiff.comp
    (((contDiff_id : ContDiff ℝ (∞ : ℕ∞ω) (fun t : ℝ => t)).add contDiff_const).div_const (2 * ε))

theorem timeSliceCutoff_zero {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ -ε) :
    timeSliceCutoff ε t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem timeSliceCutoff_one {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) :
    timeSliceCutoff ε t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ (by positivity : 0 < 2 * ε)).mpr (by linarith)

theorem deriv_timeSliceCutoff_eq_zero_of_not_mem {ε : ℝ} (hε : 0 < ε) {t : ℝ}
    (ht : t ∉ Icc (-ε) ε) : deriv (timeSliceCutoff ε) t = 0 := by
  have hout : t < -ε ∨ ε < t := by simpa only [mem_Icc, not_and_or, not_le] using ht
  rcases hout with ht | ht
  · have heq : timeSliceCutoff ε =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact timeSliceCutoff_zero hε hs.le
    rw [heq.deriv_eq]
    exact deriv_const _ _
  · have heq : timeSliceCutoff ε =ᶠ[𝓝 t] (fun _ => 1) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact timeSliceCutoff_one hε hs.le
    rw [heq.deriv_eq]
    exact deriv_const _ _

theorem tsupport_deriv_timeSliceCutoff_subset {ε : ℝ} (hε : 0 < ε) :
    tsupport (deriv (timeSliceCutoff ε)) ⊆ Icc (-ε) ε := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hout
  exact ht (deriv_timeSliceCutoff_eq_zero_of_not_mem hε hout)

theorem tsupport_deriv_twice_timeSliceCutoff_subset {ε : ℝ} (hε : 0 < ε) :
    tsupport (deriv (deriv (timeSliceCutoff ε))) ⊆ Icc (-ε) ε :=
  tsupport_deriv_subset.trans (tsupport_deriv_timeSliceCutoff_subset hε)

theorem hasCompactSupport_deriv_timeSliceCutoff {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (deriv (timeSliceCutoff ε)) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (tsupport_deriv_timeSliceCutoff_subset hε)

theorem contDiff_deriv_timeSliceCutoff (ε : ℝ) :
    ContDiff ℝ (∞ : ℕ∞ω) (deriv (timeSliceCutoff ε)) :=
  (contDiff_infty_iff_deriv.mp (contDiff_timeSliceCutoff ε)).2

theorem contDiff_deriv_twice_timeSliceCutoff (ε : ℝ) :
    ContDiff ℝ (∞ : ℕ∞ω) (deriv (deriv (timeSliceCutoff ε))) :=
  (contDiff_infty_iff_deriv.mp (contDiff_deriv_timeSliceCutoff ε)).2

end VacuumBellSeparation
