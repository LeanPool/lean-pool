/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortSmoothExt
public import LeanPool.EscauriazaSereginSverak.Linear.UCSpatialCutoff

/-!
# Compact cutoffs for the short-time Carleman estimate

A ball cutoff, the normal-phase cutoff, and a lower-time cutoff are
multiplied before applying the weak half-space estimate.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The lower-time cutoff, starting at time one half plus `ε`. -/
@[expose] def buShortTimeCutoff (ε s : ℝ) : ℝ :=
  ucInitialTimeCutoff ε (s - 1 / 2)

/-- The full scalar cutoff on product coordinates. -/
@[expose] def buShortFullCutoff (scale R : ℝ) (hR : 0 < R) (ε : ℝ)
    (q : Vec3 × ℝ) : ℝ :=
  ucSpatialCutoff (2 * R) (by positivity) q.1 *
    buShortEtaExt scale q * buShortTimeCutoff ε q.2

/-- The lower-time cutoff is smooth for every fixed `ε`. -/
theorem buShortTimeCutoff_smooth (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (buShortTimeCutoff ε) := by
  unfold buShortTimeCutoff
  exact (ucInitialTimeCutoff_smooth ε).comp
    (contDiff_id.sub contDiff_const)

/-- The full scalar cutoff is globally smooth. -/
theorem buShortFullCutoff_smooth
    (scale R : ℝ) (hR : 0 < R) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (buShortFullCutoff scale R hR ε) := by
  have hspatial : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => ucSpatialCutoff (2 * R) (by positivity) q.1) :=
    (ucSpatialCutoff_smooth (show 0 < 2 * R by positivity)).comp contDiff_fst
  have htime : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => buShortTimeCutoff ε q.2) :=
    (buShortTimeCutoff_smooth ε).comp contDiff_snd
  exact (hspatial.mul (buShortEtaExt_smooth scale)).mul htime

end ESS
