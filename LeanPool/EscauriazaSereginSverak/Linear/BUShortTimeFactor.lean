/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortErrorSupport
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus

/-!
# Separating the lower-time cutoff

The lower-time factor has no spatial derivatives. These identities isolate
its one derivative from the fixed spatial and phase factors.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The product of the spatial and normal-phase cutoff factors. -/
@[expose] def buShortSpacePhaseCutoff (scale R : ℝ) (hR : 0 < R)
    (q : Vec3 × ℝ) : ℝ :=
  ucSpatialCutoff (2 * R) (by positivity) q.1 * buShortEtaExt scale q

/-- The two-factor cutoff is smooth. -/
theorem buShortSpacePhaseCutoff_smooth
    (scale R : ℝ) (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞) (buShortSpacePhaseCutoff scale R hR) := by
  unfold buShortSpacePhaseCutoff
  exact ((ucSpatialCutoff_smooth (show 0 < 2 * R by positivity)).comp
    contDiff_fst).mul (buShortEtaExt_smooth scale)

/-- The spatial first derivative carries the lower-time factor without
differentiating it. -/
theorem buShortFullCutoff_spatialPartial_time_factor
    (scale R ε : ℝ) (hR : 0 < R)
    (z : ParabolicPoint) (j : Fin 3) :
    spatialPartial (buCutScalar (buShortFullCutoff scale R hR ε)) j z =
      spatialPartial (buCutScalar (buShortSpacePhaseCutoff scale R hR)) j z *
        buShortTimeCutoff ε z.2 := by
  rcases z with ⟨y, s⟩
  change spatialPartial
    (fun q : ParabolicPoint =>
      buShortSpacePhaseCutoff scale R hR (q.1, q.2) *
        buShortTimeCutoff ε q.2) j (y, s) = _
  exact spatialPartial_mul_time
    (buShortSpacePhaseCutoff_smooth scale R hR) j (y, s)

/-- The spatial second derivative also carries the lower-time factor
without differentiating it. -/
theorem buShortFullCutoff_spatialSecondPartial_time_factor
    (scale R ε : ℝ) (hR : 0 < R)
    (z : ParabolicPoint) (i j : Fin 3) :
    spatialSecondPartial (buCutScalar (buShortFullCutoff scale R hR ε)) i j z =
      spatialSecondPartial (buCutScalar (buShortSpacePhaseCutoff scale R hR))
        i j z * buShortTimeCutoff ε z.2 := by
  rcases z with ⟨y, s⟩
  change spatialSecondPartial
    (fun q : ParabolicPoint =>
      buShortSpacePhaseCutoff scale R hR (q.1, q.2) *
        buShortTimeCutoff ε q.2) i j (y, s) = _
  exact spatialSecondPartial_mul_time
    (buShortSpacePhaseCutoff_smooth scale R hR) i j (y, s)

/-- The only lower-time derivative appears in the time product rule. -/
theorem buShortFullCutoff_timePartial_time_factor
    (scale R ε : ℝ) (hR : 0 < R) (z : ParabolicPoint) :
    timePartial (buCutScalar (buShortFullCutoff scale R hR ε)) z =
      timePartial (buCutScalar (buShortSpacePhaseCutoff scale R hR)) z *
        buShortTimeCutoff ε z.2 +
      buShortSpacePhaseCutoff scale R hR (z.1, z.2) *
        deriv (buShortTimeCutoff ε) z.2 := by
  rcases z with ⟨y, s⟩
  change timePartial
    (fun q : ParabolicPoint =>
      buShortSpacePhaseCutoff scale R hR (q.1, q.2) *
        buShortTimeCutoff ε q.2) (y, s) = _
  exact timePartial_mul_time
    (buShortSpacePhaseCutoff_smooth scale R hR)
    (buShortTimeCutoff_smooth ε) (y, s)

end ESS
