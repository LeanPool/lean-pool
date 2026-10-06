/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineIntervalWeakScalar

/-!
# Weak derivatives on affine time intervals

The weak spatial and time derivatives transport between corresponding
half-space time intervals in `lem:bu-small-time`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Weak derivatives transport through an affine parabolic change of
variables between corresponding positive half-space time intervals. -/
theorem bu_affine_weak_derivatives_interval
    (τ scale a b : ℝ) (hscale : 0 < scale)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2}
      (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b))
      w Dw D2w Dtw) :
    HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo a b)
      (buAffineField τ scale w) (buAffineDw τ scale Dw)
      (buAffineD2w τ scale D2w) (buAffineDtw τ scale Dtw) := by
  let S := spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b))
  have hwloc : LocallyIntegrableOn (buAffineField τ scale w)
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b)) volume := by
    change LocallyIntegrableOn (w ∘ buAffinePoint τ scale) _ volume
    exact bu_affine_locallyIntegrableOn_interval τ scale a b hscale w hweak.1
  have hDwloc : LocallyIntegrableOn (buAffineDw τ scale Dw)
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b)) volume := by
    change LocallyIntegrableOn
      (scale • (Dw ∘ buAffinePoint τ scale)) _ volume
    exact (bu_affine_locallyIntegrableOn_interval τ scale a b hscale Dw hweak.2.1).smul scale
  have hD2loc : LocallyIntegrableOn (buAffineD2w τ scale D2w)
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b)) volume := by
    change LocallyIntegrableOn
      (scale ^ 2 • (D2w ∘ buAffinePoint τ scale)) _ volume
    exact (bu_affine_locallyIntegrableOn_interval τ scale a b hscale D2w hweak.2.2.1).smul
      (scale ^ 2)
  have hDtloc : LocallyIntegrableOn (buAffineDtw τ scale Dtw)
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b)) volume := by
    change LocallyIntegrableOn
      (scale ^ 2 • (Dtw ∘ buAffinePoint τ scale)) _ volume
    exact (bu_affine_locallyIntegrableOn_interval τ scale a b hscale Dtw hweak.2.2.2.1).smul
      (scale ^ 2)
  have hwm_i (i : Fin 3) : AEStronglyMeasurable (fun z => w z i)
      (volume.restrict S) :=
    (continuous_apply i).comp_aestronglyMeasurable
      hweak.1.aestronglyMeasurable
  have hDwm_ij (i j : Fin 3) : AEStronglyMeasurable (fun z => Dw z i j)
      (volume.restrict S) :=
    (continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable
        hweak.2.1.aestronglyMeasurable)
  have hD2m_ijk (i j k : Fin 3) : AEStronglyMeasurable
      (fun z => D2w z i j k) (volume.restrict S) :=
    (continuous_apply k).comp_aestronglyMeasurable
      ((continuous_apply j).comp_aestronglyMeasurable
        ((continuous_apply i).comp_aestronglyMeasurable
          hweak.2.2.1.aestronglyMeasurable))
  have hDtm_i (i : Fin 3) : AEStronglyMeasurable (fun z => Dtw z i)
      (volume.restrict S) :=
    (continuous_apply i).comp_aestronglyMeasurable
      hweak.2.2.2.1.aestronglyMeasurable
  refine ⟨hwloc, hDwloc, hD2loc, hDtloc, ?_⟩
  intro ψ hψ
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have h := bu_affine_spatial_weak_identity_interval τ scale a b 1 hscale
      (fun z => w z i) (fun z => Dw z i j) j
      (hwm_i i) (hDwm_ij i j)
      (fun φ hφ => (hweak.2.2.2.2 φ hφ).1 i j) ψ hψ
    simpa only [buAffineField, buAffineDw, one_mul] using h
  · intro i j k
    have h := bu_affine_spatial_weak_identity_interval τ scale a b scale hscale
      (fun z => Dw z i j) (fun z => D2w z i j k) k
      (hDwm_ij i j) (hD2m_ijk i j k)
      (fun φ hφ => (hweak.2.2.2.2 φ hφ).2.1 i j k) ψ hψ
    simpa only [buAffineDw, buAffineD2w, pow_two, mul_assoc] using h
  · intro i
    have h := bu_affine_time_weak_identity_interval τ scale a b 1 hscale
      (fun z => w z i) (fun z => Dtw z i)
      (hwm_i i) (hDtm_i i)
      (fun φ hφ => (hweak.2.2.2.2 φ hφ).2.2 i) ψ hψ
    simpa only [buAffineField, buAffineDtw, one_mul] using h

end ESS
