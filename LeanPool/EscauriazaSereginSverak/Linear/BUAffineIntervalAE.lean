/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineIntervalDerivativeL2
public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineAE

/-!
# Almost everywhere data on affine time intervals

The heat inequality pulls back from the physical initial interval to the
shifted interval in `lem:bu-small-time`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Almost everywhere statements pull back along a positive affine
parabolic change of variables between corresponding time intervals. -/
theorem bu_affine_ae_pullback_interval
    (τ scale a b : ℝ) (hscale : 0 < scale)
    (P : ParabolicPoint → Prop)
    (hP : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)))), P z) :
    ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b))),
      P (buAffinePoint τ scale z) := by
  have hΩ : MeasurableSet {x : Vec3 | 0 < x 2} :=
    (isOpen_lt continuous_const (continuous_apply 2)).measurableSet
  have hmap := CKN.map_scalingParabolic_restrict hscale
    ((0 : Vec3), τ) hΩ (measurableSet_Ioo : MeasurableSet (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)))
  rw [rescaledSpaceTimeSet_eq_preimage scale
      (show ParabolicPoint from ((0 : Vec3), τ))
      {x : Vec3 | 0 < x 2} (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)),
    ← buAffinePoint_eq_scalingParabolic,
    buAffinePoint_preimage_interval τ scale a b hscale] at hmap
  have hPmap : ∀ᵐ z ∂(Measure.map (buAffinePoint τ scale)
      (volume.restrict (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b)))), P z := by
    rw [hmap]
    exact Measure.ae_smul_measure hP (ENNReal.ofReal (scale⁻¹ ^ 5))
  exact ae_of_ae_map (buAffinePoint_continuous τ scale).measurable.aemeasurable hPmap

end ESS
