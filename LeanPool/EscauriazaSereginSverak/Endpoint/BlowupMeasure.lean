/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupBadPoint
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average

/-!
# The open top of a past cylinder

The top time slice is null for space-time volume, so the open past cylinder
and the CKN cylinder give the same energy integral (`prop:blowup-limit`).
-/

public section


open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Opening the top face of a past cylinder preserves its volume restriction. -/
theorem blowupPastCylinder_restrict_eq
    (x : Vec3) (t r : ℝ) :
    (volume : Measure ParabolicPoint).restrict
        (goodPointPastCylinder x t r) =
      volume.restrict (parabolicCylinder x t r) := by
  apply Measure.restrict_congr_set
  rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
  change (vec3Ball x r ×ˢ Ioo (t - r ^ 2) t) =ᵐ[(volume : Measure Vec3).prod volume]
    (vec3Ball x r ×ˢ Ioc (t - r ^ 2) t)
  exact Measure.set_prod_ae_eq EventuallyEq.rfl Ioo_ae_eq_Ioc

/-- The good-point energy can be integrated over the open past cylinder. -/
theorem goodPointEnergy_eq_open_top
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (x : Vec3) (t r : ℝ) :
    goodPointEnergy u p x t r =
      ∫⁻ z in goodPointPastCylinder x t r,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) := by
  unfold goodPointEnergy
  rw [blowupPastCylinder_restrict_eq]

end ESS
