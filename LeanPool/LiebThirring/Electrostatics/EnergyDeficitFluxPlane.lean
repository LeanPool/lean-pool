/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.PlaneDistance
public import LeanPool.LiebThirring.Electrostatics.PlanePolar
public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitHalfSpaceRadial

/-!
# Integrable boundary majorant for the exterior inverse-square flux

Exact planar radial inverse-fourth mass with its flux numerator.

Exact whole-plane integral of the positive inverse-square flux density.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring

/-- Exact planar radial inverse-fourth mass with its flux numerator. -/
theorem lintegral_planar_inverse_fourth_flux (a : ℝ) (ha : 0 < a) :
    (∫⁻ q : Planar, ENNReal.ofReal (a / (‖q‖ ^ 2 + a ^ 2) ^ 2)) =
      ENNReal.ofReal (Real.pi / a) := by
  have hf : Measurable (fun r : ℝ => ENNReal.ofReal
      (r / (a ^ 2 + r ^ 2) ^ 2)) :=
    (measurable_id.div ((measurable_const.add (measurable_id.pow_const 2)).pow_const
      2)).ennreal_ofReal
  have hg : Measurable (fun r : ℝ => ENNReal.ofReal
      (a / (r ^ 2 + a ^ 2) ^ 2)) :=
    (measurable_const.div (((measurable_id.pow_const 2).add measurable_const).pow_const
      2)).ennreal_ofReal
  rw [lintegral_planar_norm _ hg]
  have hrad : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
      ENNReal.ofReal (a / (r ^ 2 + a ^ 2) ^ 2)) =
      ENNReal.ofReal a * ENNReal.ofReal (1 / (2 * a ^ 2)) := by
    calc
      _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal a *
          ENNReal.ofReal (r / (a ^ 2 + r ^ 2) ^ 2) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
        rw [← ENNReal.ofReal_mul hr.le, ← ENNReal.ofReal_mul ha.le]
        congr 1
        rw [add_comm (r ^ 2)]
        ring
      _ = _ := by rw [lintegral_const_mul _ hf, lintegral_inverse_fourth_radial a ha]
  rw [hrad, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi * a)]
  congr 1
  field_simp

/-- Exact whole-plane integral of the positive inverse-square flux density. -/
theorem lintegral_plane_inverse_fourth_flux (n b c : Position) (hn : ‖n‖ = 1)
    (F : PlaneFrame (affinePlane n b)) (ha : 0 < planeHeight n b c) :
    (∫⁻ y, ENNReal.ofReal (planeHeight n b c / ‖y - c‖ ^ 4) ∂planeMeasure F) =
      ENNReal.ofReal (Real.pi / planeHeight n b c) := by
  have hf : Measurable (fun y : Position => ENNReal.ofReal
      (planeHeight n b c / ‖y - c‖ ^ 4)) :=
    (measurable_const.div ((measurable_id.sub measurable_const).norm.pow_const 4)).ennreal_ofReal
  rw [lintegral_planeMeasure_atFoot n b c hn F _ hf]
  have hd (q : Planar) :
      ‖(planeFrameAtFoot n b c hn F q : Position) - c‖ ^ 4 =
        (‖q‖ ^ 2 + planeHeight n b c ^ 2) ^ 2 := by
    rw [norm_sub_rev, norm_sub_planeFrameAtFoot_eq_sqrt, show 4 = 2 * 2 from rfl,
      pow_mul, Real.sq_sqrt (by positivity)]
  simp_rw [hd]
  exact lintegral_planar_inverse_fourth_flux _ ha

/-- The full-plane flux majorant is Bochner integrable. -/
theorem integrable_plane_inverse_fourth_flux (n b c : Position) (hn : ‖n‖ = 1)
    (F : PlaneFrame (affinePlane n b)) (ha : 0 < planeHeight n b c) :
    Integrable (fun y : Position => planeHeight n b c / ‖y - c‖ ^ 4) (planeMeasure F) := by
  refine ⟨(measurable_const.div ((measurable_id.sub measurable_const).norm.pow_const
    4)).aestronglyMeasurable, ?_⟩
  change (∫⁻ y, ‖planeHeight n b c / ‖y - c‖ ^ 4‖ₑ ∂planeMeasure F) < ⊤
  have hnonneg (y : Position) : 0 ≤ planeHeight n b c / ‖y - c‖ ^ 4 := by positivity
  simp_rw [Real.enorm_eq_ofReal (hnonneg _)]
  rw [lintegral_plane_inverse_fourth_flux n b c hn F ha]
  exact ENNReal.ofReal_lt_top

end LiebThirring

end
