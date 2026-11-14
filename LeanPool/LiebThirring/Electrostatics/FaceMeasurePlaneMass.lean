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
public import LeanPool.LiebThirring.Electrostatics.FaceMeasurePlaneMassRadial

/-!
# Whole-plane mass of the face-charge density

At positive height, the whole-plane face-charge density has mass exactly `Z`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring

/-- Exact mass of the radial form of the planar face-charge density. -/
theorem lintegral_planar_faceDensity_mass (a Z : ℝ) (ha : 0 < a) (hZ : 0 ≤ Z) :
    (∫⁻ q : Planar, ENNReal.ofReal
      (Z * a / (2 * Real.pi * (Real.sqrt (‖q‖ ^ 2 + a ^ 2)) ^ 3))) =
      ENNReal.ofReal Z := by
  have hs : Measurable (fun r : ℝ => Real.sqrt (r ^ 2 + a ^ 2)) :=
    Real.continuous_sqrt.measurable.comp ((measurable_id.pow_const 2).add measurable_const)
  have hg : Measurable (fun r : ℝ => ENNReal.ofReal
      (Z * a / (2 * Real.pi * (Real.sqrt (r ^ 2 + a ^ 2)) ^ 3))) :=
    (measurable_const.div (measurable_const.mul (hs.pow_const 3))).ennreal_ofReal
  have hf : Measurable (fun r : ℝ => ENNReal.ofReal
      (r / (Real.sqrt (r ^ 2 + a ^ 2)) ^ 3)) :=
    (measurable_id.div (hs.pow_const 3)).ennreal_ofReal
  have hπ : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hC : 0 ≤ Z * a / (2 * Real.pi) := div_nonneg (mul_nonneg hZ ha.le) hπ.le
  rw [lintegral_planar_norm _ hg]
  have hrad : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * ENNReal.ofReal
      (Z * a / (2 * Real.pi * (Real.sqrt (r ^ 2 + a ^ 2)) ^ 3))) =
      ENNReal.ofReal (Z * a / (2 * Real.pi)) * ENNReal.ofReal a⁻¹ := by
    calc
      _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Z * a / (2 * Real.pi)) *
          ENNReal.ofReal (r / (Real.sqrt (r ^ 2 + a ^ 2)) ^ 3) := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
        rw [← ENNReal.ofReal_mul hr.le, ← ENNReal.ofReal_mul hC]
        congr 1
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by rw [lintegral_const_mul _ hf, lintegral_faceDensity_radial a ha]
  rw [hrad, ← mul_assoc, ← ENNReal.ofReal_mul hπ.le,
    ← ENNReal.ofReal_mul (mul_nonneg hπ.le hC)]
  congr 1
  field_simp

/-- The whole-plane face charge face-charge density has mass exactly `Z`. -/
theorem lintegral_plane_faceDensity_mass (n b c : Position) (hn : ‖n‖ = 1)
    (F : PlaneFrame (affinePlane n b)) (Z : ℝ) (hZ : 0 ≤ Z)
    (ha : 0 < planeHeight n b c) :
    (∫⁻ y, ENNReal.ofReal
      (Z * planeHeight n b c / (2 * Real.pi * ‖y - c‖ ^ 3)) ∂planeMeasure F) =
      ENNReal.ofReal Z := by
  have hf : Measurable (fun y : Position => ENNReal.ofReal
      (Z * planeHeight n b c / (2 * Real.pi * ‖y - c‖ ^ 3))) :=
    (measurable_const.div (measurable_const.mul
      ((measurable_id.sub measurable_const).norm.pow_const 3))).ennreal_ofReal
  rw [lintegral_planeMeasure_atFoot n b c hn F _ hf]
  have hd (q : Planar) :
      ‖(planeFrameAtFoot n b c hn F q : Position) - c‖ =
        Real.sqrt (‖q‖ ^ 2 + planeHeight n b c ^ 2) := by
    rw [norm_sub_rev, norm_sub_planeFrameAtFoot_eq_sqrt]
  simp_rw [hd]
  exact lintegral_planar_faceDensity_mass (planeHeight n b c) Z ha hZ

end LiebThirring

end
