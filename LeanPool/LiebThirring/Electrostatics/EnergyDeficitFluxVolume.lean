/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.SphereRadial
public import LeanPool.LiebThirring.Electrostatics.EnergyDeficitHalfSpaceRadial
public import LeanPool.LiebThirring.Electrostatics.VoronoiDistance

/-!
# The volume majorant for the exterior cutoff limit

Exact radial mass outside the closed positive-radius threshold.

Translation-invariant exact inverse-fourth mass outside a positive-radius ball.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LiebThirring

/-- Exact radial mass outside the closed positive-radius threshold. -/
theorem lintegral_inverse_fourth_outside_origin_ball (a : ℝ) (ha : 0 < a) :
    (∫⁻ x : Position, if a ≤ ‖x‖ then ENNReal.ofReal (1 / ‖x‖ ^ 4) else 0) =
      ENNReal.ofReal (4 * Real.pi / a) := by
  have hf : Measurable (fun r : ℝ => ENNReal.ofReal (1 / r ^ 4)) :=
    (measurable_const.div (measurable_id.pow_const 4)).ennreal_ofReal
  rw [lintegral_norm _ (Measurable.ite measurableSet_Ici hf measurable_const)]
  have hrad : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) *
      (if a ≤ r then ENNReal.ofReal (1 / r ^ 4) else 0)) =
      ENNReal.ofReal (Real.pi / a) / ENNReal.ofReal Real.pi := by
    have hπ : ENNReal.ofReal Real.pi ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr Real.pi_pos)
    apply (ENNReal.eq_div_iff hπ ENNReal.ofReal_ne_top).mpr
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc
      _ = ∫⁻ r in Ioi (0 : ℝ), (Ici a).indicator
          (fun r : ℝ => ENNReal.ofReal (Real.pi / r ^ 2)) r := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
        by_cases har : a ≤ r
        · rw [ite_eq_left har, indicator_of_mem (show r ∈ Ici a from har), ← ENNReal.ofReal_mul
          (sq_nonneg r),
            ← ENNReal.ofReal_mul Real.pi_pos.le]
          congr 1
          field_simp
        · rw [ite_eq_right har, indicator_of_notMem (show r ∉ Ici a from har), mul_zero, mul_zero]
      _ = ∫⁻ r in Ici a, ENNReal.ofReal (Real.pi / r ^ 2) := by
        rw [setLIntegral_indicator measurableSet_Ici,
          inter_eq_left.mpr (show Ici a ⊆ Ioi (0 : ℝ) from fun r hr => ha.trans_le hr)]
      _ = _ := lintegral_inverse_square_height a ha
  rw [hrad, ← ENNReal.ofReal_div_of_pos Real.pi_pos,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi)]
  congr 1
  field_simp

/-- Translation-invariant exact inverse-fourth mass outside a positive-radius ball. -/
theorem lintegral_inverse_fourth_outside_ball (c : Position) (a : ℝ) (ha : 0 < a) :
    (∫⁻ x in (ball c a)ᶜ, ENNReal.ofReal (1 / ‖x - c‖ ^ 4)) =
      ENNReal.ofReal (4 * Real.pi / a) := by
  rw [← lintegral_indicator (measurableSet_ball.compl)]
  have heq (x : Position) : ((ball c a)ᶜ).indicator
      (fun x : Position => ENNReal.ofReal (1 / ‖x - c‖ ^ 4)) x =
      (fun z : Position => if a ≤ ‖z‖ then ENNReal.ofReal (1 / ‖z‖ ^ 4) else 0) (x - c) := by
    simp only [indicator, mem_compl_iff, mem_ball, dist_eq_norm, not_lt]
  simp_rw [heq]
  rw [lintegral_sub_right_eq_self (fun z : Position => if a ≤ ‖z‖ then ENNReal.ofReal (1 / ‖z‖ ^ 4)
    else 0) c]
  exact lintegral_inverse_fourth_outside_origin_ball a ha

/-- Integrability of the inverse-fourth kernel outside a positive-radius ball. -/
theorem integrableOn_inverse_fourth_outside_ball (c : Position) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : Position => 1 / ‖x - c‖ ^ 4) (ball c a)ᶜ := by
  refine ⟨(measurable_const.div ((measurable_id.sub measurable_const).norm.pow_const
    4)).aestronglyMeasurable, ?_⟩
  change (∫⁻ x in (ball c a)ᶜ, ‖1 / ‖x - c‖ ^ 4‖ₑ) < ⊤
  have hn (x : Position) : 0 ≤ 1 / ‖x - c‖ ^ 4 := by positivity
  simp_rw [Real.enorm_eq_ofReal (hn _)]
  rw [lintegral_inverse_fourth_outside_ball c a ha]
  exact ENNReal.ofReal_lt_top

/-- Any ball contained in a Voronoi cell gives the exterior volume majorant. -/
theorem integrableOn_inverse_fourth_exterior_of_ball_subset {M : ℕ}
    (R : Fin M → Position) (k : Fin M) (a : ℝ) (ha : 0 < a)
    (hball : ball (R k) a ⊆ voronoiCell R k) :
    IntegrableOn (fun x : Position => 1 / ‖x - R k‖ ^ 4) (voronoiCell R k)ᶜ :=
  (integrableOn_inverse_fourth_outside_ball (R k) a ha).mono_set (compl_subset_compl.mpr hball)

end LiebThirring

end
