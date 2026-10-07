/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSpaceTimeMollify

/-!
# L5 Serrin

Space-time `L⁵` membership gives the finite branch of `thm:lps` at
`s = 5`, where the time exponent is also five.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Space-time `L⁵` membership gives the finite branch of `thm:lps` at
`s = 5`, where the time exponent is also five. -/
theorem lps_finite_branch_of_memLp_five
    {T : ℝ} {u : ParabolicPoint → Vec3}
    (hu : MemLp u (ENNReal.ofReal (5 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    (∫⁻ t in Ioo (0 : ℝ) T,
      (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (5 : ℝ)) ^
          (((2 * 5 / (5 - 3)) / 5 : ℝ))) < ⊤ := by
  have hexp : ((2 * 5 / (5 - 3)) / 5 : ℝ) = 1 := by norm_num
  let ν : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  rw [serrin_slab_measure_eq T] at hu
  have hsm : AEStronglyMeasurable u ν := hu.aestronglyMeasurable
  have hnormsm : AEStronglyMeasurable (fun z : ParabolicPoint =>
      vec3EuclideanNorm (u z)) ν :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hsm
  have hnormBound :
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (u z))
          (ENNReal.ofReal (5 : ℝ)) ν ≤
        ENNReal.ofReal (Real.sqrt 3) * eLpNorm u (ENNReal.ofReal (5 : ℝ)) ν := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (f := fun z : ParabolicPoint => vec3EuclideanNorm (u z)) (g := u)
      (c := Real.sqrt 3) hnormsm ?_ (ENNReal.ofReal (5 : ℝ))
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact vec3EuclideanNorm_le_sqrt_three_mul_norm (u z)
  have hnormFinite :
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (u z))
          (ENNReal.ofReal (5 : ℝ)) ν < ⊤ := by
    exact lt_of_le_of_lt hnormBound
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.eLpNorm_lt_top)
  have hpow : (ENNReal.ofReal (5 : ℝ)).toReal = 5 := by norm_num
  have hlinFinite :
      (∫⁻ z : ParabolicPoint,
        ‖vec3EuclideanNorm (u z)‖ₑ ^ (5 : ℝ) ∂ν) < ⊤ := by
    have hfinite := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := ENNReal.ofReal (5 : ℝ)) (by norm_num) ENNReal.ofReal_ne_top hnormsm).mp
        hnormFinite
    rw [hpow] at hfinite
    exact hfinite
  have hpowMeas : AEMeasurable
      (fun z : ParabolicPoint => ‖vec3EuclideanNorm (u z)‖ₑ ^ (5 : ℝ)) ν :=
    hnormsm.enorm.pow_const _
  have htonelli :
      (∫⁻ z : ParabolicPoint,
        ‖vec3EuclideanNorm (u z)‖ₑ ^ (5 : ℝ) ∂ν) =
      ∫⁻ t in Ioo (0 : ℝ) T,
        ∫⁻ x : Vec3,
          ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ (5 : ℝ) := by
    rw [← lintegral_prod_symm _ hpowMeas]
    rfl
  have hnormEq (z : ParabolicPoint) :
      ‖vec3EuclideanNorm (u z)‖ₑ =
        ENNReal.ofReal (vec3EuclideanNorm (u z)) :=
    Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)
  rw [hexp]
  simp_rw [ENNReal.rpow_one]
  have htargetEq :
      (∫⁻ t in Ioo (0 : ℝ) T,
        ∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (5 : ℝ)) =
      ∫⁻ t in Ioo (0 : ℝ) T,
        ∫⁻ x : Vec3,
          ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ (5 : ℝ) := by
    apply lintegral_congr_ae
    filter_upwards [] with t
    apply lintegral_congr
    intro x
    rw [hnormEq (x, t)]
  rw [htargetEq, ← htonelli]
  exact hlinFinite

end ESS
