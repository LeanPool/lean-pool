/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortThreeDensityAverage
public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineInterval

/-!
# Rescaling a short-time velocity average

The averaging box centered at a dyadic midpoint is the affine
preimage of the physical Gaussian averaging cylinder.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The normalized short-time averaging integral equals the physical
integral times the inverse parabolic Jacobian (`lem:bu-small-time`). -/
theorem bu_short_average_rescaling_integral
    (scale : ℝ) (hscale : 0 < scale)
    (Y : Vec3) (δ : ℝ)
    (F : ParabolicPoint → ℝ)
    (hFm : AEStronglyMeasurable F
      (volume.restrict (spaceTimeSet
        (vec3Ball (scale • Y) (scale * Real.sqrt (3 * δ / 2)))
        (Ioo (scale ^ 2 * δ / 2) (5 * scale ^ 2 * δ / 4))))) :
    (∫ z in spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
      (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4)),
      F (buAffinePoint (-scale ^ 2 / 2) scale z)
        ∂(volume : Measure ParabolicPoint)) =
      scale⁻¹ ^ 5 *
        ∫ z in spaceTimeSet
          (vec3Ball (scale • Y) (scale * Real.sqrt (3 * δ / 2)))
          (Ioo (scale ^ 2 * δ / 2) (5 * scale ^ 2 * δ / 4)),
          F z ∂(volume : Measure ParabolicPoint) := by
  let R := Real.sqrt (3 * δ / 2)
  let Ω := vec3Ball (scale • Y) (scale * R)
  let I := Ioo (scale ^ 2 * δ / 2) (5 * scale ^ 2 * δ / 4)
  let shift := -scale ^ 2 / 2
  have hΩ : MeasurableSet Ω := vec3Ball_measurable _ _
  have hI : MeasurableSet I := measurableSet_Ioo
  have hspace : rescaledSpace scale (0 : Vec3) Ω = vec3Ball Y R := by
    ext y
    change vec3EuclideanNorm ((0 : Vec3) + scale • y - scale • Y) < scale * R ↔
      vec3EuclideanNorm (y - Y) < R
    rw [zero_add, ← smul_sub, vec3EuclideanNorm_smul, abs_of_pos hscale]
    exact (mul_lt_mul_iff_of_pos_left hscale)
  have htime : rescaledTime scale shift I =
      Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4) := by
    ext s
    change shift + scale ^ 2 * s ∈
      Ioo (scale ^ 2 * δ / 2) (5 * scale ^ 2 * δ / 4) ↔
      s ∈ Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4)
    simp only [mem_Ioo]
    have hsq : 0 < scale ^ 2 := sq_pos_of_pos hscale
    constructor
    · rintro ⟨hlo, hhi⟩
      constructor
      · apply (mul_lt_mul_iff_of_pos_left hsq).mp
        dsimp [shift] at hlo
        nlinarith only [hlo]
      · apply (mul_lt_mul_iff_of_pos_left hsq).mp
        dsimp [shift] at hhi
        nlinarith only [hhi]
    · rintro ⟨hlo, hhi⟩
      constructor
      · dsimp [shift]
        nlinarith only [mul_lt_mul_of_pos_left hlo hsq]
      · dsimp [shift]
        nlinarith only [mul_lt_mul_of_pos_left hhi hsq]
  have hpoint : scalingParabolic scale
      (show ParabolicPoint from ((0 : Vec3), shift)) =
      buAffinePoint shift scale := by
    funext z
    change ((0 : Vec3) + scale • z.1, shift + scale ^ 2 * z.2) =
      (scale • z.1, shift + scale ^ 2 * z.2)
    simp
  have hchange := CKN.integral_comp_scaling_test scale hscale
    (show ParabolicPoint from ((0 : Vec3), shift))
    (Ω := Ω) (I := I) (F := F) hΩ hI hFm
  rw [hspace, htime, hpoint] at hchange
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ scale⁻¹ ^ 5), smul_eq_mul] at hchange
  simpa only [R, Ω, I, shift] using hchange

end ESS
