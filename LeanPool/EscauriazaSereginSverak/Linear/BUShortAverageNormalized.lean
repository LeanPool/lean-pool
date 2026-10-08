/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortAverageExponents

/-!
# Normalizing the physical Gaussian average

After the affine change of variables, the physical average estimate
has the dyadic form used in the high-strip cell summation.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A physical Gaussian average estimate yields the corresponding
normalized dyadic average bound (`lem:bu-small-time`). -/
theorem bu_short_normalized_average_bound
    (scale β M C δ d : ℝ) (Y : Vec3)
    (hscale : 0 < scale) (hβ : 0 < β) (hC : 0 ≤ C)
    (hδ : 0 < δ) (hδd : δ ≤ d) (hd : d ≤ 1)
    (w : ParabolicPoint → Vec3)
    (hFm : AEStronglyMeasurable
      (fun z => vec3EuclideanNorm (w z) ^ 2)
      (volume.restrict (spaceTimeSet
        (vec3Ball (scale • Y) (scale * Real.sqrt (3 * δ / 2)))
        (Ioo (scale ^ 2 * δ / 2) (5 * scale ^ 2 * δ / 4)))))
    (hPhysical :
      let t := scale ^ 2 * δ / 2
      Real.rpow t (-(5 / 2 : ℝ)) *
        (∫ z in spaceTimeSet
          (vec3Ball (scale • Y) (scale * Real.sqrt (3 * δ / 2)))
          (Ioo t (5 * t / 2)),
          vec3EuclideanNorm (w z) ^ 2
            ∂(volume : Measure ParabolicPoint)) ≤
        C * Real.exp (8 * M * vec3EuclideanNorm (scale • Y) ^ 2) *
          Real.exp (-(β * (scale • Y) 2 ^ 2 / (12 * t)))) :
    let v := buAffineField (-scale ^ 2 / 2) scale w
    let G := 8 * M * scale ^ 2
    let Avg := spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
      (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4))
    (∫ z in Avg, vec3EuclideanNorm (v z) ^ 2
      ∂(volume : Measure ParabolicPoint)) ≤
        C * d ^ 2 *
        Real.exp (G * (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) *
        Real.exp (-(β * Y 2 ^ 2 / (12 * d))) := by
  dsimp
  let t := scale ^ 2 * δ / 2
  let P := ∫ z in spaceTimeSet
    (vec3Ball (scale • Y) (scale * Real.sqrt (3 * δ / 2)))
    (Ioo t (5 * t / 2)),
    vec3EuclideanNorm (w z) ^ 2 ∂(volume : Measure ParabolicPoint)
  let Q := ∫ z in spaceTimeSet (vec3Ball Y (Real.sqrt (3 * δ / 2)))
    (Ioo (1 / 2 + δ / 2) (1 / 2 + 5 * δ / 4)),
    vec3EuclideanNorm (buAffineField (-scale ^ 2 / 2) scale w z) ^ 2
      ∂(volume : Measure ParabolicPoint)
  let R := C * Real.exp (8 * M * vec3EuclideanNorm (scale • Y) ^ 2) *
    Real.exp (-(β * (scale • Y) 2 ^ 2 / (12 * t)))
  have ht : 0 < t := by dsimp [t]; positivity
  have hRpow : 0 ≤ Real.rpow t (5 / 2 : ℝ) :=
    (Real.rpow_pos_of_pos ht _).le
  have hcancel : Real.rpow t (5 / 2 : ℝ) *
      Real.rpow t (-(5 / 2 : ℝ)) = 1 := by
    have hneg : Real.rpow t (-(5 / 2 : ℝ)) =
        (Real.rpow t (5 / 2 : ℝ))⁻¹ := Real.rpow_neg ht.le _
    rw [hneg]
    exact mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos ht _))
  have hP : P ≤ Real.rpow t (5 / 2 : ℝ) * R := by
    calc
      P = (Real.rpow t (5 / 2 : ℝ) *
          Real.rpow t (-(5 / 2 : ℝ))) * P := by rw [hcancel, one_mul]
      _ = Real.rpow t (5 / 2 : ℝ) *
          (Real.rpow t (-(5 / 2 : ℝ)) * P) := by ring
      _ ≤ Real.rpow t (5 / 2 : ℝ) * R :=
        mul_le_mul_of_nonneg_left hPhysical hRpow
  have hChange : Q = scale⁻¹ ^ 5 * P := by
    have h := bu_short_average_rescaling_integral scale hscale Y δ
      (fun z => vec3EuclideanNorm (w z) ^ 2) hFm
    simpa only [Q, P, t, buAffineField,
      show 5 * (scale ^ 2 * δ / 2) / 2 =
        5 * scale ^ 2 * δ / 4 by ring] using h
  have hFactor := bu_short_average_jacobian_factor_le
    scale δ d hscale hδ hδd hd
  have hTail := bu_short_average_normal_tail_le
    scale β δ d Y hscale hβ hδ hδd
  have hNorm : vec3EuclideanNorm (scale • Y) ^ 2 =
      scale ^ 2 * (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2) := by
    rw [vec3EuclideanNorm_smul, abs_of_pos hscale,
      mul_pow, bu_short_vec3_norm_sq_coordinates]
  have hExpEq : Real.exp (8 * M * vec3EuclideanNorm (scale • Y) ^ 2) =
      Real.exp ((8 * M * scale ^ 2) *
        (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) := by
    rw [hNorm]
    congr 1
    ring
  have hscaleCoeff : 0 ≤ scale⁻¹ ^ 5 := by positivity
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hfixedCoeff : 0 ≤ d ^ 2 * C *
      Real.exp ((8 * M * scale ^ 2) *
        (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) := by positivity
  calc
    Q = scale⁻¹ ^ 5 * P := hChange
    _ ≤ scale⁻¹ ^ 5 * (Real.rpow t (5 / 2 : ℝ) * R) :=
      mul_le_mul_of_nonneg_left hP hscaleCoeff
    _ = (scale⁻¹ ^ 5 * Real.rpow t (5 / 2 : ℝ)) * R := by ring
    _ ≤ d ^ 2 * R := mul_le_mul_of_nonneg_right hFactor hR0
    _ = d ^ 2 * C *
        Real.exp ((8 * M * scale ^ 2) *
          (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) *
        Real.exp (-(β * (scale • Y) 2 ^ 2 / (12 * t))) := by
      rw [← hExpEq]
      dsimp [R]
      ring
    _ ≤ d ^ 2 * C *
        Real.exp ((8 * M * scale ^ 2) *
          (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) *
        Real.exp (-(β * Y 2 ^ 2 / (12 * d))) :=
      mul_le_mul_of_nonneg_left hTail hfixedCoeff
    _ = C * d ^ 2 *
        Real.exp ((8 * M * scale ^ 2) *
          (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2)) *
        Real.exp (-(β * Y 2 ^ 2 / (12 * d))) := by ring

end ESS
