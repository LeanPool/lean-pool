/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.FaceMeasureBounds

/-!
# Cubic decay of the actual Voronoi face densities

Explicit cubic decay estimates for the Voronoi face densities.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace LiebThirring

variable {M : ℕ}

/-- The explicit coefficient of the cubic decay bound in face charge. -/
noncomputable def nuclearFaceDecayCoefficient (R : Fin M → Position) (Z : ℝ)
    (k l : Fin M) : ℝ :=
  (Z * nuclearHalfDistance R k l / (2 * Real.pi)) *
    (1 + (1 + ‖R k‖) / nuclearHalfDistance R k l) ^ 3

theorem nuclearFaceDecayCoefficient_nonneg (R : Fin M → Position) {Z : ℝ}
    (hZ : 0 ≤ Z) (k l : Fin M) : 0 ≤ nuclearFaceDecayCoefficient R Z k l := by
  unfold nuclearFaceDecayCoefficient nuclearHalfDistance
  positivity

/-- The lower separation on a bisector converts inverse cubic nuclear distance
into inverse cubic distance from the origin. -/
theorem nuclearFaceDensity_le_decay (R : Fin M → Position) (hR : Function.Injective R)
    {Z : ℝ} (hZ : 0 ≤ Z) {k l : Fin M} (hkl : k ≠ l) {y : Position}
    (hy : y ∈ bisectorPlane R k l) :
    nuclearFaceDensity R Z k l y ≤ nuclearFaceDecayCoefficient R Z k l / (1 + ‖y‖) ^ 3 := by
  let a := nuclearHalfDistance R k l
  let D := 1 + (1 + ‖R k‖) / a
  let c := Z * a / (2 * Real.pi)
  have ha : 0 < a := nuclearHalfDistance_pos R hR hkl
  have hr : a ≤ ‖y - R k‖ := nuclearHalfDistance_le_norm_on_bisector R hR hkl hy
  have hrp : 0 < ‖y - R k‖ := ha.trans_le hr
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hnorm : ‖y‖ ≤ ‖y - R k‖ + ‖R k‖ := by
    simpa only [sub_add_cancel] using norm_add_le (y - R k) (R k)
  have hratio : 1 + ‖R k‖ ≤ (1 + ‖R k‖) / a * ‖y - R k‖ := by
    calc
      _ = ((1 + ‖R k‖) / a) * a := (div_mul_cancel₀ _ ha.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
  have hd : 1 + ‖y‖ ≤ D * ‖y - R k‖ := by
    dsimp [D]
    nlinarith only [hnorm, hratio]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖y‖) hd 3
  rw [mul_pow] at hp
  have hmul := mul_le_mul_of_nonneg_left hp hc
  have he : nuclearFaceDensity R Z k l y = c / ‖y - R k‖ ^ 3 := by
    dsimp [nuclearFaceDensity, c, a]
    rw [div_div]
  rw [he]
  change c / ‖y - R k‖ ^ 3 ≤ c * D ^ 3 / (1 + ‖y‖) ^ 3
  apply (div_le_div_iff₀ (pow_pos hrp 3) (by positivity)).mpr
  simpa only [mul_assoc] using hmul

/-- The genuine-face indicator preserves the cubic decay bound everywhere. -/
theorem voronoiFaceDensity_le_decay (R : Fin M → Position) (hR : Function.Injective R)
    {Z : ℝ} (hZ : 0 ≤ Z) (k l : Fin M) (hkl : k ≠ l) (y : Position) :
    voronoiFaceDensity R Z k l y ≤
      ENNReal.ofReal (nuclearFaceDecayCoefficient R Z k l / (1 + ‖y‖) ^ 3) := by
  by_cases hy : y ∈ voronoiFace R k l
  · rw [voronoiFaceDensity, indicator_of_mem hy]
    exact ENNReal.ofReal_le_ofReal (nuclearFaceDensity_le_decay R hR hZ hkl hy.2.1)
  · simp only [voronoiFaceDensity, indicator_of_notMem hy, zero_le]

end LiebThirring

end
