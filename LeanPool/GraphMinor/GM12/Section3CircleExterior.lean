/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3HalfPlaneCharts
public import LeanPool.GraphMinor.GM12.Section3CircleCoordinates
import LeanPool.GraphMinor.Surface.Gluing

/-!
# Surface charts on the outside of a circle

For the boundary charts in XII (3.1), page 245, circle coordinates
identify a neighbourhood outside a deleted disc with the outside of
the unit circle. The semicircle coordinate change sends that set to
a half-plane. Rotation gives the same chart at every unit-circle point.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- The outside of the unit circle has a half-plane chart wherever
the point is on the right side and its imaginary coordinate is small. -/
theorem isManifoldPoint_circleExterior_right
    {z : {w : ℂ // 1 ≤ ‖w‖}} (hzre : 0 < z.val.re) (hzim : |z.val.im| < 1) :
    IsManifoldPoint z := by
  let Y : Set ℂ := {w | 1 ≤ ‖w‖}
  let M : Set ℂ := {w | 0 < w.re ∧ |w.im| < 1}
  let U : Set Y := (Subtype.val : Y → ℂ) ⁻¹' M
  have hM : IsOpen M := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_im.abs continuous_const)
  have hU : IsOpen U := hM.preimage continuous_subtype_val
  have hzU : z ∈ U := ⟨hzre, hzim⟩
  let E : U ≃ₜ (M ∩ Y : Set ℂ) := {
    toFun := fun w => ⟨w.val.val, ⟨w.property, w.val.property⟩⟩
    invFun := fun w => ⟨⟨w.val, w.property.2⟩, w.property.1⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val }
  have himage : circleBoundaryShear '' (M ∩ Y) = (circleBoundaryShear '' M) ∩ halfPlane := by
    ext w
    constructor
    · rintro ⟨v, ⟨hvM, hvY⟩, rfl⟩
      exact ⟨⟨v, hvM, rfl⟩, (circleBoundaryShear_outside_iff hvM.1 hvM.2).mp hvY⟩
    · rintro ⟨⟨v, hvM, rfl⟩, hvhalf⟩
      exact ⟨v, ⟨hvM, (circleBoundaryShear_outside_iff hvM.1 hvM.2).mpr hvhalf⟩, rfl⟩
  let e := E.trans ((circleBoundaryShear.image (M ∩ Y)).trans (Homeomorph.setCongr himage))
  exact isManifoldPoint_of_complex_halfPlane_chart hU hzU
    (circleBoundaryShear.isOpenMap _ hM) e

/-- Every point of the unit circle has a surface chart on its exterior.
This is the local model for a cuff of Sigma-star in XII (3.1), page 245. -/
theorem isManifoldPoint_circleExterior_boundary
    {z : {w : ℂ // 1 ≤ ‖w‖}} (hz : ‖z.val‖ = 1) : IsManifoldPoint z := by
  have hz0 : z.val ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at hz
    exact zero_ne_one hz
  let ρ := z.val⁻¹
  have hρ0 : ρ ≠ 0 := inv_ne_zero hz0
  have hρ : ‖ρ‖ = 1 := by rw [norm_inv, hz, inv_one]
  have hρinv : ‖ρ⁻¹‖ = 1 := by rw [norm_inv, hρ, inv_one]
  let R : {w : ℂ // 1 ≤ ‖w‖} ≃ₜ {w : ℂ // 1 ≤ ‖w‖} := {
    toFun := fun w => ⟨ρ * w.val, by simpa only [norm_mul, hρ, one_mul] using w.property⟩
    invFun := fun w => ⟨ρ⁻¹ * w.val, by simpa only [norm_mul, hρinv, one_mul] using w.property⟩
    left_inv w := Subtype.ext (by simp only [← mul_assoc, inv_mul_cancel₀ hρ0, one_mul])
    right_inv w := Subtype.ext (by simp only [← mul_assoc, mul_inv_cancel₀ hρ0, one_mul])
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_const.mul continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact continuous_const.mul continuous_subtype_val }
  have hRz : (R z).val = 1 := inv_mul_cancel₀ hz0
  have hm : IsManifoldPoint (R z) := isManifoldPoint_circleExterior_right
    (by rw [hRz]; norm_num) (by rw [hRz]; norm_num)
  exact (isManifoldPoint_iff_of_isOpenEmbedding R.isOpenEmbedding).mp hm

end GraphMinor.GM12
