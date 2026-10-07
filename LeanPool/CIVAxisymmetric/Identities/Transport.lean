/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.Axisymmetric

/-!
# The convective term of an axisymmetric field in cylindrical form

On the meridional plane `{x₂ = 0}` away from the axis, the Cartesian convective term
`(u · ∇) u_i` of a smooth axisymmetric field is the cylindrical transport term of
`eq:aniso:scalar:nse`: the radial component picks up the centrifugal term `-u_θ²/r`, the
swirl picks up `u_r u_θ / r`, and the vertical component is transported by the meridional
velocity alone. The three identities are the `θ`-derivative relations of design note R4
inserted into the middle summand; they are pointwise and do not use the equation.
-/

public section

open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The convective term of the radial component on the meridional plane, off the axis:
`u_r ∂_r u_r + u_z ∂_z u_r - u_θ²/r`, the left-hand side of `eq:aniso:scalar:nse:r` without
the time derivative. -/
theorem sum_convective_zero_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    ∑ j : Fin 3, u z j * spatialPartial (fun w => u w 0) j z
      = u z 0 * spatialPartial (fun w => u w 0) 0 z
        + u z 2 * spatialPartial (fun w => u w 0) 2 z - u z 1 ^ 2 / z.1 0 := by
  rw [Fin.sum_univ_three, spatialPartial_one_zero_meridional h hu hz hplane hr]
  ring

/-- The convective term of the swirl on the meridional plane, off the axis:
`u_r ∂_r u_θ + u_z ∂_z u_θ + u_r u_θ / r`, the left-hand side of
`eq:aniso:scalar:nse:swirl` without the time derivative. -/
theorem sum_convective_one_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    ∑ j : Fin 3, u z j * spatialPartial (fun w => u w 1) j z
      = u z 0 * spatialPartial (fun w => u w 1) 0 z
        + u z 2 * spatialPartial (fun w => u w 1) 2 z + u z 0 * u z 1 / z.1 0 := by
  rw [Fin.sum_univ_three, spatialPartial_one_one_meridional h hu hz hplane hr]
  ring

/-- The convective term of the vertical component on the meridional plane, off the axis:
`u_r ∂_r u_z + u_z ∂_z u_z`, the left-hand side of `eq:aniso:scalar:nse:z` without the time
derivative. -/
theorem sum_convective_two_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    ∑ j : Fin 3, u z j * spatialPartial (fun w => u w 2) j z
      = u z 0 * spatialPartial (fun w => u w 2) 0 z
        + u z 2 * spatialPartial (fun w => u w 2) 2 z := by
  rw [Fin.sum_univ_three, spatialPartial_one_two_meridional h hu hz hplane hr]
  ring

end CIV
