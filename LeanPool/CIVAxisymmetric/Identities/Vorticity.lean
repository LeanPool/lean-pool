/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.Axisymmetric
public import LeanPool.CIVAxisymmetric.Statements.Circulation

/-!
# The vorticity and the circulation of an axisymmetric field

The Cartesian curl `curlComp u i` of a field is written with CKN's classical spatial
partial derivatives. For a smooth axisymmetric field, on the meridional plane `{x₂ = 0}`
away from the axis, its components are the cylindrical ones of `eq:aniso:vorticity`,
`ω_r = -∂_z u_θ`, `ω_θ = ∂_z u_r - ∂_r u_z`, `ω_z = ∂_r u_θ + u_θ/r`; the middle one is
the definition itself, the outer two use the `θ`-derivative relations of design note R4.
The circulation `Γ = r u_θ` of `eq:aniso:vorticity` is `x₁ u₂` on that plane.
-/

public section

open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The `i`-th Cartesian component of the curl, `(∇ × u)_i = ∂_{i+1} u_{i+2} - ∂_{i+2} u_{i+1}`
with the indices read cyclically. -/
@[expose] def curlComp (u : ParabolicPoint → Vec3) (i : Fin 3) (z : ParabolicPoint) : ℝ :=
  spatialPartial (fun w => u w (i + 2)) (i + 1) z
    - spatialPartial (fun w => u w (i + 1)) (i + 2) z

/-- The first Cartesian component of the curl is `∂₂u₃ - ∂₃u₂`. -/
theorem curlComp_zero (u : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    curlComp u 0 z
      = spatialPartial (fun w => u w 2) 1 z - spatialPartial (fun w => u w 1) 2 z := rfl

/-- The second Cartesian component of the curl is `∂₃u₁ - ∂₁u₃`; on the meridional plane this
is the azimuthal vorticity `ω_θ = ∂_z u_r - ∂_r u_z` of `eq:aniso:vorticity`. -/
theorem curlComp_one (u : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    curlComp u 1 z
      = spatialPartial (fun w => u w 0) 2 z - spatialPartial (fun w => u w 2) 0 z := rfl

/-- The third Cartesian component of the curl is `∂₁u₂ - ∂₂u₁`. -/
theorem curlComp_two (u : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    curlComp u 2 z
      = spatialPartial (fun w => u w 1) 0 z - spatialPartial (fun w => u w 0) 1 z := rfl

/-- On the meridional plane, off the axis, the first component of the curl of a smooth
axisymmetric field is the radial vorticity `ω_r = -∂_z u_θ` of `eq:aniso:vorticity`. -/
theorem curlComp_zero_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    curlComp u 0 z = -spatialPartial (fun w => u w 1) 2 z := by
  rw [curlComp_zero, spatialPartial_one_two_meridional h hu hz hplane hr, zero_sub]

/-- On the meridional plane, off the axis, the third component of the curl of a smooth
axisymmetric field is the vertical vorticity `ω_z = ∂_r u_θ + u_θ/r` of
`eq:aniso:vorticity`. -/
theorem curlComp_two_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    curlComp u 2 z = spatialPartial (fun w => u w 1) 0 z + u z 1 / z.1 0 := by
  rw [curlComp_two, spatialPartial_one_zero_meridional h hu hz hplane hr]
  ring

/-- On the meridional plane the circulation `Γ = r u_θ` of `eq:aniso:vorticity` is `x₁ u₂`. -/
theorem circulation_meridional (u : ParabolicPoint → Vec3) {z : ParabolicPoint}
    (hplane : z.1 1 = 0) : circulation u z = z.1 0 * u z 1 := by
  rw [circulation, hplane, zero_mul, sub_zero]

end CIV
