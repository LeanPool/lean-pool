/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.IsClassicalSolutionOn
public import LeanPool.CIVAxisymmetric.Identities.Transport
public import LeanPool.CIVAxisymmetric.Identities.Laplacian
public import LeanPool.CIVAxisymmetric.Identities.Divergence
public import LeanPool.CIVAxisymmetric.Identities.PressureAxisymmetric

/-!
# The swirl component of the scalar Navier–Stokes equation on the meridional plane

`eq:aniso:scalar:nse:swirl` is the swirl component of the momentum equation restricted to the
meridional plane `{x₂ = 0}` off the axis.  It states that the time derivative, the cylindrical
convective term `u_r ∂_r u_θ + u_z ∂_z u_θ + u_r u_θ / r`, and the forcing balance the
cylindrical Laplacian `∂_r² u_θ + r⁻¹ ∂_r u_θ + ∂_z² u_θ - r⁻² u_θ`.

The angular derivative of the pressure drops out of the swirl component because the pressure
of a classical solution with axisymmetric velocity and axisymmetric force is itself
axisymmetric (`pressure_rotZ_invariant`). The rotation invariance of the pressure is
therefore not a hypothesis here: only the axisymmetry of the force is.
-/

public section

open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



theorem scalar_nse_swirl
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hfaxi : IsAxisymmetricOn f unitCylinder)
    (z : ParabolicPoint) (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    timePartial (fun w => u w 1) z + u z 0 * spatialPartial (fun w => u w 1) 0 z
        + u z 2 * spatialPartial (fun w => u w 1) 2 z + u z 0 / z.1 0 * u z 1 =
      spatialSecondPartial (fun w => u w 1) 0 0 z + spatialPartial (fun w => u w 1) 0 z / z.1 0
        + spatialSecondPartial (fun w => u w 1) 2 2 z - u z 1 / (z.1 0) ^ 2 + f z 1 := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hsol.1.of_le (by norm_num)
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hsol.1.of_le (by norm_num)
  have hp1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => p z) unitCylinder :=
    hsol.2.1.of_le (by norm_num)
  have hp : ∀ φ : ℝ, ∀ z ∈ unitCylinder, p (rotZ φ z.1, z.2) = p z :=
    pressure_rotZ_invariant u p f hsol haxi hfaxi
  have h_mom := hsol.2.2.2.1 z hz 1
  have h_press : spatialPartial p 1 z = 0 :=
    spatialPartial_one_meridional_of_invariant hp1 hp hz hplane hr
  have h_conv := sum_convective_one_meridional haxi hu1 hz hplane hr
  have h_lap := sum_spatialSecondPartial_one_meridional haxi hu2 hz hplane hr
  rw [h_press] at h_mom
  rw [h_conv, h_lap] at h_mom
  field_simp [hr] at h_mom ⊢
  linarith only [h_mom]

end CIV
