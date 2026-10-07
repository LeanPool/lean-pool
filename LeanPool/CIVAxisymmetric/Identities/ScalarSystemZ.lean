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

/-!
# The vertical component of the momentum equation on the meridional plane

The axial component of `eq:aniso:scalar:nse`. Take the momentum equation at `i = 2` from
`hsol.2.2.2.1`, rewrite the convective sum with
`sum_convective_two_meridional` and the Laplacian sum with
`sum_spatialSecondPartial_two_meridional`, and rearrange. This is the simplest of the
three: no centrifugal term and no `1/r²` term.
-/

public section

open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



theorem scalar_nse_z
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (z : ParabolicPoint) (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    timePartial (fun w => u w 2) z + u z 0 * spatialPartial (fun w => u w 2) 0 z
        + u z 2 * spatialPartial (fun w => u w 2) 2 z =
      spatialSecondPartial (fun w => u w 2) 0 0 z + spatialPartial (fun w => u w 2) 0 z / z.1 0
        + spatialSecondPartial (fun w => u w 2) 2 2 z - spatialPartial p 2 z + f z 2 := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hsol.1.of_le (by norm_num)
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hsol.1.of_le (by norm_num)
  have hmomentum := hsol.2.2.2.1 z hz 2
  have hconv := sum_convective_two_meridional haxi hu1 hz hplane hr
  have hlap := sum_spatialSecondPartial_two_meridional haxi hu2 hz hplane hr
  rw [hconv, hlap] at hmomentum
  linarith only [hmomentum]

end CIV
