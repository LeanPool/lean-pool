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
# Scalar System R

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The radial component of `eq:aniso:scalar:nse`. Take the momentum equation at `i = 0` from
`hsol.2.2.2.1 z hz 0`, rewrite its convective sum with
`sum_convective_zero_meridional` and its Laplacian sum with
`sum_spatialSecondPartial_zero_meridional`, and rearrange. The centrifugal
term `-u_θ²/r` comes from the convective rewrite and the `-u_r/r²` from the Laplacian rewrite. -/
theorem scalar_nse_r
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (z : ParabolicPoint) (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    timePartial (fun w => u w 0) z + u z 0 * spatialPartial (fun w => u w 0) 0 z
        + u z 2 * spatialPartial (fun w => u w 0) 2 z - (u z 1) ^ 2 / z.1 0 =
      spatialSecondPartial (fun w => u w 0) 0 0 z + spatialPartial (fun w => u w 0) 0 z / z.1 0
        + spatialSecondPartial (fun w => u w 0) 2 2 z - u z 0 / (z.1 0) ^ 2
        - spatialPartial p 0 z + f z 0 := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hsol.1.of_le (by norm_num)
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hsol.1.of_le (by norm_num)
  have hmomentum := hsol.2.2.2.1 z hz 0
  have hconv := sum_convective_zero_meridional haxi hu1 hz hplane hr
  have hlap := sum_spatialSecondPartial_zero_meridional haxi hu2 hz hplane hr
  linarith only [hmomentum, hconv, hlap]

end CIV
