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
# Scalar System Div

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- On the meridional plane, off the axis, the divergence equation `eq:aniso:scalar:nse:div`
holds for a classical solution: `∂_r u_r + u_r/r + ∂_z u_z = 0`. -/
theorem scalar_nse_div
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (z : ParabolicPoint) (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    spatialPartial (fun w => u w 0) 0 z + u z 0 / z.1 0 + spatialPartial (fun w => u w 2) 2 z =
      0 := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hsol.1.of_le (by exact_mod_cast le_top)
  have hsum := hsol.2.2.2.2 z hz
  rw [sum_spatialPartial_meridional haxi hu1 hz hplane hr] at hsum
  linarith only [hsum]

end CIV
