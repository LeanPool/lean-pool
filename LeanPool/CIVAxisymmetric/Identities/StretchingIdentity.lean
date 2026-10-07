/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.Vorticity
public import LeanPool.CIVAxisymmetric.Identities.Divergence

/-!
# Stretching Identity

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The vortex-stretching term `eq:aniso:closure:stretch` evaluated on the meridional plane.
When an axisymmetric field is smooth and the point is off the axis, the sum `∑_i ∑_j ω_j ∂_j u_i
ω_i`
collapses to the algebraic expression on the right-hand side. The proof expands both `Fin 3` sums,
replaces the three `∂_1` derivatives by their `θ`-relation values, and clears denominators. -/
theorem stretching_meridional {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        curlComp u j z * spatialPartial (fun w => u w i) j z * curlComp u i z =
      spatialPartial (fun w => u w 0) 0 z * (curlComp u 0 z) ^ 2
        + u z 0 / z.1 0 * (curlComp u 1 z) ^ 2
        + spatialPartial (fun w => u w 2) 2 z * (curlComp u 2 z) ^ 2
        + (spatialPartial (fun w => u w 0) 2 z + spatialPartial (fun w => u w 2) 0 z)
            * curlComp u 0 z * curlComp u 2 z
        - 2 * (u z 1 / z.1 0) * curlComp u 0 z * curlComp u 1 z := by
  simp only [Fin.sum_univ_three]
  rw [spatialPartial_one_zero_meridional haxi hu hz hplane hr,
    spatialPartial_one_one_meridional haxi hu hz hplane hr,
    spatialPartial_one_two_meridional haxi hu hz hplane hr]
  rw [curlComp_zero_meridional haxi hu hz hplane hr,
    curlComp_two_meridional haxi hu hz hplane hr]
  field_simp [hr]
  ring

end CIV
