/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.ScalarSystemSwirl
public import LeanPool.CIVAxisymmetric.Identities.Vorticity
public import LeanPool.CIVAxisymmetric.Identities.PartialCalculus

/-!
# The circulation component of the scalar Navier–Stokes equation on the meridional plane

`eq:aniso:circulation:pde` is the swirl component of the momentum equation written in terms of
the circulation `Γ = r u_θ`.  On the meridional plane `{x₂ = 0}` away from the axis, the
classical partials of `Γ` are expressed in terms of those of `u_θ` via the product rule; the
resulting equation follows directly from `scalar_nse_swirl` multiplied by `r`.

Away from the meridional plane `Γ = x₁ u₂ - x₂ u₁` picks up an extra term from the second
coordinate, so the product-rule expansions of its partials are proved first at every point of
the cylinder and only specialised to the plane (where that extra term vanishes) afterward; the
second derivatives are obtained by differentiating the plane-independent first-derivative
identity on a full neighbourhood of the base point and setting the second coordinate to zero
only in the final step.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



/-- The spatial partial derivative of a coordinate projection: `∂_i (x_j) = δ_{ij}`. -/
private theorem spatialPartial_coordinate (j i : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun w => w.1 j) i z = if i = j then 1 else 0 := by
  have h : spatialPartial (fun w => w.1 j) i z
      = (fderiv ℝ (fun x : Vec3 => x j) z.1) (basisVec i) := rfl
  rw [h]
  have hderiv : fderiv ℝ (fun x : Vec3 => x j) z.1
      = ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j := by
    apply hasFDerivAt_apply (𝕜 := ℝ) j z.1 |>.fderiv
  rw [hderiv, ContinuousLinearMap.proj_apply]
  by_cases h_eq : i = j
  · simp [h_eq]
  · have h_ne : j ≠ i := fun h => h_eq (h.symm)
    simp [h_eq, h_ne]

/-- General product-rule expansion of the first radial derivative of the circulation,
`∂_r Γ = u_θ + r ∂_r u_θ - x₂ ∂_r u_r`, valid at every point of the cylinder (not only on the
meridional plane). -/
private theorem spatialPartial_circulation_zero_gen {u : ParabolicPoint → Vec3}
    (hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (w : ParabolicPoint) (hw : w ∈ unitCylinder) :
    spatialPartial (circulation u) 0 w =
      u w 1 + w.1 0 * spatialPartial (fun v => u v 1) 0 w
        - w.1 1 * spatialPartial (fun v => u v 0) 0 w := by
  have hu1_diff : DifferentiableAt ℝ (fun y : Vec3 => u (y, w.2) 1) w.1 :=
    (differentiableAt_pi.1 (differentiableAt_spatialSlice hu1 hw)) 1
  have hu0_diff : DifferentiableAt ℝ (fun y : Vec3 => u (y, w.2) 0) w.1 :=
    (differentiableAt_pi.1 (differentiableAt_spatialSlice hu1 hw)) 0
  have hy0_diff : DifferentiableAt ℝ (fun y : Vec3 => y 0) w.1 :=
    (hasFDerivAt_apply (𝕜 := ℝ) 0 w.1).differentiableAt
  have hy1_diff : DifferentiableAt ℝ (fun y : Vec3 => y 1) w.1 :=
    (hasFDerivAt_apply (𝕜 := ℝ) 1 w.1).differentiableAt
  have hA : DifferentiableAt ℝ (fun y : Vec3 => y 0 * u (y, w.2) 1) w.1 := hy0_diff.fun_mul hu1_diff
  have hB : DifferentiableAt ℝ (fun y : Vec3 => y 1 * u (y, w.2) 0) w.1 := hy1_diff.fun_mul hu0_diff
  have hsub := spatialPartial_sub_of_differentiableAt
    (g := fun v : ParabolicPoint => v.1 0 * u v 1) (h := fun v : ParabolicPoint => v.1 1 * u v 0)
    (z := w) (i := (0 : Fin 3)) hA hB
  have hmul1 := spatialPartial_mul_of_differentiableAt
    (g := fun v : ParabolicPoint => v.1 0) (h := fun v : ParabolicPoint => u v 1)
    (z := w) (i := (0 : Fin 3)) hy0_diff hu1_diff
  have hmul2 := spatialPartial_mul_of_differentiableAt
    (g := fun v : ParabolicPoint => v.1 1) (h := fun v : ParabolicPoint => u v 0)
    (z := w) (i := (0 : Fin 3)) hy1_diff hu0_diff
  have hc0 : spatialPartial (fun v : ParabolicPoint => v.1 0) 0 w = 1 := by
    have h := spatialPartial_coordinate 0 0 w; simpa using h
  have hc1 : spatialPartial (fun v : ParabolicPoint => v.1 1) 0 w = 0 := by
    have h := spatialPartial_coordinate 1 0 w; simpa using h
  change spatialPartial (fun v : ParabolicPoint => v.1 0 * u v 1 - v.1 1 * u v 0) 0 w = _
  rw [hsub, hmul1, hmul2, hc0, hc1]
  ring

/-- General product-rule expansion of the first vertical derivative of the circulation,
`∂_z Γ = r ∂_z u_θ - x₂ ∂_z u_r`, valid at every point of the cylinder. -/
private theorem spatialPartial_circulation_two_gen {u : ParabolicPoint → Vec3}
    (hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (w : ParabolicPoint) (hw : w ∈ unitCylinder) :
    spatialPartial (circulation u) 2 w =
      w.1 0 * spatialPartial (fun v => u v 1) 2 w
        - w.1 1 * spatialPartial (fun v => u v 0) 2 w := by
  have hu1_diff : DifferentiableAt ℝ (fun y : Vec3 => u (y, w.2) 1) w.1 :=
    (differentiableAt_pi.1 (differentiableAt_spatialSlice hu1 hw)) 1
  have hu0_diff : DifferentiableAt ℝ (fun y : Vec3 => u (y, w.2) 0) w.1 :=
    (differentiableAt_pi.1 (differentiableAt_spatialSlice hu1 hw)) 0
  have hy0_diff : DifferentiableAt ℝ (fun y : Vec3 => y 0) w.1 :=
    (hasFDerivAt_apply (𝕜 := ℝ) 0 w.1).differentiableAt
  have hy1_diff : DifferentiableAt ℝ (fun y : Vec3 => y 1) w.1 :=
    (hasFDerivAt_apply (𝕜 := ℝ) 1 w.1).differentiableAt
  have hA : DifferentiableAt ℝ (fun y : Vec3 => y 0 * u (y, w.2) 1) w.1 := hy0_diff.fun_mul hu1_diff
  have hB : DifferentiableAt ℝ (fun y : Vec3 => y 1 * u (y, w.2) 0) w.1 := hy1_diff.fun_mul hu0_diff
  have hsub := spatialPartial_sub_of_differentiableAt
    (g := fun v : ParabolicPoint => v.1 0 * u v 1) (h := fun v : ParabolicPoint => v.1 1 * u v 0)
    (z := w) (i := (2 : Fin 3)) hA hB
  have hmul1 := spatialPartial_mul_of_differentiableAt
    (g := fun v : ParabolicPoint => v.1 0) (h := fun v : ParabolicPoint => u v 1)
    (z := w) (i := (2 : Fin 3)) hy0_diff hu1_diff
  have hmul2 := spatialPartial_mul_of_differentiableAt
    (g := fun v : ParabolicPoint => v.1 1) (h := fun v : ParabolicPoint => u v 0)
    (z := w) (i := (2 : Fin 3)) hy1_diff hu0_diff
  have hc0 : spatialPartial (fun v : ParabolicPoint => v.1 0) 2 w = 0 := by
    have h := spatialPartial_coordinate 0 2 w; simpa using h
  have hc1 : spatialPartial (fun v : ParabolicPoint => v.1 1) 2 w = 0 := by
    have h := spatialPartial_coordinate 1 2 w; simpa using h
  change spatialPartial (fun v : ParabolicPoint => v.1 0 * u v 1 - v.1 1 * u v 0) 2 w = _
  rw [hsub, hmul1, hmul2, hc0, hc1]
  ring

/-- First radial derivative of the circulation on the meridional plane: `∂_r Γ = u_θ + r ∂_r
u_θ`. -/
theorem spatialPartial_circulation_zero {u : ParabolicPoint → Vec3}
    (hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (w : ParabolicPoint) (hw : w ∈ unitCylinder) (hplane : w.1 1 = 0) :
    spatialPartial (circulation u) 0 w = u w 1 + w.1 0 * spatialPartial (fun v => u v 1) 0 w := by
  rw [spatialPartial_circulation_zero_gen hu1 w hw, hplane]
  ring

/-- First vertical derivative of the circulation on the meridional plane: `∂_z Γ = r ∂_z u_θ`. -/
theorem spatialPartial_circulation_two {u : ParabolicPoint → Vec3}
    (hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (w : ParabolicPoint) (hw : w ∈ unitCylinder) (hplane : w.1 1 = 0) :
    spatialPartial (circulation u) 2 w = w.1 0 * spatialPartial (fun v => u v 1) 2 w := by
  rw [spatialPartial_circulation_two_gen hu1 w hw, hplane]
  ring

/-- Second radial derivative of the circulation: `∂_r² Γ = 2 ∂_r u_θ + r ∂_r² u_θ`. -/
theorem spatialSecondPartial_circulation_zero_zero {u : ParabolicPoint → Vec3}
    (hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (w : ParabolicPoint) (hw : w ∈ unitCylinder) (hplane : w.1 1 = 0) :
    spatialSecondPartial (circulation u) 0 0 w =
      2 * spatialPartial (fun v => u v 1) 0 w + w.1 0 * spatialSecondPartial (fun v => u v 1) 0
        0 w := by
  have hx_mem : w.1 ∈ vec3Ball 0 1 := hw.1
  have ht_mem : w.2 ∈ Ioo (-1 : ℝ) 0 := hw.2
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder := hu2.of_le (by norm_num)
  have h_circ2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => circulation u z) unitCylinder := by
    unfold circulation
    have h0 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => z.1 0) unitCylinder :=
      ((contDiff_apply ℝ ℝ 0).comp contDiff_fst).contDiffOn
    have h1 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => z.1 1) unitCylinder :=
      ((contDiff_apply ℝ ℝ 1).comp contDiff_fst).contDiffOn
    have hu0' : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z 0) unitCylinder := contDiffOn_component
      hu2 0
    have hu1' : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z 1) unitCylinder := contDiffOn_component
      hu2 1
    exact (h0.mul hu1').sub (h1.mul hu0')
  have hu1_diff : DifferentiableAt ℝ (fun y : Vec3 => u (y, w.2) 1) w.1 :=
    (differentiableAt_pi.1 (differentiableAt_spatialSlice hu1 hw)) 1
  have hy0_diff : DifferentiableAt ℝ (fun y : Vec3 => y 0) w.1 :=
    (hasFDerivAt_apply (𝕜 := ℝ) 0 w.1).differentiableAt
  have hy1_diff : DifferentiableAt ℝ (fun y : Vec3 => y 1) w.1 :=
    (hasFDerivAt_apply (𝕜 := ℝ) 1 w.1).differentiableAt
  have h_spatial_u1 : DifferentiableAt ℝ (fun y : Vec3 => spatialPartial (fun v => u v 1) 0 (y,
    w.2)) w.1 :=
    differentiableAt_spatialPartial_slice (contDiffOn_component hu2 1) hw 0
  have h_spatial_u0 : DifferentiableAt ℝ (fun y : Vec3 => spatialPartial (fun v => u v 0) 0 (y,
    w.2)) w.1 :=
    differentiableAt_spatialPartial_slice (contDiffOn_component hu2 0) hw 0
  -- Transport the plane-independent first-derivative formula to a neighbourhood of `w.1`.
  have h_formula : (fun y : Vec3 => spatialPartial (circulation u) 0 (y, w.2)) =ᶠ[nhds w.1]
      (fun y : Vec3 => u (y, w.2) 1 + y 0 * spatialPartial (fun v => u v 1) 0 (y, w.2)
        - y 1 * spatialPartial (fun v => u v 0) 0 (y, w.2)) := by
    filter_upwards [(isOpen_vec3Ball 0 1).mem_nhds hx_mem] with y hy
    exact spatialPartial_circulation_zero_gen hu1 (y, w.2) ⟨hy, ht_mem⟩
  have h_key : spatialSecondPartial (circulation u) 0 0 w =
      spatialPartial (fun w' : ParabolicPoint =>
        u w' 1 + w'.1 0 * spatialPartial (fun v => u v 1) 0 w' - w'.1 1 * spatialPartial (fun v
          => u v 0) 0 w')
        0 w := by
    change (fderiv ℝ (fun y : Vec3 => spatialPartial (circulation u) 0 (y, w.2)) w.1) (basisVec 0) =
        (fderiv ℝ (fun y : Vec3 => u (y, w.2) 1 + y 0 * spatialPartial (fun v => u v 1) 0 (y, w.2)
          - y 1 * spatialPartial (fun v => u v 0) 0 (y, w.2)) w.1) (basisVec 0)
    rw [h_formula.fderiv_eq]
  -- Expand the outer `spatialPartial` of that closed-form expression term by term.
  have hT2diff : DifferentiableAt ℝ (fun y : Vec3 => y 0 * spatialPartial (fun v => u v 1) 0 (y,
    w.2)) w.1 :=
    hy0_diff.fun_mul h_spatial_u1
  have hT3diff : DifferentiableAt ℝ (fun y : Vec3 => y 1 * spatialPartial (fun v => u v 0) 0 (y,
    w.2)) w.1 :=
    hy1_diff.fun_mul h_spatial_u0
  have hT12diff : DifferentiableAt ℝ
      (fun y : Vec3 => u (y, w.2) 1 + y 0 * spatialPartial (fun v => u v 1) 0 (y, w.2)) w.1 :=
    hu1_diff.add hT2diff
  have hsub := spatialPartial_sub_of_differentiableAt
    (g := fun v : ParabolicPoint => u v 1 + v.1 0 * spatialPartial (fun v' => u v' 1) 0 v)
    (h := fun v : ParabolicPoint => v.1 1 * spatialPartial (fun v' => u v' 0) 0 v)
    (i := (0 : Fin 3)) hT12diff hT3diff
  have hadd := spatialPartial_add_of_differentiableAt
    (g := fun v : ParabolicPoint => u v 1)
    (h := fun v : ParabolicPoint => v.1 0 * spatialPartial (fun v' => u v' 1) 0 v)
    (i := (0 : Fin 3)) hu1_diff hT2diff
  have hmulT2 := spatialPartial_mul_of_differentiableAt
    (g := fun v : ParabolicPoint => v.1 0) (h := fun v : ParabolicPoint => spatialPartial (fun
      v' => u v' 1) 0 v)
    (i := (0 : Fin 3)) hy0_diff h_spatial_u1
  have hmulT3 := spatialPartial_mul_of_differentiableAt
    (g := fun v : ParabolicPoint => v.1 1) (h := fun v : ParabolicPoint => spatialPartial (fun
      v' => u v' 0) 0 v)
    (i := (0 : Fin 3)) hy1_diff h_spatial_u0
  have hc0 : spatialPartial (fun v : ParabolicPoint => v.1 0) 0 w = 1 := by
    have h := spatialPartial_coordinate 0 0 w; simpa using h
  have hc1 : spatialPartial (fun v : ParabolicPoint => v.1 1) 0 w = 0 := by
    have h := spatialPartial_coordinate 1 0 w; simpa using h
  have hss1 : spatialPartial (fun w' : ParabolicPoint => spatialPartial (fun v => u v 1) 0 w') 0 w
      = spatialSecondPartial (fun v => u v 1) 0 0 w := rfl
  have hss0 : spatialPartial (fun w' : ParabolicPoint => spatialPartial (fun v => u v 0) 0 w') 0 w
      = spatialSecondPartial (fun v => u v 0) 0 0 w := rfl
  rw [h_key, hsub, hadd, hmulT2, hmulT3, hc0, hc1, hss1, hss0, hplane]
  ring

/-- Second vertical derivative of the circulation: `∂_z² Γ = r ∂_z² u_θ`. -/
theorem spatialSecondPartial_circulation_two_two {u : ParabolicPoint → Vec3}
    (hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (w : ParabolicPoint) (hw : w ∈ unitCylinder) (hplane : w.1 1 = 0) :
    spatialSecondPartial (circulation u) 2 2 w =
      w.1 0 * spatialSecondPartial (fun v => u v 1) 2 2 w := by
  have hx_mem : w.1 ∈ vec3Ball 0 1 := hw.1
  have ht_mem : w.2 ∈ Ioo (-1 : ℝ) 0 := hw.2
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder := hu2.of_le (by norm_num)
  have h_circ2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => circulation u z) unitCylinder := by
    unfold circulation
    have h0 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => z.1 0) unitCylinder :=
      ((contDiff_apply ℝ ℝ 0).comp contDiff_fst).contDiffOn
    have h1 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => z.1 1) unitCylinder :=
      ((contDiff_apply ℝ ℝ 1).comp contDiff_fst).contDiffOn
    have hu0' : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z 0) unitCylinder := contDiffOn_component
      hu2 0
    have hu1' : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z 1) unitCylinder := contDiffOn_component
      hu2 1
    exact (h0.mul hu1').sub (h1.mul hu0')
  have hy0_diff : DifferentiableAt ℝ (fun y : Vec3 => y 0) w.1 :=
    (hasFDerivAt_apply (𝕜 := ℝ) 0 w.1).differentiableAt
  have hy1_diff : DifferentiableAt ℝ (fun y : Vec3 => y 1) w.1 :=
    (hasFDerivAt_apply (𝕜 := ℝ) 1 w.1).differentiableAt
  have h_spatial_u1 : DifferentiableAt ℝ (fun y : Vec3 => spatialPartial (fun v => u v 1) 2 (y,
    w.2)) w.1 :=
    differentiableAt_spatialPartial_slice (contDiffOn_component hu2 1) hw 2
  have h_spatial_u0 : DifferentiableAt ℝ (fun y : Vec3 => spatialPartial (fun v => u v 0) 2 (y,
    w.2)) w.1 :=
    differentiableAt_spatialPartial_slice (contDiffOn_component hu2 0) hw 2
  have h_formula : (fun y : Vec3 => spatialPartial (circulation u) 2 (y, w.2)) =ᶠ[nhds w.1]
      (fun y : Vec3 => y 0 * spatialPartial (fun v => u v 1) 2 (y, w.2)
        - y 1 * spatialPartial (fun v => u v 0) 2 (y, w.2)) := by
    filter_upwards [(isOpen_vec3Ball 0 1).mem_nhds hx_mem] with y hy
    exact spatialPartial_circulation_two_gen hu1 (y, w.2) ⟨hy, ht_mem⟩
  have h_key : spatialSecondPartial (circulation u) 2 2 w =
      spatialPartial (fun w' : ParabolicPoint =>
        w'.1 0 * spatialPartial (fun v => u v 1) 2 w' - w'.1 1 * spatialPartial (fun v => u v 0)
          2 w')
        2 w := by
    change (fderiv ℝ (fun y : Vec3 => spatialPartial (circulation u) 2 (y, w.2)) w.1) (basisVec 2) =
        (fderiv ℝ (fun y : Vec3 => y 0 * spatialPartial (fun v => u v 1) 2 (y, w.2)
          - y 1 * spatialPartial (fun v => u v 0) 2 (y, w.2)) w.1) (basisVec 2)
    rw [h_formula.fderiv_eq]
  have hT2diff : DifferentiableAt ℝ (fun y : Vec3 => y 0 * spatialPartial (fun v => u v 1) 2 (y,
    w.2)) w.1 :=
    hy0_diff.fun_mul h_spatial_u1
  have hT3diff : DifferentiableAt ℝ (fun y : Vec3 => y 1 * spatialPartial (fun v => u v 0) 2 (y,
    w.2)) w.1 :=
    hy1_diff.fun_mul h_spatial_u0
  have hsub := spatialPartial_sub_of_differentiableAt
    (g := fun v : ParabolicPoint => v.1 0 * spatialPartial (fun v' => u v' 1) 2 v)
    (h := fun v : ParabolicPoint => v.1 1 * spatialPartial (fun v' => u v' 0) 2 v)
    (i := (2 : Fin 3)) hT2diff hT3diff
  have hmulT2 := spatialPartial_mul_of_differentiableAt
    (g := fun v : ParabolicPoint => v.1 0) (h := fun v : ParabolicPoint => spatialPartial (fun
      v' => u v' 1) 2 v)
    (i := (2 : Fin 3)) hy0_diff h_spatial_u1
  have hmulT3 := spatialPartial_mul_of_differentiableAt
    (g := fun v : ParabolicPoint => v.1 1) (h := fun v : ParabolicPoint => spatialPartial (fun
      v' => u v' 0) 2 v)
    (i := (2 : Fin 3)) hy1_diff h_spatial_u0
  have hc0 : spatialPartial (fun v : ParabolicPoint => v.1 0) 2 w = 0 := by
    have h := spatialPartial_coordinate 0 2 w; simpa using h
  have hc1 : spatialPartial (fun v : ParabolicPoint => v.1 1) 2 w = 0 := by
    have h := spatialPartial_coordinate 1 2 w; simpa using h
  have hss1 : spatialPartial (fun w' : ParabolicPoint => spatialPartial (fun v => u v 1) 2 w') 2 w
      = spatialSecondPartial (fun v => u v 1) 2 2 w := rfl
  have hss0 : spatialPartial (fun w' : ParabolicPoint => spatialPartial (fun v => u v 0) 2 w') 2 w
      = spatialSecondPartial (fun v => u v 0) 2 2 w := rfl
  rw [h_key, hsub, hmulT2, hmulT3, hc0, hc1, hss1, hss0, hplane]
  ring

/-- The circulation component `eq:aniso:circulation:pde` of the scalar Navier–Stokes equation:
for a classical solution with axisymmetric velocity and axisymmetric force, on the meridional
plane off the axis, `∂_t Γ + u_r ∂_r Γ + u_z ∂_z Γ = ∂_r² Γ - r⁻¹ ∂_r Γ + ∂_z² Γ + r f_θ`. -/
theorem circulation_pde
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hfaxi : IsAxisymmetricOn f unitCylinder)
    (z : ParabolicPoint) (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    timePartial (circulation u) z + u z 0 * spatialPartial (circulation u) 0 z
        + u z 2 * spatialPartial (circulation u) 2 z =
      spatialSecondPartial (circulation u) 0 0 z - spatialPartial (circulation u) 0 z / z.1 0
        + spatialSecondPartial (circulation u) 2 2 z + z.1 0 * f z 1 := by
  -- Smoothness from the classical solution hypothesis
  have hu_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu_smooth.of_le (by norm_num)
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu_smooth.of_le (by norm_num)
  -- Time derivative of circulation on the plane
  have hu1_dtime : DifferentiableAt ℝ (fun s : ℝ => u (z.1, s) 1) z.2 := by
    have h_cont : ContDiffOn ℝ 1 (fun s : ℝ => u (z.1, s)) (Ioo (-1 : ℝ) 0) :=
      hu1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun s hs => ⟨hz.1, hs⟩)
    exact differentiableAt_pi.1 (h_cont.differentiableOn_one.differentiableAt
      (isOpen_Ioo.mem_nhds hz.2)) 1
  have hu0_dtime : DifferentiableAt ℝ (fun s : ℝ => u (z.1, s) 0) z.2 := by
    have h_cont : ContDiffOn ℝ 1 (fun s : ℝ => u (z.1, s)) (Ioo (-1 : ℝ) 0) :=
      hu1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun s hs => ⟨hz.1, hs⟩)
    exact differentiableAt_pi.1 (h_cont.differentiableOn_one.differentiableAt
      (isOpen_Ioo.mem_nhds hz.2)) 0
  have h_time : timePartial (circulation u) z = z.1 0 * timePartial (fun w => u w 1) z := by
    have key : deriv (fun s : ℝ => z.1 0 * u (z.1, s) 1 - z.1 1 * u (z.1, s) 0) z.2 =
        z.1 0 * deriv (fun s : ℝ => u (z.1, s) 1) z.2 - z.1 1 * deriv (fun s : ℝ => u (z.1, s)
          0) z.2 :=
      ((hu1_dtime.hasDerivAt.const_mul (z.1 0)).sub (hu0_dtime.hasDerivAt.const_mul (z.1 1))).deriv
    change deriv (fun s : ℝ => z.1 0 * u (z.1, s) 1 - z.1 1 * u (z.1, s) 0) z.2 =
        z.1 0 * deriv (fun s : ℝ => u (z.1, s) 1) z.2
    rw [key, hplane]
    ring
  -- First spatial derivatives
  have h_spatial0 : spatialPartial (circulation u) 0 z = u z 1 + z.1 0 * spatialPartial (fun w
    => u w 1) 0 z :=
    spatialPartial_circulation_zero hu1 z hz hplane
  have h_spatial2 : spatialPartial (circulation u) 2 z = z.1 0 * spatialPartial (fun w => u w 1)
    2 z :=
    spatialPartial_circulation_two hu1 z hz hplane
  -- Second spatial derivatives
  have h_spatialSecond00 : spatialSecondPartial (circulation u) 0 0 z =
      2 * spatialPartial (fun w => u w 1) 0 z + z.1 0 * spatialSecondPartial (fun w => u w 1) 0
        0 z :=
    spatialSecondPartial_circulation_zero_zero hu2 z hz hplane
  have h_spatialSecond22 : spatialSecondPartial (circulation u) 2 2 z =
      z.1 0 * spatialSecondPartial (fun w => u w 1) 2 2 z :=
    spatialSecondPartial_circulation_two_two hu2 z hz hplane
  -- Use the swirl equation, scaled by `r = z.1 0`
  have h_swirl := scalar_nse_swirl u p f hsol haxi hfaxi z hz hplane hr
  rw [h_time, h_spatial0, h_spatial2, h_spatialSecond00, h_spatialSecond22]
  field_simp [hr] at h_swirl ⊢
  linear_combination h_swirl

end CIV
