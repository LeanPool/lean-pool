/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.Axisymmetric

/-!
# The Laplacian of an axisymmetric field in cylindrical form

Differentiating the infinitesimal identities of `CIV.Identities.Axisymmetric` once more in
the second Cartesian direction gives the missing second derivative on the meridional plane:
for an axisymmetric scalar, `∂₂∂₂ g = r⁻¹ ∂_r g`, so the Cartesian Laplacian becomes the
cylindrical one `∂_r² + r⁻¹ ∂_r + ∂_z²` of `eq:aniso:scalar:nse:z`. For the radial and swirl
components of an axisymmetric field the same computation carries the source term of the
infinitesimal identity and produces the extra `-r⁻²` of `eq:aniso:scalar:nse:r` and
`eq:aniso:scalar:nse:swirl`.

The differentiation is carried out on the slice `y ↦ g (y, t)` of the unit ball, where the
identity of `angularGenerator_of_invariant` holds at every point; the product rule in the
direction of the second basis vector and the vanishing of the second coordinate on the
meridional plane leave exactly one term.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- A classical spatial partial derivative of a `C²` scalar is differentiable in space. -/
theorem differentiableAt_spatialPartial_slice {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => g z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i : Fin 3) :
    DifferentiableAt ℝ (fun y : Vec3 => spatialPartial g i (y, z.2)) z.1 := by
  have hS : ContDiffOn ℝ 2 (fun y : Vec3 => g (y, z.2)) (vec3Ball 0 1) :=
    contDiffOn_spatialSlice hg hz.2
  have hD : ContDiffOn ℝ 1 (fderiv ℝ fun y : Vec3 => g (y, z.2)) (vec3Ball 0 1) :=
    hS.fderiv_of_isOpen (isOpen_vec3Ball 0 1) (by norm_num)
  have hE : ContDiffOn ℝ 1 (fun y : Vec3 => spatialPartial g i (y, z.2)) (vec3Ball 0 1) :=
    hD.clm_apply contDiffOn_const
  exact (hE.differentiableOn one_ne_zero).differentiableAt ((isOpen_vec3Ball 0 1).mem_nhds hz.1)

/-- Differentiating the infinitesimal identity `-x₂ ∂₁g + x₁ ∂₂g = s` in the second Cartesian
direction: on the meridional plane the second derivative `∂₂∂₂g` is determined by `∂₁g` and by
the second derivative of the source. -/
theorem spatialSecondPartial_one_one_of_angularGenerator {g s : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => g z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder)
    (hs : DifferentiableAt ℝ (fun y : Vec3 => s (y, z.2)) z.1)
    (hrel : ∀ y ∈ vec3Ball 0 1,
      -y 1 * spatialPartial g 0 (y, z.2) + y 0 * spatialPartial g 1 (y, z.2) = s (y, z.2))
    (hplane : z.1 1 = 0) :
    z.1 0 * spatialSecondPartial g 1 1 z = spatialPartial g 0 z + spatialPartial s 1 z := by
  obtain ⟨x, t⟩ := z
  have hA : DifferentiableAt ℝ (fun y : Vec3 => spatialPartial g 0 (y, t)) x :=
    differentiableAt_spatialPartial_slice hg hz 0
  have hB : DifferentiableAt ℝ (fun y : Vec3 => spatialPartial g 1 (y, t)) x :=
    differentiableAt_spatialPartial_slice hg hz 1
  have hp0 : HasFDerivAt (fun y : Vec3 => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0) x :=
    hasFDerivAt_apply (𝕜 := ℝ) 0 x
  have hp1 : HasFDerivAt (fun y : Vec3 => y 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1) x :=
    hasFDerivAt_apply (𝕜 := ℝ) 1 x
  have hΦ := (hp1.neg.fun_mul hA.hasFDerivAt).add (hp0.fun_mul hB.hasFDerivAt)
  have hev : (fun y : Vec3 => s (y, t)) =ᶠ[nhds x]
      fun y : Vec3 => -y 1 * spatialPartial g 0 (y, t) + y 0 * spatialPartial g 1 (y, t) := by
    filter_upwards [(isOpen_vec3Ball 0 1).mem_nhds hz.1] with y hy
    exact (hrel y hy).symm
  have happ := DFunLike.congr_fun (hΦ.congr_of_eventuallyEq hev).fderiv (basisVec 1)
  simp only [add_apply, smul_apply, neg_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    basisVec_apply] at happ
  norm_num at happ
  have hp : x 1 = 0 := hplane
  rw [hp] at happ
  have hgg : spatialSecondPartial g 1 1 (x, t)
      = (fderiv ℝ (fun y : Vec3 => spatialPartial g 1 (y, t)) x) (basisVec 1) := rfl
  have hss : spatialPartial s 1 (x, t)
      = (fderiv ℝ (fun y : Vec3 => s (y, t)) x) (basisVec 1) := rfl
  have hx0 : ((x, t) : ParabolicPoint).1 0 = x 0 := rfl
  rw [hx0, hgg, hss, happ]
  ring

/-- A classical spatial partial derivative is odd under negation of the scalar. -/
theorem spatialPartial_neg (g : ParabolicPoint → ℝ) (i : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun w => -g w) i z = -spatialPartial g i z := by
  change fderiv ℝ (fun y : Vec3 => -g (y, z.2)) z.1 (basisVec i) = _
  rw [fderiv_fun_neg]
  rfl

/-- The classical spatial partial derivatives of the zero scalar vanish. -/
theorem spatialPartial_zero_fun (i : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun _ : ParabolicPoint => (0 : ℝ)) i z = 0 := by
  change fderiv ℝ (fun _ : Vec3 => (0 : ℝ)) z.1 (basisVec i) = 0
  rw [fderiv_fun_const]
  rfl

/-! ### The cylindrical Laplacian of an axisymmetric scalar -/

/-- For a rotation-invariant `C²` scalar, on the meridional plane off the axis,
`∂₂∂₂g = r⁻¹ ∂_r g`. -/
theorem spatialSecondPartial_one_one_of_invariant {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => g z) unitCylinder)
    (hinv : ∀ (φ : ℝ) (w : ParabolicPoint), w ∈ unitCylinder → g (rotZ φ w.1, w.2) = g w)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    spatialSecondPartial g 1 1 z = spatialPartial g 0 z / z.1 0 := by
  have hg1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => g w) unitCylinder := hg.of_le (by norm_num)
  have key := spatialSecondPartial_one_one_of_angularGenerator (s := fun _ => (0 : ℝ)) hg hz
    (differentiableAt_const 0)
    (fun y hy => angularGenerator_of_invariant hg1 hinv (z := (y, z.2)) ⟨hy, hz.2⟩) hplane
  rw [spatialPartial_zero_fun, add_zero] at key
  rw [eq_div_iff hr]
  linear_combination key

/-- For a rotation-invariant `C²` scalar, on the meridional plane off the axis, the Cartesian
Laplacian is the cylindrical Laplacian `∂_r² + r⁻¹ ∂_r + ∂_z²` of `eq:aniso:scalar:nse:z`. -/
theorem sum_spatialSecondPartial_of_invariant {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => g z) unitCylinder)
    (hinv : ∀ (φ : ℝ) (w : ParabolicPoint), w ∈ unitCylinder → g (rotZ φ w.1, w.2) = g w)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    ∑ j : Fin 3, spatialSecondPartial g j j z
      = spatialSecondPartial g 0 0 z + spatialPartial g 0 z / z.1 0
        + spatialSecondPartial g 2 2 z := by
  rw [Fin.sum_univ_three, spatialSecondPartial_one_one_of_invariant hg hinv hz hplane hr]

/-! ### The cylindrical Laplacian of the components of an axisymmetric field -/

/-- On the meridional plane, off the axis, the second Cartesian derivative of the radial
component in the second direction is `r⁻¹ ∂_r u_r - r⁻² u_r`. -/
theorem spatialSecondPartial_one_one_zero_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    spatialSecondPartial (fun w => u w 0) 1 1 z
      = spatialPartial (fun w => u w 0) 0 z / z.1 0 - u z 0 / z.1 0 ^ 2 := by
  have hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder := hu.of_le (by norm_num)
  have hs : DifferentiableAt ℝ (fun y : Vec3 => -u (y, z.2) 1) z.1 :=
    (differentiableAt_pi.1 (differentiableAt_spatialSlice hu1 hz) 1).neg
  have key := spatialSecondPartial_one_one_of_angularGenerator (g := fun w => u w 0)
    (s := fun w => -u w 1) (contDiffOn_component hu 0) hz hs
    (fun y hy => angularGenerator_zero h hu1 (z := (y, z.2)) ⟨hy, hz.2⟩) hplane
  rw [spatialPartial_neg, spatialPartial_one_one_meridional h hu1 hz hplane hr] at key
  field_simp at key ⊢
  linarith only [key]

/-- On the meridional plane, off the axis, the second Cartesian derivative of the swirl in the
second direction is `r⁻¹ ∂_r u_θ - r⁻² u_θ`. -/
theorem spatialSecondPartial_one_one_one_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    spatialSecondPartial (fun w => u w 1) 1 1 z
      = spatialPartial (fun w => u w 1) 0 z / z.1 0 - u z 1 / z.1 0 ^ 2 := by
  have hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder := hu.of_le (by norm_num)
  have hs : DifferentiableAt ℝ (fun y : Vec3 => u (y, z.2) 0) z.1 :=
    differentiableAt_pi.1 (differentiableAt_spatialSlice hu1 hz) 0
  have key := spatialSecondPartial_one_one_of_angularGenerator (g := fun w => u w 1)
    (s := fun w => u w 0) (contDiffOn_component hu 1) hz hs
    (fun y hy => angularGenerator_one h hu1 (z := (y, z.2)) ⟨hy, hz.2⟩) hplane
  rw [spatialPartial_one_zero_meridional h hu1 hz hplane hr] at key
  field_simp at key ⊢
  linarith only [key]

/-- On the meridional plane, off the axis, the second Cartesian derivative of the vertical
component in the second direction is `r⁻¹ ∂_r u_z`. -/
theorem spatialSecondPartial_one_one_two_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    spatialSecondPartial (fun w => u w 2) 1 1 z
      = spatialPartial (fun w => u w 2) 0 z / z.1 0 := by
  have hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder := hu.of_le (by norm_num)
  have key := spatialSecondPartial_one_one_of_angularGenerator (g := fun w => u w 2)
    (s := fun _ => (0 : ℝ)) (contDiffOn_component hu 2) hz (differentiableAt_const 0)
    (fun y hy => angularGenerator_two h hu1 (z := (y, z.2)) ⟨hy, hz.2⟩) hplane
  rw [spatialPartial_zero_fun, add_zero] at key
  rw [eq_div_iff hr]
  linear_combination key

/-- The Cartesian Laplacian of the radial component on the meridional plane, off the axis:
the cylindrical operator `∂_r² + r⁻¹ ∂_r + ∂_z² - r⁻²` of `eq:aniso:scalar:nse:r`. -/
theorem sum_spatialSecondPartial_zero_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    ∑ j : Fin 3, spatialSecondPartial (fun w => u w 0) j j z
      = spatialSecondPartial (fun w => u w 0) 0 0 z + spatialPartial (fun w => u w 0) 0 z / z.1 0
        + spatialSecondPartial (fun w => u w 0) 2 2 z - u z 0 / z.1 0 ^ 2 := by
  rw [Fin.sum_univ_three, spatialSecondPartial_one_one_zero_meridional h hu hz hplane hr]
  ring

/-- The Cartesian Laplacian of the swirl on the meridional plane, off the axis: the cylindrical
operator `∂_r² + r⁻¹ ∂_r + ∂_z² - r⁻²` of `eq:aniso:scalar:nse:swirl`. -/
theorem sum_spatialSecondPartial_one_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    ∑ j : Fin 3, spatialSecondPartial (fun w => u w 1) j j z
      = spatialSecondPartial (fun w => u w 1) 0 0 z + spatialPartial (fun w => u w 1) 0 z / z.1 0
        + spatialSecondPartial (fun w => u w 1) 2 2 z - u z 1 / z.1 0 ^ 2 := by
  rw [Fin.sum_univ_three, spatialSecondPartial_one_one_one_meridional h hu hz hplane hr]
  ring

/-- The Cartesian Laplacian of the vertical component on the meridional plane, off the axis:
the cylindrical operator `∂_r² + r⁻¹ ∂_r + ∂_z²` of `eq:aniso:scalar:nse:z`. -/
theorem sum_spatialSecondPartial_two_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    ∑ j : Fin 3, spatialSecondPartial (fun w => u w 2) j j z
      = spatialSecondPartial (fun w => u w 2) 0 0 z + spatialPartial (fun w => u w 2) 0 z / z.1 0
        + spatialSecondPartial (fun w => u w 2) 2 2 z := by
  rw [Fin.sum_univ_three, spatialSecondPartial_one_one_two_meridional h hu hz hplane hr]

end CIV
