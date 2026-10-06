/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Cylinder
public import LeanPool.CIVAxisymmetric.Setting.Rotation
public import LeanPool.CIVAxisymmetric.Setting.RotationLemmas
public import LeanPool.CIVAxisymmetric.Setting.AngularMeanSmooth
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Infinitesimal consequences of rotation invariance

An axisymmetric field on the unit cylinder is equivariant, `u (Q_φ x, t) = Q_φ u (x, t)`
(`apply_rotZ`). Differentiating this identity in the angle at `φ = 0` gives the three
scalar identities of `angularGenerator_zero`, `angularGenerator_one` and
`angularGenerator_two`: with the generator `J x = (-x₂, x₁, 0)` of the rotations,
`J u(x, t) = Du(x, t) (J x)`.

On the meridional plane `{x₂ = 0}` away from the axis these become the `θ`-derivative
relations `∂₂u₁ = -u₂/r`, `∂₂u₂ = u₁/r`, `∂₂u₃ = 0` (design note R4: the cylindrical
coefficients of an axisymmetric field are read on that plane, where `u_r = u₁`,
`u_θ = u₂`, `u_z = u₃` and `∂_r = ∂₁`, `∂_z = ∂₃`). They are what turns the Cartesian
divergence, curl and Laplacian into their cylindrical forms
`eq:aniso:scalar:nse:div`, `eq:aniso:vorticity` and the right-hand sides of
`eq:aniso:scalar:nse`.

Differentiating the equivariance in the space variable instead gives
`fderiv_comp_rotZ`, the commutation `Du(Q_φ x) Q_φ = Q_φ Du(x)`. At `φ = π` it yields
the structure on the axis quoted in the standing assumptions of Section
`sec:aniso:equations`: `u_r`, `u_θ`, `∂_z u_r`, `∂_z u_θ` and `∂_r u_z` all vanish
there, and the components are odd, odd and even under the reflection
`(x₁, 0, x₃) ↦ (-x₁, 0, x₃)` of the meridional plane.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Spatial slices of a field on the cylinder -/

section Slice

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : ParabolicPoint → E}

/-- A field of class `C^n` on the unit cylinder has `C^n` spatial slices on the unit ball. -/
theorem contDiffOn_spatialSlice {n : WithTop ℕ∞}
    (hv : ContDiffOn ℝ n (fun z : Vec3 × ℝ => v z) unitCylinder) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 0) :
    ContDiffOn ℝ n (fun y : Vec3 => v (y, t)) (vec3Ball 0 1) :=
  hv.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun _ hy => ⟨hy, ht⟩

/-- The spatial slice of a `C¹` field is differentiable at every point of the cylinder. -/
theorem differentiableAt_spatialSlice
    (hv : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => v z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    DifferentiableAt ℝ (fun y : Vec3 => v (y, z.2)) z.1 :=
  ((contDiffOn_spatialSlice hv hz.2).differentiableOn one_ne_zero).differentiableAt
    ((isOpen_vec3Ball 0 1).mem_nhds hz.1)

end Slice

/-- A component of a `C^n` field is `C^n`. -/
theorem contDiffOn_component {n : WithTop ℕ∞} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ n (fun z : Vec3 × ℝ => u z) unitCylinder) (i : Fin 3) :
    ContDiffOn ℝ n (fun z : Vec3 × ℝ => u z i) unitCylinder :=
  contDiffOn_pi.1 hu i

/-- The spatial derivative of a component is the corresponding component of the spatial
derivative. -/
theorem fderiv_spatialSlice_apply {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i : Fin 3) (w : Vec3) :
    fderiv ℝ (fun y : Vec3 => u (y, z.2) i) z.1 w
      = fderiv ℝ (fun y : Vec3 => u (y, z.2)) z.1 w i := by
  have hF := (differentiableAt_spatialSlice hu hz).hasFDerivAt
  exact DFunLike.congr_fun (hasFDerivAt_pi'.1 hF i).fderiv w

/-- Each classical spatial partial derivative of a component is read off the full spatial
derivative. -/
theorem spatialPartial_eq_fderiv_apply {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i j : Fin 3) :
    spatialPartial (fun w => u w i) j z
      = fderiv ℝ (fun y : Vec3 => u (y, z.2)) z.1 (basisVec j) i :=
  fderiv_spatialSlice_apply hu hz i (basisVec j)

/-! ### The generator of the rotations -/

/-- The angle derivative of `φ ↦ Q_φ x` at `φ = 0` is the generator `J x = (-x₂, x₁, 0)`. -/
theorem hasDerivAt_rotZ_zero (x : Vec3) :
    HasDerivAt (fun φ : ℝ => rotZ φ x) ![-x 1, x 0, 0] 0 := by
  have h0 : HasDerivAt (fun φ : ℝ => Real.cos φ * x 0 - Real.sin φ * x 1)
      (-Real.sin 0 * x 0 - Real.cos 0 * x 1) 0 :=
    ((Real.hasDerivAt_cos 0).mul_const (x 0)).sub ((Real.hasDerivAt_sin 0).mul_const (x 1))
  have h1 : HasDerivAt (fun φ : ℝ => Real.sin φ * x 0 + Real.cos φ * x 1)
      (Real.cos 0 * x 0 + -Real.sin 0 * x 1) 0 :=
    ((Real.hasDerivAt_sin 0).mul_const (x 0)).add ((Real.hasDerivAt_cos 0).mul_const (x 1))
  rw [Real.sin_zero, Real.cos_zero] at h0 h1
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [rotZ] using h0
  · simpa [rotZ] using h1
  · simpa [rotZ] using hasDerivAt_const (0 : ℝ) (x 2)

/-- The angle derivative at `φ = 0` of a `C¹` scalar transported along the rotations is the
derivative of the scalar along the generator. -/
theorem hasDerivAt_comp_rotZ {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => g z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    HasDerivAt (fun φ : ℝ => g (rotZ φ z.1, z.2))
      (-z.1 1 * spatialPartial g 0 z + z.1 0 * spatialPartial g 1 z) 0 := by
  have hL : HasFDerivAt (fun y : Vec3 => g (y, z.2))
      (fderiv ℝ (fun y : Vec3 => g (y, z.2)) z.1) z.1 :=
    (differentiableAt_spatialSlice hg hz).hasFDerivAt
  have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq (hl := hL) (hf := hasDerivAt_rotZ_zero z.1)
    (hy := (rotZ_zero_apply z.1).symm)
  have hsplit : (![-z.1 1, z.1 0, 0] : Vec3)
      = (-z.1 1) • basisVec 0 + (z.1 0) • basisVec 1 := by
    ext i
    fin_cases i <;> simp [basisVec_apply]
  have hval : (fderiv ℝ (fun y : Vec3 => g (y, z.2)) z.1) ![-z.1 1, z.1 0, 0]
      = -z.1 1 * spatialPartial g 0 z + z.1 0 * spatialPartial g 1 z := by
    rw [hsplit, map_add, map_smul, map_smul]
    rfl
  rw [hval] at hcomp
  exact hcomp

/-! ### Equivariance of an axisymmetric field -/

/-- An axisymmetric field on the unit cylinder is equivariant under the rotations:
`u (Q_φ x, t) = Q_φ u (x, t)` (Section `sec:aniso:notation`). -/
theorem IsAxisymmetricOn.apply_rotZ {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder) (φ : ℝ) {z : ParabolicPoint} (hz : z ∈ unitCylinder) :
    u (rotZ φ z.1, z.2) = rotZ φ (u z) := by
  have hz' : ((rotZ φ z.1 : Vec3), z.2) ∈ unitCylinder := rotZ_mem_unitCylinder φ hz
  have key := (isAxisymmetricOn_unitCylinder_iff u).1 h φ (rotZ φ z.1, z.2) hz'
  have hval : rotField φ u ((rotZ φ z.1 : Vec3), z.2) = rotZ φ (u z) := by
    change rotZ φ (u (rotZ (-φ) (rotZ φ z.1), z.2)) = rotZ φ (u z)
    rw [rotZ_neg_rotZ]
    rfl
  rw [hval] at key
  exact key.symm

/-! ### The three infinitesimal identities -/

/-- Master form of the infinitesimal identity: whatever the angle derivative at `φ = 0` of
`φ ↦ g (Q_φ x, t)` is, it equals the derivative of `g` along the generator. -/
theorem angularGenerator_of_hasDerivAt {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => g z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) {c : ℝ} (hc : HasDerivAt (fun φ : ℝ => g (rotZ φ z.1, z.2)) c 0) :
    -z.1 1 * spatialPartial g 0 z + z.1 0 * spatialPartial g 1 z = c :=
  (hasDerivAt_comp_rotZ hg hz).unique hc

/-- The infinitesimal form of rotation invariance, first component: `-x₂ ∂₁u₁ + x₁ ∂₂u₁ = -u₂`
(`sec:aniso:equations`). -/
theorem angularGenerator_zero {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    -z.1 1 * spatialPartial (fun w => u w 0) 0 z + z.1 0 * spatialPartial (fun w => u w 0) 1 z
      = -u z 1 := by
  refine angularGenerator_of_hasDerivAt (contDiffOn_component hu 0) hz ?_
  refine HasDerivAt.congr_of_eventuallyEq
    ((hasDerivAt_pi.1 (hasDerivAt_rotZ_zero (u z))) 0) ?_
  filter_upwards with φ
  rw [h.apply_rotZ φ hz]

/-- The infinitesimal form of rotation invariance, second component:
`-x₂ ∂₁u₂ + x₁ ∂₂u₂ = u₁`. -/
theorem angularGenerator_one {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    -z.1 1 * spatialPartial (fun w => u w 1) 0 z + z.1 0 * spatialPartial (fun w => u w 1) 1 z
      = u z 0 := by
  refine angularGenerator_of_hasDerivAt (contDiffOn_component hu 1) hz ?_
  refine HasDerivAt.congr_of_eventuallyEq
    ((hasDerivAt_pi.1 (hasDerivAt_rotZ_zero (u z))) 1) ?_
  filter_upwards with φ
  rw [h.apply_rotZ φ hz]

/-- The infinitesimal form of rotation invariance, third component:
`-x₂ ∂₁u₃ + x₁ ∂₂u₃ = 0`. -/
theorem angularGenerator_two {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    -z.1 1 * spatialPartial (fun w => u w 2) 0 z + z.1 0 * spatialPartial (fun w => u w 2) 1 z
      = 0 := by
  refine angularGenerator_of_hasDerivAt (contDiffOn_component hu 2) hz ?_
  refine HasDerivAt.congr_of_eventuallyEq
    ((hasDerivAt_pi.1 (hasDerivAt_rotZ_zero (u z))) 2) ?_
  filter_upwards with φ
  rw [h.apply_rotZ φ hz]

/-- For a rotation-invariant scalar the derivative along the generator vanishes:
`-x₂ ∂₁g + x₁ ∂₂g = 0`. -/
theorem angularGenerator_of_invariant {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => g z) unitCylinder)
    (hinv : ∀ (φ : ℝ) (w : ParabolicPoint), w ∈ unitCylinder → g (rotZ φ w.1, w.2) = g w)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) :
    -z.1 1 * spatialPartial g 0 z + z.1 0 * spatialPartial g 1 z = 0 := by
  refine angularGenerator_of_hasDerivAt hg hz ?_
  refine HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const (0 : ℝ) (g z)) ?_
  filter_upwards with φ
  exact hinv φ z hz

/-! ### The `θ`-derivative relations on the meridional plane -/

/-- On the meridional plane, off the axis, `∂_θ u_r = -u_θ`: the second Cartesian partial
derivative of the first component is `-u_θ / r` (design note R4). -/
theorem spatialPartial_one_zero_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    spatialPartial (fun w => u w 0) 1 z = -u z 1 / z.1 0 := by
  have hgen := angularGenerator_zero h hu hz
  rw [hplane] at hgen
  rw [eq_div_iff hr]
  linear_combination hgen

/-- On the meridional plane, off the axis, `∂_θ u_θ = u_r`: the second Cartesian partial
derivative of the second component is `u_r / r` (design note R4). -/
theorem spatialPartial_one_one_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    spatialPartial (fun w => u w 1) 1 z = u z 0 / z.1 0 := by
  have hgen := angularGenerator_one h hu hz
  rw [hplane] at hgen
  rw [eq_div_iff hr]
  linear_combination hgen

/-- On the meridional plane, off the axis, `∂_θ u_z = 0`: the second Cartesian partial
derivative of the third component vanishes (design note R4). -/
theorem spatialPartial_one_two_meridional {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    spatialPartial (fun w => u w 2) 1 z = 0 := by
  have hgen := angularGenerator_two h hu hz
  rw [hplane] at hgen
  have := mul_eq_zero.1 (by linear_combination hgen :
    z.1 0 * spatialPartial (fun w => u w 2) 1 z = 0)
  exact this.resolve_left hr

/-! ### The derivative intertwines the rotations -/

/-- The spatial derivative of an axisymmetric field intertwines the rotations:
`Du(Q_φ x, t) Q_φ = Q_φ Du(x, t)`. -/
theorem fderiv_comp_rotZ {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (φ : ℝ) (w : Vec3) :
    fderiv ℝ (fun y : Vec3 => u (y, z.2)) (rotZ φ z.1) (rotZ φ w)
      = rotZ φ (fderiv ℝ (fun y : Vec3 => u (y, z.2)) z.1 w) := by
  have hz' : ((rotZ φ z.1 : Vec3), z.2) ∈ unitCylinder := rotZ_mem_unitCylinder φ hz
  have hL : HasFDerivAt (fun y : Vec3 => u (y, z.2))
      (fderiv ℝ (fun y : Vec3 => u (y, z.2)) z.1) z.1 :=
    (differentiableAt_spatialSlice hu hz).hasFDerivAt
  have hM : HasFDerivAt (fun y : Vec3 => u (y, z.2))
      (fderiv ℝ (fun y : Vec3 => u (y, z.2)) (rotZ φ z.1)) (rotZ φ z.1) :=
    (differentiableAt_spatialSlice hu hz').hasFDerivAt
  have hA : HasFDerivAt (fun y : Vec3 => rotZ φ y) (rotZEquiv φ).toContinuousLinearMap z.1 :=
    (rotZEquiv φ).toContinuousLinearMap.hasFDerivAt
  have hA' : HasFDerivAt (fun y : Vec3 => rotZ φ y) (rotZEquiv φ).toContinuousLinearMap
      (u (z.1, z.2)) := (rotZEquiv φ).toContinuousLinearMap.hasFDerivAt
  have hcomp := hM.comp z.1 hA
  have hR := hA'.comp z.1 hL
  have hev : (fun y : Vec3 => rotZ φ (u (y, z.2))) =ᶠ[nhds z.1]
      fun y : Vec3 => u (rotZ φ y, z.2) := by
    filter_upwards [(isOpen_vec3Ball 0 1).mem_nhds hz.1] with y hy
    exact (h.apply_rotZ (z := (y, z.2)) φ ⟨hy, hz.2⟩).symm
  have huniq := (hcomp.congr_of_eventuallyEq hev).unique hR
  exact DFunLike.congr_fun huniq w

/-! ### The axis and the reflection of the meridional plane -/

/-- The rotation by `π` fixes the points of the vertical axis. -/
theorem rotZ_pi_of_axis {x : Vec3} (h0 : x 0 = 0) (h1 : x 1 = 0) : rotZ Real.pi x = x := by
  ext i
  fin_cases i <;> simp [rotZ, h0, h1]

/-- The rotation by `π` is the reflection `(x₁, 0, x₃) ↦ (-x₁, 0, x₃)` of the meridional
plane. -/
theorem rotZ_pi_meridional (x₁ x₃ : ℝ) :
    rotZ Real.pi (meridional x₁ x₃) = meridional (-x₁) x₃ := by
  ext i
  fin_cases i <;> simp [rotZ, meridional]

/-- The radial component of an axisymmetric field vanishes on the axis (standing assumptions
of Section `sec:aniso:equations`). -/
theorem apply_axis_zero {u : ParabolicPoint → Vec3} (h : IsAxisymmetricOn u unitCylinder)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (h0 : z.1 0 = 0) (h1 : z.1 1 = 0) :
    u z 0 = 0 := by
  have key := h.apply_rotZ Real.pi hz
  rw [rotZ_pi_of_axis h0 h1] at key
  have key' : u z = rotZ Real.pi (u z) := key
  have hcomp := congrFun key' 0
  rw [rotZ_apply_zero, Real.cos_pi, Real.sin_pi] at hcomp
  linarith only [hcomp]

/-- The swirl of an axisymmetric field vanishes on the axis (standing assumptions of Section
`sec:aniso:equations`). -/
theorem apply_axis_one {u : ParabolicPoint → Vec3} (h : IsAxisymmetricOn u unitCylinder)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (h0 : z.1 0 = 0) (h1 : z.1 1 = 0) :
    u z 1 = 0 := by
  have key := h.apply_rotZ Real.pi hz
  rw [rotZ_pi_of_axis h0 h1] at key
  have key' : u z = rotZ Real.pi (u z) := key
  have hcomp := congrFun key' 1
  rw [rotZ_apply_one, Real.cos_pi, Real.sin_pi] at hcomp
  linarith only [hcomp]

/-- The rotation by `π` reverses the first basis vector. -/
theorem rotZ_pi_basisVec_zero : rotZ Real.pi (basisVec 0) = -(basisVec 0 : Vec3) := by
  ext i
  fin_cases i <;> simp [rotZ, basisVec_apply]

/-- The rotation by `π` reverses the second basis vector. -/
theorem rotZ_pi_basisVec_one : rotZ Real.pi (basisVec 1) = -(basisVec 1 : Vec3) := by
  ext i
  fin_cases i <;> simp [rotZ, basisVec_apply]

/-- The rotation by `π` fixes the vertical basis vector. -/
theorem rotZ_pi_basisVec_two : rotZ Real.pi (basisVec 2) = (basisVec 2 : Vec3) := by
  ext i
  fin_cases i <;> simp [rotZ, basisVec_apply]

/-- At an axis point the spatial derivative anticommutes with the reflection `Q_π`. -/
theorem fderiv_rotZ_pi_axis {u : ParabolicPoint → Vec3} (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (h0 : z.1 0 = 0) (h1 : z.1 1 = 0) (w : Vec3) :
    fderiv ℝ (fun y : Vec3 => u (y, z.2)) z.1 (rotZ Real.pi w)
      = rotZ Real.pi (fderiv ℝ (fun y : Vec3 => u (y, z.2)) z.1 w) := by
  have key := fderiv_comp_rotZ h hu hz Real.pi w
  rwa [rotZ_pi_of_axis h0 h1] at key

/-- On the axis the radial derivative of the vertical component vanishes: `∂_r u_z = 0`
(standing assumptions of Section `sec:aniso:equations`). -/
theorem spatialPartial_zero_two_axis {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (h0 : z.1 0 = 0) (h1 : z.1 1 = 0) :
    spatialPartial (fun w => u w 2) 0 z = 0 := by
  have key := fderiv_rotZ_pi_axis h hu hz h0 h1 (basisVec 0)
  rw [rotZ_pi_basisVec_zero, map_neg] at key
  have hcomp := congrFun key 2
  rw [rotZ_apply_two, Pi.neg_apply] at hcomp
  rw [spatialPartial_eq_fderiv_apply hu hz 2 0]
  linarith only [hcomp]

/-- On the axis the second Cartesian derivative of the vertical component vanishes
(standing assumptions of Section `sec:aniso:equations`). -/
theorem spatialPartial_one_two_axis {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (h0 : z.1 0 = 0) (h1 : z.1 1 = 0) :
    spatialPartial (fun w => u w 2) 1 z = 0 := by
  have key := fderiv_rotZ_pi_axis h hu hz h0 h1 (basisVec 1)
  rw [rotZ_pi_basisVec_one, map_neg] at key
  have hcomp := congrFun key 2
  rw [rotZ_apply_two, Pi.neg_apply] at hcomp
  rw [spatialPartial_eq_fderiv_apply hu hz 2 1]
  linarith only [hcomp]

/-- On the axis the vertical derivative of the radial component vanishes: `∂_z u_r = 0`
(the paragraph after `eq:aniso:circulation:pde`). -/
theorem spatialPartial_two_zero_axis {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (h0 : z.1 0 = 0) (h1 : z.1 1 = 0) :
    spatialPartial (fun w => u w 0) 2 z = 0 := by
  have key := fderiv_rotZ_pi_axis h hu hz h0 h1 (basisVec 2)
  rw [rotZ_pi_basisVec_two] at key
  have hcomp := congrFun key 0
  rw [rotZ_apply_zero, Real.cos_pi, Real.sin_pi] at hcomp
  rw [spatialPartial_eq_fderiv_apply hu hz 0 2]
  linarith only [hcomp]

/-- On the axis the vertical derivative of the swirl vanishes: `∂_z u_θ = 0`. -/
theorem spatialPartial_two_one_axis {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (h0 : z.1 0 = 0) (h1 : z.1 1 = 0) :
    spatialPartial (fun w => u w 1) 2 z = 0 := by
  have key := fderiv_rotZ_pi_axis h hu hz h0 h1 (basisVec 2)
  rw [rotZ_pi_basisVec_two] at key
  have hcomp := congrFun key 1
  rw [rotZ_apply_one, Real.cos_pi, Real.sin_pi] at hcomp
  rw [spatialPartial_eq_fderiv_apply hu hz 1 2]
  linarith only [hcomp]

/-- Under the reflection of the meridional plane the radial component is odd. -/
theorem apply_meridional_reflect_zero {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder) {x₁ x₃ t : ℝ}
    (hz : ((meridional x₁ x₃ : Vec3), t) ∈ unitCylinder) :
    u (meridional (-x₁) x₃, t) 0 = -u (meridional x₁ x₃, t) 0 := by
  have key : u ((rotZ Real.pi (meridional x₁ x₃) : Vec3), t)
      = rotZ Real.pi (u (meridional x₁ x₃, t)) := h.apply_rotZ Real.pi hz
  rw [rotZ_pi_meridional] at key
  have hcomp := congrFun key 0
  rw [rotZ_apply_zero, Real.cos_pi, Real.sin_pi] at hcomp
  linarith only [hcomp]

/-- Under the reflection of the meridional plane the swirl is odd. -/
theorem apply_meridional_reflect_one {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder) {x₁ x₃ t : ℝ}
    (hz : ((meridional x₁ x₃ : Vec3), t) ∈ unitCylinder) :
    u (meridional (-x₁) x₃, t) 1 = -u (meridional x₁ x₃, t) 1 := by
  have key : u ((rotZ Real.pi (meridional x₁ x₃) : Vec3), t)
      = rotZ Real.pi (u (meridional x₁ x₃, t)) := h.apply_rotZ Real.pi hz
  rw [rotZ_pi_meridional] at key
  have hcomp := congrFun key 1
  rw [rotZ_apply_one, Real.cos_pi, Real.sin_pi] at hcomp
  linarith only [hcomp]

/-- Under the reflection of the meridional plane the vertical component is even. -/
theorem apply_meridional_reflect_two {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder) {x₁ x₃ t : ℝ}
    (hz : ((meridional x₁ x₃ : Vec3), t) ∈ unitCylinder) :
    u (meridional (-x₁) x₃, t) 2 = u (meridional x₁ x₃, t) 2 := by
  have key : u ((rotZ Real.pi (meridional x₁ x₃) : Vec3), t)
      = rotZ Real.pi (u (meridional x₁ x₃, t)) := h.apply_rotZ Real.pi hz
  rw [rotZ_pi_meridional] at key
  exact congrFun key 2

/-- On the meridional plane, off the axis, the second Cartesian partial derivative of a
rotation-invariant scalar vanishes: `∂_θ g = 0` (design note R4). -/
theorem spatialPartial_one_meridional_of_invariant {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => g z) unitCylinder)
    (hinv : ∀ (φ : ℝ) (w : ParabolicPoint), w ∈ unitCylinder → g (rotZ φ w.1, w.2) = g w)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    spatialPartial g 1 z = 0 := by
  have hgen := angularGenerator_of_invariant hg hinv hz
  rw [hplane] at hgen
  have hprod : z.1 0 * spatialPartial g 1 z = 0 := by linear_combination hgen
  exact (mul_eq_zero.1 hprod).resolve_left hr

end CIV
