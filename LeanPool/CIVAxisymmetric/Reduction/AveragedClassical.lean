/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.AngularMeanSmooth
public import LeanPool.CIVAxisymmetric.Identities.Axisymmetric
public import LeanPool.CIVAxisymmetric.Identities.Laplacian
public import LeanPool.CIVAxisymmetric.Statements.IsClassicalSolutionOn
public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import LeanPool.CIVAxisymmetric.Statements.RotField
public import LeanPool.CIVAxisymmetric.Statements.AngularMean
public import LeanPool.CIVAxisymmetric.Statements.AngularMeanScalar
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Rotation covariance and the averaged classical solution (`sec:reduction:core`)

The forced Navier–Stokes system `eq:nse:forced` is covariant under the rigid rotations
`Q_φ` of `CIV.rotZ`: if `(u, p, f)` is a classical solution on the unit cylinder then so is
the rotated triple `(ℛ_φ u, p ∘ Q_φ⁻¹, ℛ_φ f)` (`isClassicalSolutionOn_rotField`). Design
note R8 records the reduction this feeds: since an axisymmetric `u` is fixed by every
`ℛ_φ`, averaging the rotated triples in `φ` over `[0, 2π]` replaces `(u, p, f)` by
`(u, 𝒫p, 𝒫f)`, again a classical solution (`isClassicalSolutionOn_angularMean`), with an
axisymmetric, `C²`-bounded force when the original force was `C²`-bounded
(`forceC2Bounded_angularMean`).
-/

public section

open MeasureTheory Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### The derivative of the rotated field -/

/-- The derivative of `rotField` with respect to the space variable. -/
theorem fderiv_rotField_spatial (φ : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (w : Vec3) :
    fderiv ℝ (fun y : Vec3 => rotField φ u (y, z.2)) z.1 w
      = rotZ φ (fderiv ℝ (fun y : Vec3 => u (y, z.2)) (rotZ (-φ) z.1) (rotZ (-φ) w)) := by
  have hz' : (rotZ (-φ) z.1, z.2) ∈ unitCylinder := rotZ_mem_unitCylinder (-φ) hz
  have hrot'' : HasFDerivAt (fun y : Vec3 => u (y, z.2))
      (fderiv ℝ (fun y : Vec3 => u (y, z.2)) (rotZ (-φ) z.1)) (rotZ (-φ) z.1) :=
    ((contDiffOn_spatialSlice hu hz'.2).differentiableOn one_ne_zero).differentiableAt
      ((isOpen_vec3Ball 0 1).mem_nhds hz'.1) |>.hasFDerivAt
  have h_comp1 : HasFDerivAt (fun y : Vec3 => u (rotZ (-φ) y, z.2))
      ((fderiv ℝ (fun y : Vec3 => u (y, z.2)) (rotZ (-φ) z.1)) ∘L
        (rotZEquiv (-φ)).toContinuousLinearMap) z.1 :=
    hrot''.comp z.1 ((rotZEquiv (-φ)).toContinuousLinearMap.hasFDerivAt (x := z.1))
  have h_rotZ : HasFDerivAt (rotZ φ) (rotZEquiv φ).toContinuousLinearMap
      (u (rotZ (-φ) z.1, z.2)) :=
    (rotZEquiv φ).toContinuousLinearMap.hasFDerivAt
  have h_comp2 : HasFDerivAt (rotZ φ ∘ (fun y : Vec3 => u (rotZ (-φ) y, z.2)))
      ((rotZEquiv φ).toContinuousLinearMap ∘L
        ((fderiv ℝ (fun y : Vec3 => u (y, z.2)) (rotZ (-φ) z.1)) ∘L
          (rotZEquiv (-φ)).toContinuousLinearMap)) z.1 :=
    h_rotZ.comp z.1 h_comp1
  have h_eq : (fun y : Vec3 => rotField φ u (y, z.2)) = rotZ φ ∘ (fun y : Vec3 => u (rotZ (-φ)
    y, z.2)) := by
    ext y; rfl
  rw [h_eq]
  have hfderiv := h_comp2.fderiv
  have := DFunLike.congr_fun hfderiv w
  simpa [ContinuousLinearMap.comp_apply] using this

/-- `rotField` at a fixed angle is `C¹` on the unit cylinder whenever `u` is. -/
theorem contDiffOn_rotField (φ : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => rotField φ u z) unitCylinder := by
  have h1 : ContDiffOn ℝ 1 (fun p : ℝ × (Vec3 × ℝ) => rotField p.1 u p.2) (univ ×ˢ unitCylinder) :=
    contDiffOn_rotField_uncurry 1 hu
  have h2 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => (φ, z)) unitCylinder :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have h3 : MapsTo (fun z : Vec3 × ℝ => (φ, z)) unitCylinder (univ ×ˢ unitCylinder) :=
    fun w hw => ⟨mem_univ _, hw⟩
  have h4 := h1.comp h2 h3
  exact h4

/-- The derivative with respect to the space variable of a scalar field composed with a
rotation of the point. -/
private theorem fderiv_comp_rotZ_scalar (ψ : ℝ) (g : ParabolicPoint → ℝ) (t : ℝ) (x w : Vec3) :
    fderiv ℝ (fun y : Vec3 => g (rotZ ψ y, t)) x w
      = fderiv ℝ (fun y : Vec3 => g (y, t)) (rotZ ψ x) (rotZ ψ w) := by
  have hh : (fun y : Vec3 => g (rotZ ψ y, t)) = (fun y : Vec3 => g (y, t)) ∘ (rotZEquiv ψ) := rfl
  rw [hh, ContinuousLinearEquiv.comp_right_fderiv]
  rfl

/-- The spatial partial derivative of a scalar field composed with a rotation of the point
is the corresponding partial derivative of the field at the rotated point, in the rotated
direction. Unconditional: no regularity hypothesis on `g` is needed. -/
theorem spatialPartial_comp_rotZ (ψ : ℝ) (g : ParabolicPoint → ℝ) (z : ParabolicPoint) (i : Fin 3) :
    spatialPartial (fun w => g (rotZ ψ w.1, w.2)) i z
      = fderiv ℝ (fun y : Vec3 => g (y, z.2)) (rotZ ψ z.1) (rotZ ψ (basisVec i)) :=
  fderiv_comp_rotZ_scalar ψ g z.2 z.1 (basisVec i)

/-! ### The time derivative of the rotated field -/

/-- The time slice of a `C¹` field is differentiable in time. -/
private theorem differentiableAt_timeSlice {v : ParabolicPoint → Vec3}
    (hv : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => v z) unitCylinder) {x : Vec3} {t : ℝ}
    (hxt : (x, t) ∈ unitCylinder) :
    DifferentiableAt ℝ (fun s : ℝ => v (x, s)) t := by
  have hcont : ContDiffOn ℝ 1 (fun s : ℝ => v (x, s)) (Ioo (-1 : ℝ) 0) :=
    hv.comp ((contDiff_const.prodMk contDiff_id).contDiffOn) (fun s hs => ⟨hxt.1, hs⟩)
  exact (hcont.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hxt.2)

/-- The time derivative of a component is the corresponding component of the time
derivative of the field. -/
private theorem fderiv_timeSlice_apply {v : ParabolicPoint → Vec3}
    (hv : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => v z) unitCylinder) {x : Vec3} {t : ℝ}
    (hxt : (x, t) ∈ unitCylinder) (i : Fin 3) :
    fderiv ℝ (fun s : ℝ => v (x, s) i) t 1 = fderiv ℝ (fun s : ℝ => v (x, s)) t 1 i := by
  have hF := (differentiableAt_timeSlice hv hxt).hasFDerivAt
  exact DFunLike.congr_fun (hasFDerivAt_pi'.1 hF i).fderiv 1

/-- The time derivative of `rotField`, as a vector identity. Unconditional in the sense
that the composition with the outer rotation `rotZ φ` needs no regularity of `u`; the
regularity is used only to identify the two sides with genuine time partials. -/
private theorem fderiv_rotField_time (φ : ℝ) (u : ParabolicPoint → Vec3) (x : Vec3) (t : ℝ) :
    fderiv ℝ (fun s : ℝ => rotField φ u (x, s)) t 1
      = rotZ φ (fderiv ℝ (fun s : ℝ => u (rotZ (-φ) x, s)) t 1) := by
  have hh : (fun s : ℝ => rotField φ u (x, s))
      = (rotZEquiv φ) ∘ (fun s : ℝ => u (rotZ (-φ) x, s)) := rfl
  rw [hh, ContinuousLinearEquiv.comp_fderiv]
  rfl

/-- The time derivative of `rotField`, component `0`. -/
theorem timePartial_rotField_zero (φ : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    timePartial (fun w => rotField φ u w 0) z =
      Real.cos φ * timePartial (fun w => u w 0) (rotZ (-φ) z.1, z.2) -
      Real.sin φ * timePartial (fun w => u w 1) (rotZ (-φ) z.1, z.2) := by
  have hrot : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => rotField φ u z) unitCylinder :=
    contDiffOn_rotField φ u hu
  have hz' : (rotZ (-φ) z.1, z.2) ∈ unitCylinder := rotZ_mem_unitCylinder (-φ) hz
  change fderiv ℝ (fun s : ℝ => rotField φ u (z.1, s) 0) z.2 1 = _
  rw [fderiv_timeSlice_apply hrot hz 0, fderiv_rotField_time φ u z.1 z.2, rotZ_apply_zero,
    ← fderiv_timeSlice_apply hu hz' 0, ← fderiv_timeSlice_apply hu hz' 1]
  rfl

/-- The time derivative of `rotField`, component `1`. -/
theorem timePartial_rotField_one (φ : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    timePartial (fun w => rotField φ u w 1) z =
      Real.sin φ * timePartial (fun w => u w 0) (rotZ (-φ) z.1, z.2) +
      Real.cos φ * timePartial (fun w => u w 1) (rotZ (-φ) z.1, z.2) := by
  have hrot : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => rotField φ u z) unitCylinder :=
    contDiffOn_rotField φ u hu
  have hz' : (rotZ (-φ) z.1, z.2) ∈ unitCylinder := rotZ_mem_unitCylinder (-φ) hz
  change fderiv ℝ (fun s : ℝ => rotField φ u (z.1, s) 1) z.2 1 = _
  rw [fderiv_timeSlice_apply hrot hz 1, fderiv_rotField_time φ u z.1 z.2, rotZ_apply_one,
    ← fderiv_timeSlice_apply hu hz' 0, ← fderiv_timeSlice_apply hu hz' 1]
  rfl

/-- The time derivative of `rotField`, component `2`. -/
theorem timePartial_rotField_two (φ : ℝ) (u : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    timePartial (fun w => rotField φ u w 2) z =
      timePartial (fun w => u w 2) (rotZ (-φ) z.1, z.2) := rfl

/-! ### The spatial derivatives of the rotated field -/

/-- A spatial partial derivative of `rotField`, component `0`. -/
theorem spatialPartial_rotField_zero (φ : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (j : Fin 3) :
    spatialPartial (fun w => rotField φ u w 0) j z =
      Real.cos φ * fderiv ℝ (fun y : Vec3 => u (y, z.2) 0) (rotZ (-φ) z.1) (rotZ (-φ) (basisVec
        j)) -
      Real.sin φ * fderiv ℝ (fun y : Vec3 => u (y, z.2) 1) (rotZ (-φ) z.1) (rotZ (-φ) (basisVec
        j)) := by
  have hrot : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => rotField φ u z) unitCylinder :=
    contDiffOn_rotField φ u hu
  have hz' : (rotZ (-φ) z.1, z.2) ∈ unitCylinder := rotZ_mem_unitCylinder (-φ) hz
  change fderiv ℝ (fun y : Vec3 => rotField φ u (y, z.2) 0) z.1 (basisVec j) = _
  rw [fderiv_spatialSlice_apply hrot hz 0 (basisVec j), fderiv_rotField_spatial φ u hu hz
    (basisVec j),
    rotZ_apply_zero, ← fderiv_spatialSlice_apply hu hz' 0 (rotZ (-φ) (basisVec j)),
    ← fderiv_spatialSlice_apply hu hz' 1 (rotZ (-φ) (basisVec j))]

/-- A spatial partial derivative of `rotField`, component `1`. -/
theorem spatialPartial_rotField_one (φ : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (j : Fin 3) :
    spatialPartial (fun w => rotField φ u w 1) j z =
      Real.sin φ * fderiv ℝ (fun y : Vec3 => u (y, z.2) 0) (rotZ (-φ) z.1) (rotZ (-φ) (basisVec
        j)) +
      Real.cos φ * fderiv ℝ (fun y : Vec3 => u (y, z.2) 1) (rotZ (-φ) z.1) (rotZ (-φ) (basisVec
        j)) := by
  have hrot : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => rotField φ u z) unitCylinder :=
    contDiffOn_rotField φ u hu
  have hz' : (rotZ (-φ) z.1, z.2) ∈ unitCylinder := rotZ_mem_unitCylinder (-φ) hz
  change fderiv ℝ (fun y : Vec3 => rotField φ u (y, z.2) 1) z.1 (basisVec j) = _
  rw [fderiv_spatialSlice_apply hrot hz 1 (basisVec j), fderiv_rotField_spatial φ u hu hz
    (basisVec j),
    rotZ_apply_one, ← fderiv_spatialSlice_apply hu hz' 0 (rotZ (-φ) (basisVec j)),
    ← fderiv_spatialSlice_apply hu hz' 1 (rotZ (-φ) (basisVec j))]

/-- A spatial partial derivative of `rotField`, component `2`. -/
theorem spatialPartial_rotField_two (φ : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (j : Fin 3) :
    spatialPartial (fun w => rotField φ u w 2) j z =
      fderiv ℝ (fun y : Vec3 => u (y, z.2) 2) (rotZ (-φ) z.1) (rotZ (-φ) (basisVec j)) := by
  have hrot : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => rotField φ u z) unitCylinder :=
    contDiffOn_rotField φ u hu
  have hz' : (rotZ (-φ) z.1, z.2) ∈ unitCylinder := rotZ_mem_unitCylinder (-φ) hz
  change fderiv ℝ (fun y : Vec3 => rotField φ u (y, z.2) 2) z.1 (basisVec j) = _
  rw [fderiv_spatialSlice_apply hrot hz 2 (basisVec j), fderiv_rotField_spatial φ u hu hz
    (basisVec j),
    rotZ_apply_two, ← fderiv_spatialSlice_apply hu hz' 2 (rotZ (-φ) (basisVec j))]

/-! ### The Laplacian of a rotated scalar field -/

/-- The unconditional chain-rule identity behind Laplacian invariance: the once-more
differentiated derivative of a scalar field composed with a rotation, in a fixed direction
`w`, is again a composition with the rotation. -/
private theorem fderiv_fderiv_comp_rotZ (ψ : ℝ) (g : ParabolicPoint → ℝ) (t : ℝ) (x v w : Vec3) :
    fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun y' : Vec3 => g (rotZ ψ y', t)) y w) x v
      = fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun y' : Vec3 => g (y', t)) y (rotZ ψ w))
          (rotZ ψ x) (rotZ ψ v) := by
  have hstep : (fun y : Vec3 => fderiv ℝ (fun y' : Vec3 => g (rotZ ψ y', t)) y w)
      = (fun y : Vec3 => fderiv ℝ (fun y' : Vec3 => g (y', t)) y (rotZ ψ w)) ∘ (rotZEquiv ψ) := by
    funext y
    have hh : (fun y' : Vec3 => g (rotZ ψ y', t)) = (fun y' : Vec3 => g (y', t)) ∘ (rotZEquiv ψ)
      := rfl
    rw [hh, ContinuousLinearEquiv.comp_right_fderiv]
    rfl
  rw [hstep, ContinuousLinearEquiv.comp_right_fderiv]
  rfl

/-- Differentiability, at a general fixed direction `w` (not necessarily a basis vector), of
the once-differentiated slice of a `C²` field. -/
theorem differentiableAt_fderiv_slice {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => g z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (w : Vec3) :
    DifferentiableAt ℝ (fun y : Vec3 => fderiv ℝ (fun y' : Vec3 => g (y', z.2)) y w) z.1 := by
  have hw : w = ∑ a : Fin 3, w a • basisVec a := (sum_smul_basisVec w).symm
  have heq : (fun y : Vec3 => fderiv ℝ (fun y' : Vec3 => g (y', z.2)) y w)
      = fun y => ∑ a : Fin 3, w a * fderiv ℝ (fun y' : Vec3 => g (y', z.2)) y (basisVec a) := by
    funext y
    conv_lhs => rw [hw]
    rw [map_sum]
    simp [smul_eq_mul]
  rw [heq]
  refine DifferentiableAt.fun_sum (fun a _ => ?_)
  exact (differentiableAt_spatialPartial_slice hg hz a).const_mul (w a)

/-- The second directional derivative of a `C²` scalar field, in directions `v` (outer) and
`w` (inner). Diagonal values at basis vectors recover `spatialSecondPartial`
(`hessAt_eq_spatialSecondPartial`). -/
@[expose] def hessAt (g : ParabolicPoint → ℝ) (t : ℝ) (x v w : Vec3) : ℝ :=
  fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun y' : Vec3 => g (y', t)) y w) x v

private theorem hessAt_eq_spatialSecondPartial (g : ParabolicPoint → ℝ) (z : ParabolicPoint)
    (i j : Fin 3) : spatialSecondPartial g i j z = hessAt g z.2 z.1 (basisVec j) (basisVec i) := rfl

theorem hessAt_add_left (g : ParabolicPoint → ℝ) (t : ℝ) (x v1 v2 w : Vec3) :
    hessAt g t x (v1 + v2) w = hessAt g t x v1 w + hessAt g t x v2 w := by
  change fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun y' : Vec3 => g (y', t)) y w) x (v1 + v2) = _
  rw [map_add]; rfl

theorem hessAt_smul_left (g : ParabolicPoint → ℝ) (t : ℝ) (x : Vec3) (c : ℝ) (v w : Vec3) :
    hessAt g t x (c • v) w = c * hessAt g t x v w := by
  change fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun y' : Vec3 => g (y', t)) y w) x (c • v) = _
  rw [map_smul, smul_eq_mul]; rfl

theorem hessAt_add_right {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => g z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (v w1 w2 : Vec3) :
    hessAt g z.2 z.1 v (w1 + w2) = hessAt g z.2 z.1 v w1 + hessAt g z.2 z.1 v w2 := by
  have h1 := differentiableAt_fderiv_slice hg hz w1
  have h2 := differentiableAt_fderiv_slice hg hz w2
  have hcomb : (fun y : Vec3 => fderiv ℝ (fun y' : Vec3 => g (y', z.2)) y (w1 + w2))
      = (fun y => fderiv ℝ (fun y' : Vec3 => g (y', z.2)) y w1)
        + (fun y => fderiv ℝ (fun y' : Vec3 => g (y', z.2)) y w2) := by
    funext y; simp [map_add]
  change fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun y' : Vec3 => g (y', z.2)) y (w1 + w2)) z.1 v = _
  rw [hcomb, fderiv_add h1 h2]; rfl

theorem hessAt_const_mul_right {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => g z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (v : Vec3) (c : ℝ) (w : Vec3) :
    hessAt g z.2 z.1 v (c • w) = c * hessAt g z.2 z.1 v w := by
  have h1 := differentiableAt_fderiv_slice hg hz w
  have hcomb : (fun y : Vec3 => fderiv ℝ (fun y' : Vec3 => g (y', z.2)) y (c • w))
      = c • (fun y => fderiv ℝ (fun y' : Vec3 => g (y', z.2)) y w) := by
    funext y; simp [map_smul]
  change fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun y' : Vec3 => g (y', z.2)) y (c • w)) z.1 v = _
  rw [hcomb, fderiv_const_smul h1]; rfl

theorem hessAt_comp_rotZ (ψ : ℝ) (g : ParabolicPoint → ℝ) (z : ParabolicPoint) (v w : Vec3) :
    hessAt (fun w' => g (rotZ ψ w'.1, w'.2)) z.2 z.1 v w
      = hessAt g z.2 (rotZ ψ z.1) (rotZ ψ v) (rotZ ψ w) := by
  change fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun y' : Vec3 => g (rotZ ψ y', z.2)) y w) z.1 v = _
  rw [fderiv_fderiv_comp_rotZ]
  rfl

/-- Trace invariance of the `hessAt` diagonal under an orthogonal change of variables: the
rotated basis directions, expanded through bilinearity, contribute only their diagonal
part, by `Real.cos_sq_add_sin_sq`. -/
private theorem sum_hessAt_rotZ_diag {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => g z) unitCylinder) (ψ : ℝ) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    ∑ j : Fin 3, hessAt g z.2 (rotZ ψ z.1) (rotZ ψ (basisVec j)) (rotZ ψ (basisVec j))
      = ∑ a : Fin 3, hessAt g z.2 (rotZ ψ z.1) (basisVec a) (basisVec a) := by
  have hz' : (rotZ ψ z.1, z.2) ∈ unitCylinder := rotZ_mem_unitCylinder ψ hz
  have hadd_r := fun (v : Vec3) => hessAt_add_right hg hz' v
  have hmul_r := fun (v : Vec3) => hessAt_const_mul_right hg hz' v
  have hadd_l := hessAt_add_left g z.2 (rotZ ψ z.1)
  have hmul_l := hessAt_smul_left g z.2 (rotZ ψ z.1)
  have h0 : rotZ ψ (basisVec 0) = Real.cos ψ • basisVec 0 + Real.sin ψ • basisVec 1 := by
    ext i; fin_cases i <;> simp [rotZ, basisVec_apply]
  have h1 : rotZ ψ (basisVec 1) = (-Real.sin ψ) • basisVec 0 + Real.cos ψ • basisVec 1 := by
    ext i; fin_cases i <;> simp [rotZ, basisVec_apply]
  have h2 : rotZ ψ (basisVec 2) = basisVec 2 := by
    ext i; fin_cases i <;> simp [rotZ, basisVec_apply]
  rw [Fin.sum_univ_three, h0, h1, h2]
  simp only [hadd_l, hmul_l, hadd_r, hmul_r]
  rw [Fin.sum_univ_three]
  have htrig := Real.cos_sq_add_sin_sq ψ
  linear_combination (hessAt g z.2 (rotZ ψ z.1) (basisVec 0) (basisVec 0)
    + hessAt g z.2 (rotZ ψ z.1) (basisVec 1) (basisVec 1)) * htrig

/-- The Laplacian (sum of second Cartesian partial derivatives) of a `C²` scalar field
composed with a rotation of the point is the Laplacian of the field at the rotated point:
the trace of the Hessian is invariant under the orthogonal map `rotZ`. -/
theorem sum_spatialSecondPartial_comp_rotZ {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => g z) unitCylinder) (ψ : ℝ) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    ∑ j : Fin 3, spatialSecondPartial (fun w => g (rotZ ψ w.1, w.2)) j j z
      = ∑ a : Fin 3, spatialSecondPartial g a a (rotZ ψ z.1, z.2) := by
  have hstep : ∀ j : Fin 3, spatialSecondPartial (fun w => g (rotZ ψ w.1, w.2)) j j z
      = hessAt g z.2 (rotZ ψ z.1) (rotZ ψ (basisVec j)) (rotZ ψ (basisVec j)) := by
    intro j
    rw [hessAt_eq_spatialSecondPartial, hessAt_comp_rotZ]
  have hfin : ∀ a : Fin 3, spatialSecondPartial g a a (rotZ ψ z.1, z.2)
      = hessAt g z.2 (rotZ ψ z.1) (basisVec a) (basisVec a) :=
    fun a => hessAt_eq_spatialSecondPartial g (rotZ ψ z.1, z.2) a a
  simp_rw [hstep, hfin]
  exact sum_hessAt_rotZ_diag hg ψ hz

/-- `spatialSecondPartial` is a constant-coefficient linear combination in its function
argument. -/
private theorem spatialSecondPartial_combo {f g : ParabolicPoint → ℝ} (c d : ℝ)
    (hf : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hg : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => g z) unitCylinder)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (j : Fin 3) :
    spatialSecondPartial (fun w => c * f w - d * g w) j j z =
      c * spatialSecondPartial f j j z - d * spatialSecondPartial g j j z := by
  have hf1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => f z) unitCylinder := hf.of_le (by norm_num)
  have hg1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => g z) unitCylinder := hg.of_le (by norm_num)
  have hpt : ∀ y ∈ vec3Ball 0 1, spatialPartial (fun w => c * f w - d * g w) j (y, z.2)
      = c * spatialPartial f j (y, z.2) - d * spatialPartial g j (y, z.2) := by
    intro y hy
    have hyz : (y, z.2) ∈ unitCylinder := ⟨hy, hz.2⟩
    have hfD : DifferentiableAt ℝ (fun x : Vec3 => f (x, z.2)) y :=
      differentiableAt_spatialSlice hf1 hyz
    have hgD : DifferentiableAt ℝ (fun x : Vec3 => g (x, z.2)) y :=
      differentiableAt_spatialSlice hg1 hyz
    change fderiv ℝ (fun x : Vec3 => c * f (x, z.2) - d * g (x, z.2)) y (basisVec j) = _
    rw [fderiv_fun_sub (hfD.const_mul c) (hgD.const_mul d), fderiv_const_mul hfD,
      fderiv_const_mul hgD]
    rfl
  have hev : (fun y : Vec3 => spatialPartial (fun w => c * f w - d * g w) j (y, z.2))
      =ᶠ[nhds z.1] (fun y : Vec3 => c * spatialPartial f j (y, z.2) - d * spatialPartial g j (y,
        z.2)) := by
    filter_upwards [(isOpen_vec3Ball 0 1).mem_nhds hz.1] with y hy using hpt y hy
  have hfD2 := differentiableAt_spatialPartial_slice hf hz j
  have hgD2 := differentiableAt_spatialPartial_slice hg hz j
  change fderiv ℝ (fun y : Vec3 => spatialPartial (fun w => c * f w - d * g w) j (y, z.2)) z.1
    (basisVec j) = _
  rw [hev.fderiv_eq, fderiv_fun_sub (hfD2.const_mul c) (hgD2.const_mul d), fderiv_const_mul hfD2,
    fderiv_const_mul hgD2]
  rfl

/-- `spatialSecondPartial` is a constant-coefficient linear combination in its function
argument, the addition form. -/
private theorem spatialSecondPartial_combo_add {f g : ParabolicPoint → ℝ} (c d : ℝ)
    (hf : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hg : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => g z) unitCylinder)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (j : Fin 3) :
    spatialSecondPartial (fun w => c * f w + d * g w) j j z =
      c * spatialSecondPartial f j j z + d * spatialSecondPartial g j j z := by
  have hf1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => f z) unitCylinder := hf.of_le (by norm_num)
  have hg1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => g z) unitCylinder := hg.of_le (by norm_num)
  have hpt : ∀ y ∈ vec3Ball 0 1, spatialPartial (fun w => c * f w + d * g w) j (y, z.2)
      = c * spatialPartial f j (y, z.2) + d * spatialPartial g j (y, z.2) := by
    intro y hy
    have hyz : (y, z.2) ∈ unitCylinder := ⟨hy, hz.2⟩
    have hfD : DifferentiableAt ℝ (fun x : Vec3 => f (x, z.2)) y :=
      differentiableAt_spatialSlice hf1 hyz
    have hgD : DifferentiableAt ℝ (fun x : Vec3 => g (x, z.2)) y :=
      differentiableAt_spatialSlice hg1 hyz
    change fderiv ℝ (fun x : Vec3 => c * f (x, z.2) + d * g (x, z.2)) y (basisVec j) = _
    rw [fderiv_fun_add (hfD.const_mul c) (hgD.const_mul d), fderiv_const_mul hfD,
      fderiv_const_mul hgD]
    rfl
  have hev : (fun y : Vec3 => spatialPartial (fun w => c * f w + d * g w) j (y, z.2))
      =ᶠ[nhds z.1] (fun y : Vec3 => c * spatialPartial f j (y, z.2) + d * spatialPartial g j (y,
        z.2)) := by
    filter_upwards [(isOpen_vec3Ball 0 1).mem_nhds hz.1] with y hy using hpt y hy
  have hfD2 := differentiableAt_spatialPartial_slice hf hz j
  have hgD2 := differentiableAt_spatialPartial_slice hg hz j
  change fderiv ℝ (fun y : Vec3 => spatialPartial (fun w => c * f w + d * g w) j (y, z.2)) z.1
    (basisVec j) = _
  rw [hev.fderiv_eq, fderiv_fun_add (hfD2.const_mul c) (hgD2.const_mul d), fderiv_const_mul hfD2,
    fderiv_const_mul hgD2]
  rfl

/-- `ContDiffOn` of a component of `u` composed with a rotation of the point. -/
theorem contDiffOn_component_comp_rotZ (ψ : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) (k : Fin 3) :
    ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u (rotZ ψ z.1, z.2) k) unitCylinder := by
  have h1 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z k) unitCylinder := contDiffOn_component hu k
  have ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => rotZ ψ z.1) unitCylinder :=
    ((contDiff_rotZ_smooth ψ).comp contDiff_fst).contDiffOn
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => z.2) unitCylinder := contDiffOn_snd
  have h2top : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => (rotZ ψ z.1, z.2)) unitCylinder :=
    ha.prodMk hb
  have h2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => (rotZ ψ z.1, z.2)) unitCylinder := h2top.of_le
    (by norm_num)
  have hmaps : MapsTo (fun z : Vec3 × ℝ => (rotZ ψ z.1, z.2)) unitCylinder unitCylinder :=
    fun w hw => rotZ_mem_unitCylinder ψ hw
  have h3 := h1.comp h2 hmaps
  exact h3

/-- The Laplacian of `rotField φ u`, component `0`. -/
private theorem sumSecondPartial_rotField_zero (φ : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    ∑ j : Fin 3, spatialSecondPartial (fun w => rotField φ u w 0) j j z =
      Real.cos φ * ∑ a : Fin 3, spatialSecondPartial (fun w => u w 0) a a (rotZ (-φ) z.1, z.2) -
      Real.sin φ * ∑ a : Fin 3, spatialSecondPartial (fun w => u w 1) a a (rotZ (-φ) z.1, z.2) := by
  have hu0 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z 0) unitCylinder := contDiffOn_component hu 0
  have hu1 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z 1) unitCylinder := contDiffOn_component hu 1
  have hrot0 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u (rotZ (-φ) z.1, z.2) 0) unitCylinder :=
    contDiffOn_component_comp_rotZ (-φ) u hu 0
  have hrot1 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u (rotZ (-φ) z.1, z.2) 1) unitCylinder :=
    contDiffOn_component_comp_rotZ (-φ) u hu 1
  have hcombo : ∀ j : Fin 3, spatialSecondPartial (fun w => rotField φ u w 0) j j z
      = Real.cos φ * spatialSecondPartial (fun w => u (rotZ (-φ) w.1, w.2) 0) j j z
        - Real.sin φ * spatialSecondPartial (fun w => u (rotZ (-φ) w.1, w.2) 1) j j z := by
    intro j
    change spatialSecondPartial
      (fun w => Real.cos φ * u (rotZ (-φ) w.1, w.2) 0 - Real.sin φ * u (rotZ (-φ) w.1, w.2) 1) j
        j z = _
    exact spatialSecondPartial_combo (Real.cos φ) (Real.sin φ) hrot0 hrot1 hz j
  calc ∑ j : Fin 3, spatialSecondPartial (fun w => rotField φ u w 0) j j z
      = ∑ j : Fin 3, (Real.cos φ * spatialSecondPartial (fun w => u (rotZ (-φ) w.1, w.2) 0) j j z
          - Real.sin φ * spatialSecondPartial (fun w => u (rotZ (-φ) w.1, w.2) 1) j j z) :=
        Finset.sum_congr rfl (fun j _ => hcombo j)
    _ = Real.cos φ * ∑ j : Fin 3, spatialSecondPartial (fun w => u (rotZ (-φ) w.1, w.2) 0) j j z
        - Real.sin φ * ∑ j : Fin 3, spatialSecondPartial (fun w => u (rotZ (-φ) w.1, w.2) 1) j j
          z := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = Real.cos φ * ∑ a : Fin 3, spatialSecondPartial (fun w => u w 0) a a (rotZ (-φ) z.1, z.2)
        - Real.sin φ * ∑ a : Fin 3, spatialSecondPartial (fun w => u w 1) a a (rotZ (-φ) z.1,
          z.2) := by
        rw [sum_spatialSecondPartial_comp_rotZ hu0 (-φ) hz, sum_spatialSecondPartial_comp_rotZ
          hu1 (-φ) hz]
        rfl

/-- The Laplacian of `rotField φ u`, component `1`. -/
private theorem sumSecondPartial_rotField_one (φ : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    ∑ j : Fin 3, spatialSecondPartial (fun w => rotField φ u w 1) j j z =
      Real.sin φ * ∑ a : Fin 3, spatialSecondPartial (fun w => u w 0) a a (rotZ (-φ) z.1, z.2) +
      Real.cos φ * ∑ a : Fin 3, spatialSecondPartial (fun w => u w 1) a a (rotZ (-φ) z.1, z.2) := by
  have hu0 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z 0) unitCylinder := contDiffOn_component hu 0
  have hu1 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z 1) unitCylinder := contDiffOn_component hu 1
  have hrot0 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u (rotZ (-φ) z.1, z.2) 0) unitCylinder :=
    contDiffOn_component_comp_rotZ (-φ) u hu 0
  have hrot1 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u (rotZ (-φ) z.1, z.2) 1) unitCylinder :=
    contDiffOn_component_comp_rotZ (-φ) u hu 1
  have hcombo : ∀ j : Fin 3, spatialSecondPartial (fun w => rotField φ u w 1) j j z
      = Real.sin φ * spatialSecondPartial (fun w => u (rotZ (-φ) w.1, w.2) 0) j j z
        + Real.cos φ * spatialSecondPartial (fun w => u (rotZ (-φ) w.1, w.2) 1) j j z := by
    intro j
    change spatialSecondPartial
      (fun w => Real.sin φ * u (rotZ (-φ) w.1, w.2) 0 + Real.cos φ * u (rotZ (-φ) w.1, w.2) 1) j
        j z = _
    exact spatialSecondPartial_combo_add (Real.sin φ) (Real.cos φ) hrot0 hrot1 hz j
  calc ∑ j : Fin 3, spatialSecondPartial (fun w => rotField φ u w 1) j j z
      = ∑ j : Fin 3, (Real.sin φ * spatialSecondPartial (fun w => u (rotZ (-φ) w.1, w.2) 0) j j z
          + Real.cos φ * spatialSecondPartial (fun w => u (rotZ (-φ) w.1, w.2) 1) j j z) :=
        Finset.sum_congr rfl (fun j _ => hcombo j)
    _ = Real.sin φ * ∑ j : Fin 3, spatialSecondPartial (fun w => u (rotZ (-φ) w.1, w.2) 0) j j z
        + Real.cos φ * ∑ j : Fin 3, spatialSecondPartial (fun w => u (rotZ (-φ) w.1, w.2) 1) j j
          z := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = Real.sin φ * ∑ a : Fin 3, spatialSecondPartial (fun w => u w 0) a a (rotZ (-φ) z.1, z.2)
        + Real.cos φ * ∑ a : Fin 3, spatialSecondPartial (fun w => u w 1) a a (rotZ (-φ) z.1,
          z.2) := by
        rw [sum_spatialSecondPartial_comp_rotZ hu0 (-φ) hz, sum_spatialSecondPartial_comp_rotZ
          hu1 (-φ) hz]
        rfl

/-- The Laplacian of `rotField φ u`, component `2`. -/
private theorem sumSecondPartial_rotField_two (φ : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    ∑ j : Fin 3, spatialSecondPartial (fun w => rotField φ u w 2) j j z =
      ∑ a : Fin 3, spatialSecondPartial (fun w => u w 2) a a (rotZ (-φ) z.1, z.2) := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z 2) unitCylinder := contDiffOn_component hu 2
  have hcongr : (fun w => rotField φ u w 2) = (fun w => u (rotZ (-φ) w.1, w.2) 2) := by
    funext w; change rotZ φ (u (rotZ (-φ) w.1, w.2)) 2 = _; rw [rotZ_apply_two]
  rw [hcongr]
  exact sum_spatialSecondPartial_comp_rotZ hu2 (-φ) hz

/-! ### The convective and divergence terms of the rotated system -/

/-- A directional derivative is the sum of the coordinates against the partial derivatives
in the basis directions. -/
private theorem fderiv_eq_sum_basisVec_apply (V : Vec3 → Vec3) (x v : Vec3) (i : Fin 3) :
    fderiv ℝ V x v i = ∑ j : Fin 3, v j * fderiv ℝ V x (basisVec j) i := by
  conv_lhs => rw [← sum_smul_basisVec v]
  rw [map_sum]
  simp [smul_eq_mul]

/-- The derivative of `rotField` at the space point `z.1`, applied to the value
`rotField φ u z` itself: the input rotates back to `u` at the rotated point. -/
private theorem fderiv_rotField_spatial_self (φ : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    fderiv ℝ (fun y : Vec3 => rotField φ u (y, z.2)) z.1 (rotField φ u z)
      = rotZ φ (fderiv ℝ (fun y : Vec3 => u (y, z.2)) (rotZ (-φ) z.1) (u (rotZ (-φ) z.1, z.2)))
        := by
  have heq : rotZ (-φ) (rotField φ u z) = u (rotZ (-φ) z.1, z.2) :=
    rotZ_neg_rotZ φ (u (rotZ (-φ) z.1, z.2))
  rw [fderiv_rotField_spatial φ u hu hz (rotField φ u z), heq]

/-- The convective term of the rotated system: the direction of transport is
`rotField φ u z` itself, and the whole term is the rotation of the convective term of the
original system at the rotated point. -/
private theorem convective_rotField (φ : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i : Fin 3) :
    ∑ j : Fin 3, rotField φ u z j * spatialPartial (fun w => rotField φ u w i) j z
      = (rotZ φ (fderiv ℝ (fun y : Vec3 => u (y, z.2)) (rotZ (-φ) z.1)
          (u (rotZ (-φ) z.1, z.2)))) i := by
  have hrot : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => rotField φ u z) unitCylinder :=
    contDiffOn_rotField φ u hu
  have hstep : ∀ j : Fin 3, spatialPartial (fun w => rotField φ u w i) j z
      = fderiv ℝ (fun y : Vec3 => rotField φ u (y, z.2)) z.1 (basisVec j) i :=
    fun j => fderiv_spatialSlice_apply hrot hz i (basisVec j)
  simp_rw [hstep]
  rw [← fderiv_eq_sum_basisVec_apply (fun y => rotField φ u (y, z.2)) z.1 (rotField φ u z) i,
    fderiv_rotField_spatial_self φ u hu hz]

/-- The trace of a linear self-map of `Vec3`, conjugated by a rotation, equals the trace
itself: divergence is invariant under the orthogonal map `rotZ`. -/
private theorem trace_conj_rotZ (M : Vec3 →L[ℝ] Vec3) (φ : ℝ) :
    ∑ j : Fin 3, (rotZ φ (M (rotZ (-φ) (basisVec j)))) j = ∑ a : Fin 3, M (basisVec a) a := by
  have h0 : rotZ (-φ) (basisVec 0) = Real.cos φ • basisVec 0 + (-Real.sin φ) • basisVec 1 := by
    ext i; fin_cases i <;> simp [rotZ, basisVec_apply]
  have h1 : rotZ (-φ) (basisVec 1) = Real.sin φ • basisVec 0 + Real.cos φ • basisVec 1 := by
    ext i; fin_cases i <;> simp [rotZ, basisVec_apply]
  have h2 : rotZ (-φ) (basisVec 2) = basisVec 2 := by
    ext i; fin_cases i <;> simp [rotZ, basisVec_apply]
  rw [Fin.sum_univ_three, h0, h1, h2]
  simp only [map_add, map_smul, rotZ_apply_zero, rotZ_apply_one, rotZ_apply_two,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_three]
  have htrig := Real.cos_sq_add_sin_sq φ
  linear_combination (M (basisVec 0) 0 + M (basisVec 1) 1) * htrig

/-- The divergence of `rotField φ u` at `z` is the divergence of `u` at the rotated point:
the rotation `rotZ` is orthogonal, so it preserves the trace of the Jacobian. -/
private theorem divergence_rotField (φ : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    ∑ j : Fin 3, spatialPartial (fun w => rotField φ u w j) j z
      = ∑ a : Fin 3, spatialPartial (fun w => u w a) a (rotZ (-φ) z.1, z.2) := by
  have hrot : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => rotField φ u z) unitCylinder :=
    contDiffOn_rotField φ u hu
  have hz' : (rotZ (-φ) z.1, z.2) ∈ unitCylinder := rotZ_mem_unitCylinder (-φ) hz
  have hstep : ∀ j : Fin 3, spatialPartial (fun w => rotField φ u w j) j z
      = (rotZ φ (fderiv ℝ (fun y : Vec3 => u (y, z.2)) (rotZ (-φ) z.1) (rotZ (-φ) (basisVec
        j)))) j := by
    intro j
    change fderiv ℝ (fun y : Vec3 => rotField φ u (y, z.2) j) z.1 (basisVec j) = _
    rw [fderiv_spatialSlice_apply hrot hz j (basisVec j), fderiv_rotField_spatial φ u hu hz
      (basisVec j)]
  simp_rw [hstep]
  rw [trace_conj_rotZ (fderiv ℝ (fun y : Vec3 => u (y, z.2)) (rotZ (-φ) z.1)) φ]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact (fderiv_spatialSlice_apply hu hz' a (basisVec a)).symm

/-- The value at a rotated basis direction of a continuous linear functional is the
corresponding component of the rotation of its values on the basis. -/
private theorem apply_rotZ_neg_basisVec (ψ : ℝ) (Φ : Vec3 →L[ℝ] ℝ) (i : Fin 3) :
    Φ (rotZ (-ψ) (basisVec i)) = rotZ ψ (fun v : Fin 3 => Φ (basisVec v)) i := by
  have h0 : rotZ (-ψ) (basisVec 0) = Real.cos ψ • basisVec 0 + (-Real.sin ψ) • basisVec 1 := by
    ext k; fin_cases k <;> simp [rotZ, basisVec_apply]
  have h1 : rotZ (-ψ) (basisVec 1) = Real.sin ψ • basisVec 0 + Real.cos ψ • basisVec 1 := by
    ext k; fin_cases k <;> simp [rotZ, basisVec_apply]
  have h2 : rotZ (-ψ) (basisVec 2) = basisVec 2 := by
    ext k; fin_cases k <;> simp [rotZ, basisVec_apply]
  fin_cases i <;>
    simp [h0, h1, h2, map_add, map_smul, smul_eq_mul, rotZ_apply_zero, rotZ_apply_one,
      rotZ_apply_two]
  all_goals ring

/-- The pressure gradient term of the rotated system is the rotation of the pressure
gradient of the original system at the rotated point. -/
private theorem gradient_comp_rotZ (φ : ℝ) (p : ParabolicPoint → ℝ) (z : ParabolicPoint) (i :
    Fin 3) :
    fderiv ℝ (fun y : Vec3 => p (y, z.2)) (rotZ (-φ) z.1) (rotZ (-φ) (basisVec i))
      = rotZ φ (fun v : Fin 3 => spatialPartial p v (rotZ (-φ) z.1, z.2)) i :=
  apply_rotZ_neg_basisVec φ (fderiv ℝ (fun y : Vec3 => p (y, z.2)) (rotZ (-φ) z.1)) i

/-- The value at `u z` of the derivative of `u`'s spatial slice is the convective term of
the component `i` of `u` at `z`. -/
private theorem fderiv_apply_eq_convective (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i : Fin 3) :
    fderiv ℝ (fun y : Vec3 => u (y, z.2)) z.1 (u z) i
      = ∑ j : Fin 3, u z j * spatialPartial (fun w => u w i) j z := by
  rw [fderiv_eq_sum_basisVec_apply (fun y => u (y, z.2)) z.1 (u z) i]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  exact (fderiv_spatialSlice_apply hu hz i (basisVec j)).symm

/-- `rotField` at a fixed angle is `C¹` (respectively `C^∞`) on the unit cylinder whenever
`u` is. -/
private theorem contDiffOn_rotField_top (φ : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => rotField φ u z) unitCylinder := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Vec3 × ℝ) => rotField p.1 u p.2) (univ ×ˢ
    unitCylinder) :=
    contDiffOn_rotField_uncurry (⊤ : ℕ∞) hu
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => (φ, z)) unitCylinder :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have h3 : MapsTo (fun z : Vec3 × ℝ => (φ, z)) unitCylinder (univ ×ˢ unitCylinder) :=
    fun w hw => ⟨mem_univ _, hw⟩
  have h4 := h1.comp h2 h3
  exact h4

/-- A scalar field precomposed with the point rotation `Q_{-φ}` is `C^∞` on the unit
cylinder whenever the field is. -/
private theorem contDiffOn_comp_rotZ_scalar_top (φ : ℝ) (p : ParabolicPoint → ℝ)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p (rotZ (-φ) z.1, z.2)) unitCylinder := by
  have ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => rotZ (-φ) z.1) unitCylinder :=
    ((contDiff_rotZ_smooth (-φ)).comp contDiff_fst).contDiffOn
  have hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => z.2) unitCylinder := contDiffOn_snd
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => (rotZ (-φ) z.1, z.2)) unitCylinder :=
    ha.prodMk hb
  have hmaps : MapsTo (fun z : Vec3 × ℝ => (rotZ (-φ) z.1, z.2)) unitCylinder unitCylinder :=
    fun w hw => rotZ_mem_unitCylinder (-φ) hw
  have h3 := hp.comp h2 hmaps
  exact h3

/-! ### Rotation covariance of the Navier–Stokes equations -/

/-- The Navier–Stokes equations are covariant under rigid rotations of the spatial
coordinates (`sec:reduction:core`, design note R8). For any angle `φ`, if `(u, p, f)`
solves the forced Navier–Stokes equations on the unit cylinder, then the rotated triple
`(ℛ_φ u, p ∘ Q_φ⁻¹, ℛ_φ f)` also solves them. -/
theorem isClassicalSolutionOn_rotField (φ : ℝ)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f unitCylinder) :
    IsClassicalSolutionOn (rotField φ u) (fun z => p (rotZ (-φ) z.1, z.2))
      (rotField φ f) unitCylinder := by
  obtain ⟨hu, hp, hf, hmom, hdiv⟩ := hsol
  have hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder := hu.of_le (by norm_num)
  have hu2 : ContDiffOn ℝ 2 (fun w : Vec3 × ℝ => u w) unitCylinder := hu.of_le (by norm_num)
  refine ⟨contDiffOn_rotField_top φ u hu, contDiffOn_comp_rotZ_scalar_top φ p hp,
    contDiffOn_rotField_top φ f hf, ?_, ?_⟩
  · intro z hz i
    have hz' : (rotZ (-φ) z.1, z.2) ∈ unitCylinder := rotZ_mem_unitCylinder (-φ) hz
    fin_cases i
    · have hmom0 := hmom (rotZ (-φ) z.1, z.2) hz' 0
      have hmom1 := hmom (rotZ (-φ) z.1, z.2) hz' 1
      have hT1 := timePartial_rotField_zero φ u hu1 hz
      have hT2 := convective_rotField φ u hu1 hz 0
      have hconv0 : fderiv ℝ (fun y : Vec3 => u (y, z.2)) (rotZ (-φ) z.1) (u (rotZ (-φ) z.1, z.2)) 0
          = ∑ j : Fin 3, u (rotZ (-φ) z.1, z.2) j * spatialPartial (fun w => u w 0) j (rotZ (-φ)
            z.1, z.2) :=
        fderiv_apply_eq_convective u hu1 hz' 0
      have hconv1 : fderiv ℝ (fun y : Vec3 => u (y, z.2)) (rotZ (-φ) z.1) (u (rotZ (-φ) z.1, z.2)) 1
          = ∑ j : Fin 3, u (rotZ (-φ) z.1, z.2) j * spatialPartial (fun w => u w 1) j (rotZ (-φ)
            z.1, z.2) :=
        fderiv_apply_eq_convective u hu1 hz' 1
      have hT3 := sumSecondPartial_rotField_zero φ u hu2 hz
      have hT4 := gradient_comp_rotZ φ p z 0
      change timePartial (fun w => rotField φ u w 0) z +
          ∑ j : Fin 3, rotField φ u z j * spatialPartial (fun w => rotField φ u w 0) j z -
          ∑ j : Fin 3, spatialSecondPartial (fun w => rotField φ u w 0) j j z +
          spatialPartial (fun w => p (rotZ (-φ) w.1, w.2)) 0 z = rotField φ f z 0
      change _ = rotZ φ (f (rotZ (-φ) z.1, z.2)) 0
      rw [hT1, hT2, hT3, spatialPartial_comp_rotZ (-φ) p z 0, hT4,
        rotZ_apply_zero, rotZ_apply_zero, rotZ_apply_zero, hconv0, hconv1]
      linear_combination Real.cos φ * hmom0 - Real.sin φ * hmom1
    · have hmom0 := hmom (rotZ (-φ) z.1, z.2) hz' 0
      have hmom1 := hmom (rotZ (-φ) z.1, z.2) hz' 1
      have hT1 := timePartial_rotField_one φ u hu1 hz
      have hT2 := convective_rotField φ u hu1 hz 1
      have hconv0 : fderiv ℝ (fun y : Vec3 => u (y, z.2)) (rotZ (-φ) z.1) (u (rotZ (-φ) z.1, z.2)) 0
          = ∑ j : Fin 3, u (rotZ (-φ) z.1, z.2) j * spatialPartial (fun w => u w 0) j (rotZ (-φ)
            z.1, z.2) :=
        fderiv_apply_eq_convective u hu1 hz' 0
      have hconv1 : fderiv ℝ (fun y : Vec3 => u (y, z.2)) (rotZ (-φ) z.1) (u (rotZ (-φ) z.1, z.2)) 1
          = ∑ j : Fin 3, u (rotZ (-φ) z.1, z.2) j * spatialPartial (fun w => u w 1) j (rotZ (-φ)
            z.1, z.2) :=
        fderiv_apply_eq_convective u hu1 hz' 1
      have hT3 := sumSecondPartial_rotField_one φ u hu2 hz
      have hT4 := gradient_comp_rotZ φ p z 1
      change timePartial (fun w => rotField φ u w 1) z +
          ∑ j : Fin 3, rotField φ u z j * spatialPartial (fun w => rotField φ u w 1) j z -
          ∑ j : Fin 3, spatialSecondPartial (fun w => rotField φ u w 1) j j z +
          spatialPartial (fun w => p (rotZ (-φ) w.1, w.2)) 1 z = rotField φ f z 1
      change _ = rotZ φ (f (rotZ (-φ) z.1, z.2)) 1
      rw [hT1, hT2, hT3, spatialPartial_comp_rotZ (-φ) p z 1, hT4,
        rotZ_apply_one, rotZ_apply_one, rotZ_apply_one, hconv0, hconv1]
      linear_combination Real.sin φ * hmom0 + Real.cos φ * hmom1
    · have hmom2 := hmom (rotZ (-φ) z.1, z.2) hz' 2
      have hT1 := timePartial_rotField_two φ u z
      have hT2 := convective_rotField φ u hu1 hz 2
      have hconv2 : fderiv ℝ (fun y : Vec3 => u (y, z.2)) (rotZ (-φ) z.1) (u (rotZ (-φ) z.1, z.2)) 2
          = ∑ j : Fin 3, u (rotZ (-φ) z.1, z.2) j * spatialPartial (fun w => u w 2) j (rotZ (-φ)
            z.1, z.2) :=
        fderiv_apply_eq_convective u hu1 hz' 2
      have hT3 := sumSecondPartial_rotField_two φ u hu2 hz
      have hT4 := gradient_comp_rotZ φ p z 2
      change timePartial (fun w => rotField φ u w 2) z +
          ∑ j : Fin 3, rotField φ u z j * spatialPartial (fun w => rotField φ u w 2) j z -
          ∑ j : Fin 3, spatialSecondPartial (fun w => rotField φ u w 2) j j z +
          spatialPartial (fun w => p (rotZ (-φ) w.1, w.2)) 2 z = rotField φ f z 2
      change _ = rotZ φ (f (rotZ (-φ) z.1, z.2)) 2
      rw [hT1, hT2, hT3, spatialPartial_comp_rotZ (-φ) p z 2, hT4,
        rotZ_apply_two, rotZ_apply_two, rotZ_apply_two, hconv2]
      linear_combination hmom2
  · intro z hz
    have hz' : (rotZ (-φ) z.1, z.2) ∈ unitCylinder := rotZ_mem_unitCylinder (-φ) hz
    rw [divergence_rotField φ u hu1 hz]
    exact hdiv (rotZ (-φ) z.1, z.2) hz'

/-! ### The averaged classical solution -/

/-- The integrand of the angular mean of a scalar field is jointly `C^n`. -/
private theorem contDiffOn_angularMeanScalar_integrand (n : WithTop ℕ∞) {p : ParabolicPoint → ℝ}
    (hp : ContDiffOn ℝ n (fun z : Vec3 × ℝ => p z) unitCylinder) :
    ContDiffOn ℝ n (fun q : ℝ × (Vec3 × ℝ) => p (rotZ (-q.1) q.2.1, q.2.2)) (univ ×ˢ
      unitCylinder) := by
  have ha : ContDiffOn ℝ n (fun q : ℝ × (Vec3 × ℝ) => rotZ (-q.1) q.2.1) (univ ×ˢ unitCylinder) :=
    ((contDiff_rotZ_uncurry n).comp (contDiff_fst.neg.prodMk contDiff_snd.fst)).contDiffOn
  have hb : ContDiffOn ℝ n (fun q : ℝ × (Vec3 × ℝ) => q.2.2) (univ ×ˢ unitCylinder) :=
    contDiffOn_snd.snd
  have hinner : ContDiffOn ℝ n (fun q : ℝ × (Vec3 × ℝ) => (rotZ (-q.1) q.2.1, q.2.2))
      (univ ×ˢ unitCylinder) := ha.prodMk hb
  have hmaps : MapsTo (fun q : ℝ × (Vec3 × ℝ) => (rotZ (-q.1) q.2.1, q.2.2))
      (univ ×ˢ unitCylinder) unitCylinder := fun q hq => rotZ_mem_unitCylinder (-q.1) hq.2
  have h := hp.comp hinner hmaps
  exact h

/-- The angular mean of a `C^n` scalar field on the unit cylinder is `C^n` there. -/
theorem contDiffOn_angularMeanScalar (n : ℕ∞) {p : ParabolicPoint → ℝ}
    (hp : ContDiffOn ℝ n (fun z : Vec3 × ℝ => p z) unitCylinder) :
    ContDiffOn ℝ n (fun z : Vec3 × ℝ => angularMeanScalar p z) unitCylinder :=
  (contDiffOn_parametric_intervalIntegral isOpen_unitCylinder_prod Real.two_pi_pos.le n
    (contDiffOn_angularMeanScalar_integrand n hp)).const_smul (2 * Real.pi)⁻¹

/-- For a `C¹` scalar field, a spatial partial derivative of the angular mean is the
angular mean of the corresponding spatial partial derivatives of the rotated fields: the
derivative passes under the angular integral. -/
theorem spatialPartial_angularMeanScalar {p : ParabolicPoint → ℝ}
    (hp : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => p z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (j : Fin 3) :
    spatialPartial (fun w => angularMeanScalar p w) j z =
      (2 * Real.pi)⁻¹ *
        ∫ φ in (0 : ℝ)..(2 * Real.pi), spatialPartial (fun w => p (rotZ (-φ) w.1, w.2)) j z := by
  obtain ⟨x₀, t⟩ := z
  have hx₀ : x₀ ∈ vec3Ball 0 1 := hz.1
  have ht : t ∈ Ioo (-1 : ℝ) 0 := hz.2
  have hball : IsOpen (vec3Ball 0 1) := isOpen_vec3Ball 0 1
  have hrot := contDiffOn_angularMeanScalar_integrand 1 hp
  set G : ℝ × Vec3 → ℝ := fun q => p (rotZ (-q.1) q.2, t) with hG_def
  have hGsm : ContDiffOn ℝ 1 G (univ ×ˢ vec3Ball 0 1) := by
    have hemb : ContDiffOn ℝ 1 (fun q : ℝ × Vec3 => (q.1, (q.2, t)))
        (univ ×ˢ vec3Ball 0 1) :=
      (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)).contDiffOn
    have hmaps : MapsTo (fun q : ℝ × Vec3 => (q.1, (q.2, t))) (univ ×ˢ vec3Ball 0 1)
        (univ ×ˢ unitCylinder) := fun q hq => ⟨mem_univ _, hq.2, ht⟩
    have h2 := hrot.comp hemb hmaps
    exact h2
  have hev : (fun x => angularMeanScalar p (x, t)) =ᶠ[𝓝 x₀]
      fun x => (2 * Real.pi)⁻¹ * ∫ φ in Ioc 0 (2 * Real.pi), G (φ, x) := by
    filter_upwards [hball.mem_nhds hx₀] with x hx
    change ((2 * Real.pi)⁻¹ • ∫ φ in (0 : ℝ)..(2 * Real.pi), p (rotZ (-φ) x, t)) = _
    rw [smul_eq_mul, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  have hderiv := (hasFDerivAt_parametric_integral_Ioc hball hx₀ hGsm 0 (2 * Real.pi)).const_mul
    (2 * Real.pi)⁻¹
  have hDint : IntegrableOn (fun φ => fderiv ℝ (fun x => G (φ, x)) x₀) (Ioc 0 (2 * Real.pi)) :=
    (continuous_section_of_continuousOn (continuousOn_fderiv_section_of_contDiffOn hball hGsm)
      hx₀).integrableOn_Ioc
  change fderiv ℝ (fun x => angularMeanScalar p (x, t)) x₀ (basisVec j) = _
  rw [hev.fderiv_eq, hderiv.fderiv, smul_apply, smul_eq_mul,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, ContinuousLinearMap.integral_apply hDint]
  rfl

/-- A component of the angular mean of a `C^∞` vector field is the angular mean of the
corresponding component of the rotated fields. -/
theorem angularMean_apply_eq (f : ParabolicPoint → Vec3)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i : Fin 3) :
    angularMean f z i = (2 * Real.pi)⁻¹ * ∫ φ in (0 : ℝ)..(2 * Real.pi), rotField φ f z i := by
  have hrot := contDiffOn_rotField_uncurry (⊤ : ℕ∞) hf
  have hint : IntegrableOn (fun φ => rotField φ f z) (Ioc 0 (2 * Real.pi)) :=
    (continuous_section_of_continuousOn hrot.continuousOn (x := z) hz).integrableOn_Ioc
  change ((2 * Real.pi)⁻¹ • ∫ φ in (0 : ℝ)..(2 * Real.pi), rotField φ f z) i = _
  rw [Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integral_comp_comm
    hint).symm

/-- The value of a `2π`-periodic average of a constant function is that constant. -/
private theorem intervalIntegral_const_average (c : ℝ) :
    (2 * Real.pi)⁻¹ * ∫ _φ in (0 : ℝ)..(2 * Real.pi), c = c := by
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  field_simp

/-- The pressure gradient term of the rotated system, as a function of the angle, is
interval integrable over one period: it is continuous, by differentiation under the joint
`C¹` integrand. -/
private theorem intervalIntegrable_spatialPartial_comp_rotZ {p : ParabolicPoint → ℝ}
    (hp : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => p z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i : Fin 3) :
    IntervalIntegrable (fun φ : ℝ => spatialPartial (fun w => p (rotZ (-φ) w.1, w.2)) i z)
      MeasureTheory.volume 0 (2 * Real.pi) := by
  obtain ⟨x₀, t⟩ := z
  have hx₀ : x₀ ∈ vec3Ball 0 1 := hz.1
  have ht : t ∈ Ioo (-1 : ℝ) 0 := hz.2
  have hball : IsOpen (vec3Ball 0 1) := isOpen_vec3Ball 0 1
  have hrot := contDiffOn_angularMeanScalar_integrand 1 hp
  set G : ℝ × Vec3 → ℝ := fun q => p (rotZ (-q.1) q.2, t) with hG_def
  have hGsm : ContDiffOn ℝ 1 G (univ ×ˢ vec3Ball 0 1) := by
    have hemb : ContDiffOn ℝ 1 (fun q : ℝ × Vec3 => (q.1, (q.2, t)))
        (univ ×ˢ vec3Ball 0 1) :=
      (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)).contDiffOn
    have hmaps : MapsTo (fun q : ℝ × Vec3 => (q.1, (q.2, t))) (univ ×ˢ vec3Ball 0 1)
        (univ ×ˢ unitCylinder) := fun q hq => ⟨mem_univ _, hq.2, ht⟩
    have hcomp := hrot.comp hemb hmaps
    exact hcomp
  have hDcontOn := continuousOn_fderiv_section_of_contDiffOn hball hGsm
  have hDcont : Continuous (fun φ : ℝ => fderiv ℝ (fun x => G (φ, x)) x₀) :=
    continuous_section_of_continuousOn hDcontOn hx₀
  have hcont : Continuous (fun φ : ℝ => fderiv ℝ (fun x => G (φ, x)) x₀ (basisVec i)) :=
    hDcont.clm_apply continuous_const
  exact hcont.intervalIntegrable 0 (2 * Real.pi)

/-- A component of the rotated force, as a function of the angle, is interval integrable
over one period: it is continuous, being the section of a jointly continuous field. -/
private theorem intervalIntegrable_rotField_apply (f : ParabolicPoint → Vec3)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (i : Fin 3) :
    IntervalIntegrable (fun φ : ℝ => rotField φ f z i) MeasureTheory.volume 0 (2 * Real.pi) := by
  have hrot := contDiffOn_rotField_uncurry (⊤ : ℕ∞) hf
  have h1 : Continuous (fun φ : ℝ => rotField φ f z) :=
    continuous_section_of_continuousOn hrot.continuousOn hz
  have hcont : Continuous (fun φ : ℝ => rotField φ f z i) := (continuous_apply i).comp h1
  exact hcont.intervalIntegrable 0 (2 * Real.pi)

/-- Pointwise agreement of two scalar fields on the unit cylinder transports the time
partial derivative. -/
private theorem timePartial_congr_of_eqOn {v u : ParabolicPoint → ℝ}
    (h : ∀ w ∈ unitCylinder, v w = u w) {z : ParabolicPoint} (hz : z ∈ unitCylinder) :
    timePartial v z = timePartial u z := by
  change fderiv ℝ (fun s : ℝ => v (z.1, s)) z.2 1 = fderiv ℝ (fun s : ℝ => u (z.1, s)) z.2 1
  have hev : (fun s : ℝ => v (z.1, s)) =ᶠ[nhds z.2] (fun s : ℝ => u (z.1, s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hz.2] with s hs using h (z.1, s) ⟨hz.1, hs⟩
  rw [hev.fderiv_eq]

/-- Pointwise agreement of two scalar fields on the unit cylinder transports a spatial
partial derivative. -/
theorem spatialPartial_congr_of_eqOn {v u : ParabolicPoint → ℝ}
    (h : ∀ w ∈ unitCylinder, v w = u w) {z : ParabolicPoint} (hz : z ∈ unitCylinder) (j : Fin 3) :
    spatialPartial v j z = spatialPartial u j z := by
  change fderiv ℝ (fun y : Vec3 => v (y, z.2)) z.1 (basisVec j)
    = fderiv ℝ (fun y : Vec3 => u (y, z.2)) z.1 (basisVec j)
  have hev : (fun y : Vec3 => v (y, z.2)) =ᶠ[nhds z.1] (fun y : Vec3 => u (y, z.2)) := by
    filter_upwards [(isOpen_vec3Ball 0 1).mem_nhds hz.1] with y hy using h (y, z.2) ⟨hy, hz.2⟩
  rw [hev.fderiv_eq]

/-- Pointwise agreement of two scalar fields on the unit cylinder transports a second
spatial partial derivative. -/
private theorem spatialSecondPartial_congr_of_eqOn {v u : ParabolicPoint → ℝ}
    (h : ∀ w ∈ unitCylinder, v w = u w) {z : ParabolicPoint} (hz : z ∈ unitCylinder) (i j : Fin 3) :
    spatialSecondPartial v i j z = spatialSecondPartial u i j z :=
  spatialPartial_congr_of_eqOn (fun _w hw => spatialPartial_congr_of_eqOn h hw i) hz j

/-- The angular mean of a classical solution with axisymmetric velocity is again a classical
solution, with pressure and force replaced by their angular means (`sec:reduction:core`,
design note R8). Since the velocity is fixed by every rotation, only the pressure and force
terms of the momentum equation change under averaging; the momentum and divergence equations
themselves are linear in `(p, f)` with `u` fixed, so they survive averaging over `φ`. -/
theorem isClassicalSolutionOn_angularMean
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) :
    IsClassicalSolutionOn u (angularMeanScalar p) (angularMean f) unitCylinder := by
  obtain ⟨hu, hp, hf, hmom, hdiv⟩ := hsol
  refine ⟨hu, contDiffOn_angularMeanScalar (⊤ : ℕ∞) hp, contDiffOn_angularMean_smooth hf, ?_, ?_⟩
  · intro z hz i
    have hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder := hu.of_le (by norm_num)
    have hp1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => p w) unitCylinder := hp.of_le (by norm_num)
    have hsys : ∀ φ : ℝ, timePartial (fun w => u w i) z +
        ∑ j : Fin 3, u z j * spatialPartial (fun w => u w i) j z -
        ∑ j : Fin 3, spatialSecondPartial (fun w => u w i) j j z +
        spatialPartial (fun w => p (rotZ (-φ) w.1, w.2)) i z = rotField φ f z i := by
      intro φ
      have hrotsol := isClassicalSolutionOn_rotField φ u p f ⟨hu, hp, hf, hmom, hdiv⟩
      have hmomφ := hrotsol.2.2.2.1 z hz i
      have heq : ∀ w ∈ unitCylinder, rotField φ u w = u w :=
        fun w hw => haxi.rotField_eq (fun ψ _ hw' => rotZ_mem_unitCylinder ψ hw') φ hw
      have hcongr_i : ∀ w ∈ unitCylinder, rotField φ u w i = u w i := fun w hw => congrFun (heq
        w hw) i
      simp only [congrFun (heq z hz), spatialPartial_congr_of_eqOn hcongr_i hz,
        spatialSecondPartial_congr_of_eqOn hcongr_i hz] at hmomφ
      rwa [timePartial_congr_of_eqOn hcongr_i hz] at hmomφ
    have hCint : IntervalIntegrable
        (fun _ : ℝ => timePartial (fun w => u w i) z +
          ∑ j : Fin 3, u z j * spatialPartial (fun w => u w i) j z -
          ∑ j : Fin 3, spatialSecondPartial (fun w => u w i) j j z)
        MeasureTheory.volume 0 (2 * Real.pi) := intervalIntegrable_const
    have hXint := intervalIntegrable_spatialPartial_comp_rotZ hp1 hz i
    have hkey : (2 * Real.pi)⁻¹ *
          (∫ φ in (0 : ℝ)..(2 * Real.pi),
            (timePartial (fun w => u w i) z +
              ∑ j : Fin 3, u z j * spatialPartial (fun w => u w i) j z -
              ∑ j : Fin 3, spatialSecondPartial (fun w => u w i) j j z +
              spatialPartial (fun w => p (rotZ (-φ) w.1, w.2)) i z))
        = (2 * Real.pi)⁻¹ * ∫ φ in (0 : ℝ)..(2 * Real.pi), rotField φ f z i := by
      rw [show (fun φ : ℝ =>
          timePartial (fun w => u w i) z +
            ∑ j : Fin 3, u z j * spatialPartial (fun w => u w i) j z -
            ∑ j : Fin 3, spatialSecondPartial (fun w => u w i) j j z +
            spatialPartial (fun w => p (rotZ (-φ) w.1, w.2)) i z)
          = (fun φ : ℝ => rotField φ f z i) from funext hsys]
    rw [intervalIntegral.integral_add hCint hXint, mul_add, intervalIntegral_const_average,
      ← spatialPartial_angularMeanScalar hp1 hz i, ← angularMean_apply_eq f hf hz i] at hkey
    exact hkey
  · exact hdiv

/-! ### Corollaries -/

/-- The angular mean of a vector field is axisymmetric. -/
theorem isAxisymmetricOn_angularMean_force (f : ParabolicPoint → Vec3) :
    IsAxisymmetricOn (angularMean f) unitCylinder :=
  isAxisymmetricOn_angularMean f unitCylinder

end CIV
