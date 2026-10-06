/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.AveragedClassical
public import LeanPool.CIVAxisymmetric.Reduction.AxisymmetryFromCore
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Axisymmetry of the pressure

For a classical solution of the forced Navier–Stokes equations `eq:nse:forced` on the unit
cylinder whose velocity and force are both axisymmetric, the pressure is axisymmetric too:
`p (Q_φ x, t) = p (x, t)` for every angle `φ` (`pressure_rotZ_invariant`). Rotation
invariance of the pressure is therefore a consequence of the momentum equation and not an
extra standing assumption of Section `sec:aniso:equations`.

The argument is the one of design note R8. The system is covariant under the rigid
rotations (`isClassicalSolutionOn_rotField`), so the rotated triple
`(ℛ_φ u, p ∘ Q_φ⁻¹, ℛ_φ f)` solves it as well. Axisymmetry identifies `ℛ_φ u` with `u` and
`ℛ_φ f` with `f` on the cylinder, and the cylinder is open, so the two systems have the
same velocity, the same force and the same derivatives of the velocity there. Subtracting
the two momentum equations leaves only the two pressure gradients, whence

`∂_i (p ∘ Q_φ⁻¹) = ∂_i p` on the cylinder.

On a fixed time slice the difference `y ↦ p (Q_φ⁻¹ y, t) - p (y, t)` therefore has vanishing
spatial derivative on the unit ball, which is convex and open, so it is constant there. Its
value at the origin is zero because every rotation fixes the axis, and the constant is
therefore zero.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Classical derivatives depend only on the values on the cylinder -/

/-- Two scalars agreeing on the unit cylinder have the same time derivative there. -/
private theorem timePartial_eq_of_eqOn_unitCylinder {g h : ParabolicPoint → ℝ}
    (heq : ∀ w ∈ unitCylinder, g w = h w) {z : ParabolicPoint} (hz : z ∈ unitCylinder) :
    timePartial g z = timePartial h z := by
  have hev : (fun s : ℝ => g (z.1, s)) =ᶠ[nhds z.2] fun s : ℝ => h (z.1, s) := by
    filter_upwards [isOpen_Ioo.mem_nhds hz.2] with s hs
    exact heq (z.1, s) ⟨hz.1, hs⟩
  show fderiv ℝ (fun s : ℝ => g (z.1, s)) z.2 1 = fderiv ℝ (fun s : ℝ => h (z.1, s)) z.2 1
  rw [hev.fderiv_eq]

/-- Two scalars agreeing on the unit cylinder have the same spatial partial derivatives
there. -/
private theorem spatialPartial_eq_of_eqOn_unitCylinder {g h : ParabolicPoint → ℝ}
    (heq : ∀ w ∈ unitCylinder, g w = h w) (a : Fin 3) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    spatialPartial g a z = spatialPartial h a z := by
  have hev : (fun y : Vec3 => g (y, z.2)) =ᶠ[nhds z.1] fun y : Vec3 => h (y, z.2) := by
    filter_upwards [(isOpen_vec3Ball 0 1).mem_nhds hz.1] with y hy
    exact heq (y, z.2) ⟨hy, hz.2⟩
  show fderiv ℝ (fun y : Vec3 => g (y, z.2)) z.1 (basisVec a)
    = fderiv ℝ (fun y : Vec3 => h (y, z.2)) z.1 (basisVec a)
  rw [hev.fderiv_eq]

/-- Two scalars agreeing on the unit cylinder have the same second spatial partial
derivatives there. -/
private theorem spatialSecondPartial_eq_of_eqOn_unitCylinder {g h : ParabolicPoint → ℝ}
    (heq : ∀ w ∈ unitCylinder, g w = h w) (a b : Fin 3) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    spatialSecondPartial g a b z = spatialSecondPartial h a b z := by
  have hev : (fun y : Vec3 => spatialPartial g a (y, z.2))
      =ᶠ[nhds z.1] fun y : Vec3 => spatialPartial h a (y, z.2) := by
    filter_upwards [(isOpen_vec3Ball 0 1).mem_nhds hz.1] with y hy
    exact spatialPartial_eq_of_eqOn_unitCylinder heq a (z := (y, z.2)) ⟨hy, hz.2⟩
  show fderiv ℝ (fun y : Vec3 => spatialPartial g a (y, z.2)) z.1 (basisVec b)
    = fderiv ℝ (fun y : Vec3 => spatialPartial h a (y, z.2)) z.1 (basisVec b)
  rw [hev.fderiv_eq]

/-! ### The pressure gradient is unchanged by a rotation of the point -/

/-- Rotation covariance of the pressure gradient (design note R8): for an axisymmetric
velocity and force the pressure precomposed with a rotation has the same spatial gradient
as the pressure itself. This is the technical heart: the rotated triple solves the same
system with the same velocity and the same force, so the two momentum equations differ only
in their pressure terms. -/
private theorem spatialPartial_pressure_comp_rotZ {u : ParabolicPoint → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (φ : ℝ) {z : ParabolicPoint} (hz : z ∈ unitCylinder) (i : Fin 3) :
    spatialPartial (fun w => p (rotZ (-φ) w.1, w.2)) i z = spatialPartial p i z := by
  have hue : ∀ w ∈ unitCylinder, rotField φ u w = u w :=
    (isAxisymmetricOn_unitCylinder_iff u).1 haxi φ
  have hfe : ∀ w ∈ unitCylinder, rotField φ f w = f w :=
    (isAxisymmetricOn_unitCylinder_iff f).1 hfaxi φ
  have hcomp : ∀ w ∈ unitCylinder, rotField φ u w i = u w i :=
    fun w hw => congrFun (hue w hw) i
  have hrot := isClassicalSolutionOn_rotField φ u p f hsol
  have hmomRot := hrot.2.2.2.1 z hz i
  have hmomOrig := hsol.2.2.2.1 z hz i
  have h1 : timePartial (fun w => rotField φ u w i) z = timePartial (fun w => u w i) z :=
    timePartial_eq_of_eqOn_unitCylinder (g := fun w => rotField φ u w i)
      (h := fun w => u w i) hcomp hz
  have h2 : ∑ j, rotField φ u z j * spatialPartial (fun w => rotField φ u w i) j z
      = ∑ j, u z j * spatialPartial (fun w => u w i) j z :=
    Finset.sum_congr rfl fun j _ => by
      rw [spatialPartial_eq_of_eqOn_unitCylinder (g := fun w => rotField φ u w i)
        (h := fun w => u w i) hcomp j hz, congrFun (hue z hz) j]
  have h3 : ∑ j, spatialSecondPartial (fun w => rotField φ u w i) j j z
      = ∑ j, spatialSecondPartial (fun w => u w i) j j z :=
    Finset.sum_congr rfl fun j _ =>
      spatialSecondPartial_eq_of_eqOn_unitCylinder (g := fun w => rotField φ u w i)
        (h := fun w => u w i) hcomp j j hz
  have h4 : rotField φ f z i = f z i := congrFun (hfe z hz) i
  linarith only [hmomRot, hmomOrig, h1, h2, h3, h4]

/-! ### The rotated pressure slice differs from the pressure slice by a constant -/

/-- A continuous linear functional on `Vec3` vanishing on the coordinate basis is zero. -/
private theorem clm_eq_zero_of_basisVec {L : Vec3 →L[ℝ] ℝ} (h : ∀ a : Fin 3, L (basisVec a) = 0) :
    L = 0 := by
  ext v
  have hv : L v = ∑ a, v a • L (basisVec a) := by
    conv_lhs => rw [← sum_smul_basisVec v]
    rw [map_sum]
    simp only [map_smul]
  simp [hv, h]

/-- The spatial slice of the rotated pressure and the spatial slice of the pressure have the
same derivative on the unit ball. -/
private theorem fderiv_pressure_slice_sub {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (φ : ℝ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) {y : Vec3} (hy : y ∈ vec3Ball 0 1) :
    fderiv ℝ (fun a : Vec3 => p (rotZ (-φ) a, t) - p (a, t)) y = 0 := by
  have hp1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => p w) unitCylinder := hsol.2.1.of_le (by simp)
  have hpr1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => p (rotZ (-φ) w.1, w.2)) unitCylinder :=
    (isClassicalSolutionOn_rotField φ u p f hsol).2.1.of_le (by simp)
  have hdp : DifferentiableAt ℝ (fun a : Vec3 => p (a, t)) y :=
    differentiableAt_spatialSlice hp1 (z := (y, t)) ⟨hy, ht⟩
  have hdpr : DifferentiableAt ℝ (fun a : Vec3 => p (rotZ (-φ) a, t)) y :=
    differentiableAt_spatialSlice (v := fun w => p (rotZ (-φ) w.1, w.2)) hpr1 (z := (y, t))
      ⟨hy, ht⟩
  rw [fderiv_fun_sub hdpr hdp]
  refine clm_eq_zero_of_basisVec fun a => ?_
  rw [sub_apply, sub_eq_zero]
  exact spatialPartial_pressure_comp_rotZ hsol haxi hfaxi φ (z := (y, t)) ⟨hy, ht⟩ a

/-- On each time slice the pressure is invariant under every rotation about the axis. -/
private theorem pressure_slice_comp_rotZ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (φ : ℝ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) {y : Vec3} (hy : y ∈ vec3Ball 0 1) :
    p (rotZ (-φ) y, t) = p (y, t) := by
  have hp1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => p w) unitCylinder := hsol.2.1.of_le (by simp)
  have hpr1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => p (rotZ (-φ) w.1, w.2)) unitCylinder :=
    (isClassicalSolutionOn_rotField φ u p f hsol).2.1.of_le (by simp)
  have hdiff : DifferentiableOn ℝ (fun a : Vec3 => p (rotZ (-φ) a, t) - p (a, t))
      (vec3Ball 0 1) := by
    intro b hb
    have hdp : DifferentiableAt ℝ (fun a : Vec3 => p (a, t)) b :=
      differentiableAt_spatialSlice hp1 (z := (b, t)) ⟨hb, ht⟩
    have hdpr : DifferentiableAt ℝ (fun a : Vec3 => p (rotZ (-φ) a, t)) b :=
      differentiableAt_spatialSlice (v := fun w => p (rotZ (-φ) w.1, w.2)) hpr1 (z := (b, t))
        ⟨hb, ht⟩
    exact (hdpr.sub hdp).differentiableWithinAt
  have hzero : ∀ b ∈ vec3Ball (0 : Vec3) 1,
      fderivWithin ℝ (fun a : Vec3 => p (rotZ (-φ) a, t) - p (a, t)) (vec3Ball 0 1) b = 0 := by
    intro b hb
    rw [fderivWithin_of_isOpen (isOpen_vec3Ball 0 1) hb]
    exact fderiv_pressure_slice_sub hsol haxi hfaxi φ ht hb
  have hmem : (0 : Vec3) ∈ vec3Ball (0 : Vec3) 1 := zero_mem_vec3Ball_zero one_pos
  have hconst : p (rotZ (-φ) (0 : Vec3), t) - p ((0 : Vec3), t)
      = p (rotZ (-φ) y, t) - p (y, t) :=
    (convex_vec3Ball_zero 1).is_const_of_fderivWithin_eq_zero hdiff hzero hmem hy
  rw [rotZ_zero_vec] at hconst
  linarith only [hconst]

/-! ### Axisymmetry of the pressure -/

/-- The pressure of a classical solution with axisymmetric velocity and axisymmetric force
is itself axisymmetric on the unit cylinder (design note R8). -/
theorem pressure_rotZ_invariant (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder) :
    ∀ φ : ℝ, ∀ z ∈ unitCylinder, p (rotZ φ z.1, z.2) = p z := by
  intro φ z hz
  obtain ⟨y, t⟩ := z
  have h := pressure_slice_comp_rotZ hsol haxi hfaxi (-φ) hz.2 hz.1
  rwa [neg_neg] at h

end CIV
