/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingEquation

/-!
# First-derivative identities and bound for the rescaled receding azimuthal vorticity

The derivative identities and first-derivative bound of the rescaled receding azimuthal
vorticity `Θ_n` of `eq:aniso:zoom:receding:vorticity`, off
`eq:aniso:zoom:receding:equation`'s manuscript display — the ingredient of
`eq:aniso:zoom:receding:bound`'s derivative analogue needed before the Arzelà–Ascoli
extraction of Step 3.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-! ### A C² mixed-partial symmetry fact for the two Cartesian spatial directions 0 and 2 -/

private theorem spatialPartial_spatialPartial_comm_02 (g : ParabolicPoint → ℝ) (z : ParabolicPoint)
    (hg : ContDiffOn ℝ 2 (fun y : Vec3 => g (y, z.2)) (vec3Ball 0 1)) (hz1 : z.1 ∈ vec3Ball 0 1) :
    spatialPartial (fun w => spatialPartial g 0 w) 2 z
      = spatialPartial (fun w => spatialPartial g 2 w) 0 z := by
  set φ : Vec3 → ℝ := fun y => g (y, z.2) with hφ_def
  have hopen : IsOpen (vec3Ball (0 : Vec3) 1) := isOpen_vec3Ball 0 1
  have hg_at : ContDiffAt ℝ 2 φ z.1 := hg.contDiffAt (hopen.mem_nhds hz1)
  have hsymm : ∀ v w : Vec3, fderiv ℝ (fderiv ℝ φ) z.1 v w = fderiv ℝ (fderiv ℝ φ) z.1 w v :=
    hg_at.isSymmSndFDerivAt (by norm_num)
  have hD1 : ContDiffOn ℝ 1 (fderiv ℝ φ) (vec3Ball 0 1) :=
    hg.fderiv_of_isOpen hopen (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) z.1 :=
    (hD1.differentiableOn (by norm_num) z.1 hz1).differentiableAt (hopen.mem_nhds hz1)
  have heq1 : spatialPartial (fun w => spatialPartial g 0 w) 2 z
      = fderiv ℝ (fun x => fderiv ℝ φ x (basisVec 0)) z.1 (basisVec 2) := by
    show fderiv ℝ (fun x : Vec3 => spatialPartial g 0 (x, z.2)) z.1 (basisVec 2) = _
    rfl
  have heq2 : spatialPartial (fun w => spatialPartial g 2 w) 0 z
      = fderiv ℝ (fun x => fderiv ℝ φ x (basisVec 2)) z.1 (basisVec 0) := by
    show fderiv ℝ (fun x : Vec3 => spatialPartial g 2 (x, z.2)) z.1 (basisVec 0) = _
    rfl
  have hconv1 : fderiv ℝ (fun x => fderiv ℝ φ x (basisVec 0)) z.1 (basisVec 2)
      = fderiv ℝ (fderiv ℝ φ) z.1 (basisVec 2) (basisVec 0) := by
    have hcomp : HasFDerivAt (fun x => fderiv ℝ φ x (basisVec 0))
        ((ContinuousLinearMap.apply ℝ ℝ (basisVec 0)).comp (fderiv ℝ (fderiv ℝ φ) z.1)) z.1 :=
      (ContinuousLinearMap.apply ℝ ℝ (basisVec 0)).hasFDerivAt.comp z.1 hD.hasFDerivAt
    rw [hcomp.fderiv]
    simp
  have hconv2 : fderiv ℝ (fun x => fderiv ℝ φ x (basisVec 2)) z.1 (basisVec 0)
      = fderiv ℝ (fderiv ℝ φ) z.1 (basisVec 0) (basisVec 2) := by
    have hcomp : HasFDerivAt (fun x => fderiv ℝ φ x (basisVec 2))
        ((ContinuousLinearMap.apply ℝ ℝ (basisVec 2)).comp (fderiv ℝ (fderiv ℝ φ) z.1)) z.1 :=
      (ContinuousLinearMap.apply ℝ ℝ (basisVec 2)).hasFDerivAt.comp z.1 hD.hasFDerivAt
    rw [hcomp.fderiv]
    simp
  rw [heq1, heq2, hconv1, hconv2]
  exact (hsymm (basisVec 0) (basisVec 2)).symm

/-- The `Z`-derivative of `spatialPartial (u· i) 0` composed with `zoomPointRec`, computed via
the mixed-partial symmetry above so that it lands on the same `meridionalPartial` normal form
`drdz_zoomWRec` uses. -/
private theorem hasDerivAt_spatialPartial_zero_zoomRec_z (lam h rc zc : ℝ)
    (u : ParabolicPoint → Vec3) (i : Fin 3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ =>
      spatialPartial (fun w => u w i) 0 (zoomPointRec lam h rc zc ((p.1.1, s), p.2)))
      (lam ^ (1 - 2 * h) * meridionalPartial (fun w => u w i) 1 1 (zoomPointRec lam h rc zc p))
      p.1.2 := by
  have hpar : ContDiffOn ℝ 1
      (fun z : Vec3 × ℝ => spatialPartial (fun w => u w i) 0 z) unitCylinder :=
    contDiffOn_spatialPartial_of_contDiffOn (contDiffOn_component hu i) 0
  have hbase := hasDerivAt_comp_spatialSlice_scalar isOpen_unitCylinder_prod hpar hp
    (hasDerivAt_meridional_snd (rc + lam * p.1.1) zc (lam ^ (1 - 2 * h)) p.1.2) rfl
  have hzp : zoomPointRec lam h rc zc p ∈ unitCylinder := hp
  have hslice : ContDiffOn ℝ 2 (fun y : Vec3 => u (y, (zoomPointRec lam h rc zc p).2) i)
      (vec3Ball 0 1) :=
    contDiffOn_spatialSlice (contDiffOn_component hu i) hzp.2
  have hcomm := spatialPartial_spatialPartial_comm_02 (fun w => u w i)
    (zoomPointRec lam h rc zc p) hslice hzp.1
  have hval : spatialPartial (fun w => spatialPartial (fun w' => u w' i) 0 w) 2
      (zoomPointRec lam h rc zc p)
      = meridionalPartial (fun w => u w i) 1 1 (zoomPointRec lam h rc zc p) := hcomm
  rwa [hval] at hbase

/-! ### The four pieces of `zoomTheta`, differentiated along a coordinate slice -/

private theorem hasDerivAt_dz_zoomVRec_radial (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    HasDerivAt (fun r : ℝ => dz (zoomVRec lam h rc zc u) ((r, p.1.2), p.2))
      (dr (dz (zoomVRec lam h rc zc u)) p) p.1.1 := by
  rw [drdz_zoomVRec lam h rc zc u hu p hp]
  have h_event := eventuallyEq_slice_r_rec lam h rc zc (dz (zoomVRec lam h rc zc u))
    (spatialPartial (fun w => u w 0) 2) (lam * lam ^ (1 - 2 * h)) p hp
    (fun q hq => dz_zoomVRec lam h rc zc u (hu.of_le (by norm_num)) q hq)
  have h_mul := (hasDerivAt_spatialPartial_two_zoomRec_r lam h rc zc u 0 hu p hp).const_mul
    (lam * lam ^ (1 - 2 * h))
  simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul.congr_of_eventuallyEq h_event

private theorem hasDerivAt_dr_zoomWRec_radial (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    HasDerivAt (fun r : ℝ => dr (zoomWRec lam h rc zc u) ((r, p.1.2), p.2))
      (dr (dr (zoomWRec lam h rc zc u)) p) p.1.1 := by
  rw [drdr_zoomWRec lam h rc zc u hu p hp]
  have h_event := eventuallyEq_slice_r_rec lam h rc zc (dr (zoomWRec lam h rc zc u))
    (spatialPartial (fun w => u w 2) 0) (lam ^ 2 * lam ^ (2 * h)) p hp
    (fun q hq => dr_zoomWRec lam h rc zc u (hu.of_le (by norm_num)) q hq)
  have h_mul := (hasDerivAt_spatialPartial_zero_zoomRec_r lam h rc zc u 2 hu p hp).const_mul
    (lam ^ 2 * lam ^ (2 * h))
  simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul.congr_of_eventuallyEq h_event

private theorem hasDerivAt_dz_zoomVRec_vertical (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => dz (zoomVRec lam h rc zc u) ((p.1.1, s), p.2))
      (dz (dz (zoomVRec lam h rc zc u)) p) p.1.2 := by
  rw [dzdz_zoomVRec lam h rc zc u hu p hp]
  have h_event := eventuallyEq_slice_z_rec lam h rc zc (dz (zoomVRec lam h rc zc u))
    (spatialPartial (fun w => u w 0) 2) (lam * lam ^ (1 - 2 * h)) p hp
    (fun q hq => dz_zoomVRec lam h rc zc u (hu.of_le (by norm_num)) q hq)
  have h_mul := (hasDerivAt_spatialPartial_two_zoomRec_z lam h rc zc u 0 hu p hp).const_mul
    (lam * lam ^ (1 - 2 * h))
  simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul.congr_of_eventuallyEq h_event

private theorem hasDerivAt_dr_zoomWRec_vertical (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => dr (zoomWRec lam h rc zc u) ((p.1.1, s), p.2))
      (dr (dz (zoomWRec lam h rc zc u)) p) p.1.2 := by
  rw [drdz_zoomWRec lam h rc zc u hu p hp]
  have h_event : (fun s : ℝ => dr (zoomWRec lam h rc zc u) ((p.1.1, s), p.2))
      =ᶠ[𝓝 p.1.2]
    fun s : ℝ => lam ^ 2 * lam ^ (2 * h) *
      spatialPartial (fun w => u w 2) 0 (zoomPointRec lam h rc zc ((p.1.1, s), p.2)) := by
    have hpS : p.1.2 ∈ {s : ℝ | zoomPointRec lam h rc zc ((p.1.1, s), p.2) ∈ unitCylinder} := hp
    filter_upwards [(isOpen_slice_z_rec lam h rc zc p).mem_nhds hpS] with s hs
    exact dr_zoomWRec lam h rc zc u (hu.of_le (by norm_num)) ((p.1.1, s), p.2) hs
  have h_mul := (hasDerivAt_spatialPartial_zero_zoomRec_z lam h rc zc u 2 hu p hp).const_mul
    (lam ^ 2 * lam ^ (2 * h))
  have h_final : HasDerivAt (fun s : ℝ => lam ^ 2 * lam ^ (2 * h) *
      spatialPartial (fun w => u w 2) 0 (zoomPointRec lam h rc zc ((p.1.1, s), p.2)))
      (lam ^ 2 * lam ^ (2 * h) * lam ^ (1 - 2 * h) *
        meridionalPartial (fun w => u w 2) 1 1 (zoomPointRec lam h rc zc p)) p.1.2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul
  exact h_final.congr_of_eventuallyEq h_event

/-! ### The derivative identities and bound for the rescaled receding azimuthal vorticity -/

/-- The radial derivative of the rescaled receding azimuthal vorticity `Θ_n`, differentiating
`eq:aniso:zoom:receding:vorticity`'s difference termwise. -/
theorem dr_zoomTheta_eq (lam h rc zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dr (zoomTheta lam h rc zc u) p
      = (lam ^ (2 * h)) ^ 2 * dr (dz (zoomVRec lam h rc zc u)) p
        - dr (dr (zoomWRec lam h rc zc u)) p := by
  rw [dr]
  have h_event : (fun r : ℝ => zoomTheta lam h rc zc u ((r, p.1.2), p.2))
      =ᶠ[𝓝 p.1.1]
      fun r : ℝ => (lam ^ (2 * h)) ^ 2 * dz (zoomVRec lam h rc zc u) ((r, p.1.2), p.2)
        - dr (zoomWRec lam h rc zc u) ((r, p.1.2), p.2) := by
    have hpS : p.1.1 ∈ {r : ℝ | zoomPointRec lam h rc zc ((r, p.1.2), p.2) ∈ unitCylinder} := hp
    filter_upwards [(isOpen_slice_r_rec lam h rc zc p).mem_nhds hpS] with r hr
    exact zoomTheta_eq lam h rc zc hlam u (hu.of_le (by norm_num)) ((r, p.1.2), p.2) hr
  have hnum : HasDerivAt
      (fun r : ℝ => (lam ^ (2 * h)) ^ 2 * dz (zoomVRec lam h rc zc u) ((r, p.1.2), p.2)
        - dr (zoomWRec lam h rc zc u) ((r, p.1.2), p.2))
      ((lam ^ (2 * h)) ^ 2 * dr (dz (zoomVRec lam h rc zc u)) p
        - dr (dr (zoomWRec lam h rc zc u)) p) p.1.1 :=
    ((hasDerivAt_dz_zoomVRec_radial lam h rc zc u hu p hp).const_mul ((lam ^ (2 * h)) ^ 2)).sub
      (hasDerivAt_dr_zoomWRec_radial lam h rc zc u hu p hp)
  exact (hnum.congr_of_eventuallyEq h_event).deriv

/-- The vertical derivative of the rescaled receding azimuthal vorticity `Θ_n`, differentiating
`eq:aniso:zoom:receding:vorticity`'s difference termwise. -/
theorem dz_zoomTheta_eq (lam h rc zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dz (zoomTheta lam h rc zc u) p
      = (lam ^ (2 * h)) ^ 2 * dz (dz (zoomVRec lam h rc zc u)) p
        - dr (dz (zoomWRec lam h rc zc u)) p := by
  rw [dz]
  have h_event : (fun s : ℝ => zoomTheta lam h rc zc u ((p.1.1, s), p.2))
      =ᶠ[𝓝 p.1.2]
      fun s : ℝ => (lam ^ (2 * h)) ^ 2 * dz (zoomVRec lam h rc zc u) ((p.1.1, s), p.2)
        - dr (zoomWRec lam h rc zc u) ((p.1.1, s), p.2) := by
    have hpS : p.1.2 ∈ {s : ℝ | zoomPointRec lam h rc zc ((p.1.1, s), p.2) ∈ unitCylinder} := hp
    filter_upwards [(isOpen_slice_z_rec lam h rc zc p).mem_nhds hpS] with s hs
    exact zoomTheta_eq lam h rc zc hlam u (hu.of_le (by norm_num)) ((p.1.1, s), p.2) hs
  have hnum : HasDerivAt
      (fun s : ℝ => (lam ^ (2 * h)) ^ 2 * dz (zoomVRec lam h rc zc u) ((p.1.1, s), p.2)
        - dr (zoomWRec lam h rc zc u) ((p.1.1, s), p.2))
      ((lam ^ (2 * h)) ^ 2 * dz (dz (zoomVRec lam h rc zc u)) p
        - dr (dz (zoomWRec lam h rc zc u)) p) p.1.2 :=
    ((hasDerivAt_dz_zoomVRec_vertical lam h rc zc u hu p hp).const_mul ((lam ^ (2 * h)) ^ 2)).sub
      (hasDerivAt_dr_zoomWRec_vertical lam h rc zc u hu p hp)
  exact (hnum.congr_of_eventuallyEq h_event).deriv

/-! ### The first-derivative bound -/

private theorem const_mul_rpow_le_neg_half_rec {C t e : ℝ} (hC : 0 ≤ C) (ht : t ≤ -1)
    (he : e ≤ -(1 / 2 : ℝ)) : C * (-t) ^ e ≤ C * (-t) ^ (-(1 / 2 : ℝ)) :=
  mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith only [ht]) he) hC

private theorem abs_sq_smul_sub_le_rec {A B D delta : ℝ} (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1)
    (hA : |A| ≤ D) (hB : |B| ≤ D) : |delta ^ 2 * A - B| ≤ 2 * D := by
  have h1 : |delta ^ 2 * A - B| ≤ |delta ^ 2 * A| + |B| := by
    rw [sub_eq_add_neg]
    calc |delta ^ 2 * A + -B| ≤ |delta ^ 2 * A| + |(-B)| := abs_add_le _ _
      _ = |delta ^ 2 * A| + |B| := by rw [abs_neg]
  have h2 : |delta ^ 2 * A| = delta ^ 2 * |A| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ delta ^ 2)]
  have h3 : delta ^ 2 ≤ 1 := by nlinarith only [hd0, hd1]
  have h4 : delta ^ 2 * |A| ≤ 1 * |A| := mul_le_mul_of_nonneg_right h3 (abs_nonneg A)
  linarith only [h1, h2, h4, hA, hB]

/-- The sum of the radial and vertical derivatives of the rescaled receding azimuthal
vorticity `Θ_n` is bounded uniformly in the zoom scale by `4C(-τ)^{-1/2}`, the derivative
analogue of `eq:aniso:zoom:receding:bound`. -/
theorem abs_dr_zoomTheta_add_abs_dz_zoomTheta_le {C h lam rc zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2) (hdelta : lam ^ (2 * h) ≤ 1)
    {p : (ℝ × ℝ) × ℝ} (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (htau : p.2 ≤ -1) :
    |dr (zoomTheta lam h rc zc u) p| + |dz (zoomTheta lam h rc zc u) p|
      ≤ 4 * C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
  have hd0 : (0 : ℝ) ≤ lam ^ (2 * h) := Real.rpow_nonneg hlam.le _
  have b1 : |dr (dz (zoomVRec lam h rc zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) :=
    le_trans (abs_drdz_zoomVRec_le C h lam rc zc hlam u hb hu p hp)
      (const_mul_rpow_le_neg_half_rec hC htau (by linarith only [hh1]))
  have b2 : |dr (dr (zoomWRec lam h rc zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
    have hbnd := abs_drdr_zoomWRec_add_abs_drdr_zoomSRec_le C h lam rc zc hlam u hb hu p hp
    have hS : (0 : ℝ) ≤ |dr (dr (zoomSRec lam h rc zc u)) p| := abs_nonneg _
    have hW : |dr (dr (zoomWRec lam h rc zc u)) p| ≤
        C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 2 / 2 - (1 / 2 - h) * 0) := by
      linarith only [hbnd, hS]
    exact le_trans hW (const_mul_rpow_le_neg_half_rec hC htau (by linarith only [hh0]))
  have b3 : |dz (dz (zoomVRec lam h rc zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
    have hbnd := abs_dzdz_zoomVRec_le C h lam rc zc hlam u hb hu p hp
    exact le_trans hbnd (const_mul_rpow_le_neg_half_rec hC htau (by linarith only [hh1]))
  have b4 : |dr (dz (zoomWRec lam h rc zc u)) p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := by
    have hbnd := abs_drdz_zoomWRec_add_abs_drdz_zoomSRec_le C h lam rc zc hlam u hb hu p hp
    have hS : (0 : ℝ) ≤ |dr (dz (zoomSRec lam h rc zc u)) p| := abs_nonneg _
    have hW : |dr (dz (zoomWRec lam h rc zc u)) p| ≤
        C * (-p.2) ^ (-(1 / 2 : ℝ) - h - 1 / 2 - (1 / 2 - h) * 1) := by
      linarith only [hbnd, hS]
    exact le_trans hW (const_mul_rpow_le_neg_half_rec hC htau (by linarith only [hh0, hh1]))
  have hr : |dr (zoomTheta lam h rc zc u) p| ≤ 2 * (C * (-p.2) ^ (-(1 / 2 : ℝ))) := by
    rw [dr_zoomTheta_eq lam h rc zc hlam u hu p hp]
    exact abs_sq_smul_sub_le_rec hd0 hdelta b1 b2
  have hz : |dz (zoomTheta lam h rc zc u) p| ≤ 2 * (C * (-p.2) ^ (-(1 / 2 : ℝ))) := by
    rw [dz_zoomTheta_eq lam h rc zc hlam u hu p hp]
    exact abs_sq_smul_sub_le_rec hd0 hdelta b3 b4
  have hsum : 2 * (C * (-p.2) ^ (-(1 / 2 : ℝ))) + 2 * (C * (-p.2) ^ (-(1 / 2 : ℝ)))
      = 4 * C * (-p.2) ^ (-(1 / 2 : ℝ)) := by ring
  linarith only [hr, hz, hsum]

end CIV
