/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingThetaDerivative
public import LeanPool.CIVAxisymmetric.Zoom.Algebra

/-!
# Lipschitz-in-space bound for the receding-axis rescaled azimuthal vorticity

The Lipschitz-in-space bound for the receding-axis rescaled azimuthal vorticity `Θ_n` of
eq:aniso:zoom:receding:vorticity, the derivative-bound analogue of eq:aniso:zoom:receding:bound,
the input the receding-axis Arzelà–Ascoli extraction of Step 3 needs alongside its
finite-axis counterparts `CIV.Zoom.VRecLipschitz` / `CIV.Zoom.WRecLipschitz`.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-! ### Private helper: mixed-partial symmetry for spatial partials 0 and 2 -/

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
    rfl
  have heq2 : spatialPartial (fun w => spatialPartial g 2 w) 0 z
      = fderiv ℝ (fun x => fderiv ℝ φ x (basisVec 2)) z.1 (basisVec 0) := by
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

/-! ### Private helper: vertical derivative of `spatialPartial (u· i) 0` along `zoomPointRec` -/

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
  rw [hval] at hbase
  simpa [zoomPointRec] using hbase

/-! ### Radial and vertical derivative facts for `zoomTheta` -/

theorem hasDerivAt_dr_zoomTheta (lam h rc zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    HasDerivAt (fun r : ℝ => zoomTheta lam h rc zc u ((r, p.1.2), p.2))
      (dr (zoomTheta lam h rc zc u) p) p.1.1 := by
  have h1 : HasDerivAt (fun r' : ℝ => dz (zoomVRec lam h rc zc u) ((r', p.1.2), p.2))
      (dr (dz (zoomVRec lam h rc zc u)) p) p.1.1 := by
    rw [drdz_zoomVRec lam h rc zc u hu p hp]
    have h_event := eventuallyEq_slice_r_rec lam h rc zc (dz (zoomVRec lam h rc zc u))
      (spatialPartial (fun w => u w 0) 2) (lam * lam ^ (1 - 2 * h)) p hp
      (fun q hq => dz_zoomVRec lam h rc zc u (hu.of_le (by norm_num)) q hq)
    have h_mul := (hasDerivAt_spatialPartial_two_zoomRec_r lam h rc zc u 0 hu p hp).const_mul
      (lam * lam ^ (1 - 2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul.congr_of_eventuallyEq h_event
  have h2 : HasDerivAt (fun r' : ℝ => dr (zoomWRec lam h rc zc u) ((r', p.1.2), p.2))
      (dr (dr (zoomWRec lam h rc zc u)) p) p.1.1 := by
    rw [drdr_zoomWRec lam h rc zc u hu p hp]
    have h_event := eventuallyEq_slice_r_rec lam h rc zc (dr (zoomWRec lam h rc zc u))
      (spatialPartial (fun w => u w 2) 0) (lam ^ 2 * lam ^ (2 * h)) p hp
      (fun q hq => dr_zoomWRec lam h rc zc u (hu.of_le (by norm_num)) q hq)
    have h_mul := (hasDerivAt_spatialPartial_zero_zoomRec_r lam h rc zc u 2 hu p hp).const_mul
      (lam ^ 2 * lam ^ (2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul.congr_of_eventuallyEq h_event
  have h_combined : HasDerivAt
      (fun r' : ℝ => (lam ^ (2 * h)) ^ 2 * dz (zoomVRec lam h rc zc u) ((r', p.1.2), p.2)
        - dr (zoomWRec lam h rc zc u) ((r', p.1.2), p.2))
      ((lam ^ (2 * h)) ^ 2 * dr (dz (zoomVRec lam h rc zc u)) p
        - dr (dr (zoomWRec lam h rc zc u)) p) p.1.1 :=
    ((h1.const_mul ((lam ^ (2 * h)) ^ 2)).sub h2)
  have h_event2 : (fun r' : ℝ => zoomTheta lam h rc zc u ((r', p.1.2), p.2))
      =ᶠ[𝓝 p.1.1]
      fun r' : ℝ => (lam ^ (2 * h)) ^ 2 * dz (zoomVRec lam h rc zc u) ((r', p.1.2), p.2)
        - dr (zoomWRec lam h rc zc u) ((r', p.1.2), p.2) := by
    have hpS : p.1.1 ∈ {r : ℝ | zoomPointRec lam h rc zc ((r, p.1.2), p.2) ∈ unitCylinder} := hp
    filter_upwards [(isOpen_slice_r_rec lam h rc zc p).mem_nhds hpS] with r' hr'
    exact zoomTheta_eq lam h rc zc hlam u (hu.of_le (by norm_num)) ((r', p.1.2), p.2) hr'
  have h_target : ((lam ^ (2 * h)) ^ 2 * dr (dz (zoomVRec lam h rc zc u)) p
        - dr (dr (zoomWRec lam h rc zc u)) p) = dr (zoomTheta lam h rc zc u) p := by
    rw [dr_zoomTheta_eq lam h rc zc hlam u hu p hp]
  simpa [h_target] using h_combined.congr_of_eventuallyEq h_event2

theorem hasDerivAt_dz_zoomTheta (lam h rc zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => zoomTheta lam h rc zc u ((p.1.1, s), p.2))
      (dz (zoomTheta lam h rc zc u) p) p.1.2 := by
  have h1 : HasDerivAt (fun s' : ℝ => dz (zoomVRec lam h rc zc u) ((p.1.1, s'), p.2))
      (dz (dz (zoomVRec lam h rc zc u)) p) p.1.2 := by
    rw [dzdz_zoomVRec lam h rc zc u hu p hp]
    have h_event := eventuallyEq_slice_z_rec lam h rc zc (dz (zoomVRec lam h rc zc u))
      (spatialPartial (fun w => u w 0) 2) (lam * lam ^ (1 - 2 * h)) p hp
      (fun q hq => dz_zoomVRec lam h rc zc u (hu.of_le (by norm_num)) q hq)
    have h_mul := (hasDerivAt_spatialPartial_two_zoomRec_z lam h rc zc u 0 hu p hp).const_mul
      (lam * lam ^ (1 - 2 * h))
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_succ] using h_mul.congr_of_eventuallyEq h_event
  have h2 : HasDerivAt (fun s' : ℝ => dr (zoomWRec lam h rc zc u) ((p.1.1, s'), p.2))
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
  have h_combined : HasDerivAt
      (fun s' : ℝ => (lam ^ (2 * h)) ^ 2 * dz (zoomVRec lam h rc zc u) ((p.1.1, s'), p.2)
        - dr (zoomWRec lam h rc zc u) ((p.1.1, s'), p.2))
      ((lam ^ (2 * h)) ^ 2 * dz (dz (zoomVRec lam h rc zc u)) p
        - dr (dz (zoomWRec lam h rc zc u)) p) p.1.2 :=
    ((h1.const_mul ((lam ^ (2 * h)) ^ 2)).sub h2)
  have h_event2 : (fun s' : ℝ => zoomTheta lam h rc zc u ((p.1.1, s'), p.2))
      =ᶠ[𝓝 p.1.2]
      fun s' : ℝ => (lam ^ (2 * h)) ^ 2 * dz (zoomVRec lam h rc zc u) ((p.1.1, s'), p.2)
        - dr (zoomWRec lam h rc zc u) ((p.1.1, s'), p.2) := by
    have hpS : p.1.2 ∈ {s : ℝ | zoomPointRec lam h rc zc ((p.1.1, s), p.2) ∈ unitCylinder} := hp
    filter_upwards [(isOpen_slice_z_rec lam h rc zc p).mem_nhds hpS] with s hs
    exact zoomTheta_eq lam h rc zc hlam u (hu.of_le (by norm_num)) ((p.1.1, s), p.2) hs
  have h_target : ((lam ^ (2 * h)) ^ 2 * dz (dz (zoomVRec lam h rc zc u)) p
        - dr (dz (zoomWRec lam h rc zc u)) p) = dz (zoomTheta lam h rc zc u) p := by
    rw [dz_zoomTheta_eq lam h rc zc hlam u hu p hp]
  simpa [h_target] using h_combined.congr_of_eventuallyEq h_event2

/-! ### Pointwise derivative bounds -/

theorem abs_dr_zoomTheta_le_const {C h lam rc zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2) (hdelta : lam ^ (2 * h) ≤ 1)
    {p : (ℝ × ℝ) × ℝ} (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (htau : p.2 ≤ -1) :
    |dr (zoomTheta lam h rc zc u) p| ≤ 4 * C := by
  have hsum := abs_dr_zoomTheta_add_abs_dz_zoomTheta_le hlam hb hu hC hh0 hh1 hdelta hp htau
  have h_nonneg_dz : 0 ≤ |dz (zoomTheta lam h rc zc u) p| := abs_nonneg _
  have h_bound : (-p.2) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    have h_base : (1 : ℝ) ≤ -p.2 := by linarith only [htau]
    calc
      (-p.2) ^ (-(1 / 2 : ℝ)) ≤ (-p.2) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h_base (by linarith only)
      _ = 1 := by rw [Real.rpow_zero (-p.2)]
  have h_rhs : 4 * C * (-p.2) ^ (-(1 / 2 : ℝ)) ≤ 4 * C := by
    nlinarith only [h_bound, hC]
  linarith only [hsum, h_nonneg_dz, h_rhs]

theorem abs_dz_zoomTheta_le_const {C h lam rc zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2) (hdelta : lam ^ (2 * h) ≤ 1)
    {p : (ℝ × ℝ) × ℝ} (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (htau : p.2 ≤ -1) :
    |dz (zoomTheta lam h rc zc u) p| ≤ 4 * C := by
  have hsum := abs_dr_zoomTheta_add_abs_dz_zoomTheta_le hlam hb hu hC hh0 hh1 hdelta hp htau
  have h_nonneg_dr : 0 ≤ |dr (zoomTheta lam h rc zc u) p| := abs_nonneg _
  have h_bound : (-p.2) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    have h_base : (1 : ℝ) ≤ -p.2 := by linarith only [htau]
    calc
      (-p.2) ^ (-(1 / 2 : ℝ)) ≤ (-p.2) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h_base (by linarith only)
      _ = 1 := by rw [Real.rpow_zero (-p.2)]
  have h_rhs : 4 * C * (-p.2) ^ (-(1 / 2 : ℝ)) ≤ 4 * C := by
    nlinarith only [h_bound, hC]
  linarith only [hsum, h_nonneg_dr, h_rhs]

/-! ### Lipschitz-in-space bound -/

theorem lipschitzOnWith_zoomTheta {C h lam rc zc Ra Rb Za Zb tau : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2) (hdelta : lam ^ (2 * h) ≤ 1) (htau : tau ≤ -1)
    (hmem : ∀ y ∈ Icc Ra Rb ×ˢ Icc Za Zb, zoomPointRec lam h rc zc (y, tau) ∈ unitCylinder) :
    LipschitzOnWith (Real.toNNReal (8 * C))
      (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, tau)) (Icc Ra Rb ×ˢ Icc Za Zb) := by
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by norm_num)
  have hL : (0 : ℝ) ≤ 8 * C := mul_nonneg (by norm_num) hC
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro y1 hy1 y2 hy2
  rw [Real.coe_toNNReal _ hL, Real.dist_eq]
  have h_dr_bound (r : ℝ) (hr : r ∈ Icc Ra Rb) :
      |dr (zoomTheta lam h rc zc u) ((r, y1.2), tau)| ≤ 4 * C := by
    have hp : zoomPointRec lam h rc zc ((r, y1.2), tau) ∈ unitCylinder :=
      hmem (r, y1.2) ⟨hr, hy1.2⟩
    exact abs_dr_zoomTheta_le_const hlam hb hu hC hh0 hh1 hdelta hp htau
  have h_dz_bound (s : ℝ) (hs : s ∈ Icc Za Zb) :
      |dz (zoomTheta lam h rc zc u) ((y2.1, s), tau)| ≤ 4 * C := by
    have hp : zoomPointRec lam h rc zc ((y2.1, s), tau) ∈ unitCylinder :=
      hmem (y2.1, s) ⟨hy2.1, hs⟩
    exact abs_dz_zoomTheta_le_const hlam hb hu hC hh0 hh1 hdelta hp htau
  have hedgeR : |zoomTheta lam h rc zc u ((y2.1, y1.2), tau)
      - zoomTheta lam h rc zc u ((y1.1, y1.2), tau)|
      ≤ (4 * C) * |y2.1 - y1.1| := by
    have hderiv : ∀ r ∈ Icc Ra Rb,
        HasDerivWithinAt (fun r' : ℝ => zoomTheta lam h rc zc u ((r', y1.2), tau))
          (dr (zoomTheta lam h rc zc u) ((r, y1.2), tau)) (Icc Ra Rb) r := by
      intro r hr
      have hp : zoomPointRec lam h rc zc ((r, y1.2), tau) ∈ unitCylinder :=
        hmem (r, y1.2) ⟨hr, hy1.2⟩
      have h_hasDeriv : HasDerivAt (fun r' : ℝ => zoomTheta lam h rc zc u ((r', y1.2), tau))
          (dr (zoomTheta lam h rc zc u) ((r, y1.2), tau)) r :=
        hasDerivAt_dr_zoomTheta lam h rc zc hlam u hu ((r, y1.2), tau) hp
      exact h_hasDeriv.hasDerivWithinAt
    have hbound : ∀ r ∈ Icc Ra Rb,
        ‖dr (zoomTheta lam h rc zc u) ((r, y1.2), tau)‖ ≤ 4 * C := by
      intro r hr
      rw [Real.norm_eq_abs]
      exact h_dr_bound r hr
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Icc Ra Rb) hy1.1 hy2.1
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    exact hmvt
  have hedgeZ : |zoomTheta lam h rc zc u ((y2.1, y2.2), tau)
      - zoomTheta lam h rc zc u ((y2.1, y1.2), tau)|
      ≤ (4 * C) * |y2.2 - y1.2| := by
    have hderiv : ∀ s ∈ Icc Za Zb,
        HasDerivWithinAt (fun s' : ℝ => zoomTheta lam h rc zc u ((y2.1, s'), tau))
          (dz (zoomTheta lam h rc zc u) ((y2.1, s), tau)) (Icc Za Zb) s := by
      intro s hs
      have hp : zoomPointRec lam h rc zc ((y2.1, s), tau) ∈ unitCylinder :=
        hmem (y2.1, s) ⟨hy2.1, hs⟩
      have h_hasDeriv : HasDerivAt (fun s' : ℝ => zoomTheta lam h rc zc u ((y2.1, s'), tau))
          (dz (zoomTheta lam h rc zc u) ((y2.1, s), tau)) s :=
        hasDerivAt_dz_zoomTheta lam h rc zc hlam u hu ((y2.1, s), tau) hp
      exact h_hasDeriv.hasDerivWithinAt
    have hbound : ∀ s ∈ Icc Za Zb,
        ‖dz (zoomTheta lam h rc zc u) ((y2.1, s), tau)‖ ≤ 4 * C := by
      intro s hs
      rw [Real.norm_eq_abs]
      exact h_dz_bound s hs
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Icc Za Zb) hy1.2 hy2.2
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    exact hmvt
  have h_tri : |zoomTheta lam h rc zc u (y1, tau) - zoomTheta lam h rc zc u (y2, tau)|
      ≤ |zoomTheta lam h rc zc u (y1, tau) - zoomTheta lam h rc zc u ((y2.1, y1.2), tau)|
        + |zoomTheta lam h rc zc u ((y2.1, y1.2), tau) - zoomTheta lam h rc zc u (y2, tau)| :=
    abs_sub_le _ _ _
  have h_sym1 : |zoomTheta lam h rc zc u (y1, tau) - zoomTheta lam h rc zc u ((y2.1, y1.2), tau)|
      = |zoomTheta lam h rc zc u ((y2.1, y1.2), tau) - zoomTheta lam h rc zc u (y1, tau)| :=
    abs_sub_comm _ _
  have h_sym2 : |zoomTheta lam h rc zc u ((y2.1, y1.2), tau) - zoomTheta lam h rc zc u (y2, tau)|
      = |zoomTheta lam h rc zc u (y2, tau) - zoomTheta lam h rc zc u ((y2.1, y1.2), tau)| :=
    abs_sub_comm _ _
  have hd1 : |y2.1 - y1.1| ≤ dist y1 y2 := by
    have hcomp : dist y1.1 y2.1 = |y2.1 - y1.1| := by rw [Real.dist_eq, abs_sub_comm]
    rw [Prod.dist_eq, ← hcomp]
    exact le_max_left _ _
  have hd2 : |y2.2 - y1.2| ≤ dist y1 y2 := by
    have hcomp : dist y1.2 y2.2 = |y2.2 - y1.2| := by rw [Real.dist_eq, abs_sub_comm]
    rw [Prod.dist_eq, ← hcomp]
    exact le_max_right _ _
  have h_et1 : ((y1.1, y1.2) : ℝ × ℝ) = y1 := rfl
  have h_et2 : ((y2.1, y2.2) : ℝ × ℝ) = y2 := rfl
  rw [h_et1] at hedgeR
  rw [h_et2] at hedgeZ
  have hstep1 : (4 * C) * |y2.1 - y1.1| ≤ (4 * C) * dist y1 y2 :=
    mul_le_mul_of_nonneg_left hd1 (mul_nonneg (by norm_num) hC)
  have hstep2 : (4 * C) * |y2.2 - y1.2| ≤ (4 * C) * dist y1 y2 :=
    mul_le_mul_of_nonneg_left hd2 (mul_nonneg (by norm_num) hC)
  calc
    |zoomTheta lam h rc zc u (y1, tau) - zoomTheta lam h rc zc u (y2, tau)|
        ≤ |zoomTheta lam h rc zc u (y1, tau) - zoomTheta lam h rc zc u ((y2.1, y1.2), tau)|
          + |zoomTheta lam h rc zc u ((y2.1, y1.2), tau) - zoomTheta lam h rc zc u (y2, tau)| :=
            h_tri
    _ = |zoomTheta lam h rc zc u ((y2.1, y1.2), tau) - zoomTheta lam h rc zc u (y1, tau)|
          + |zoomTheta lam h rc zc u (y2, tau) - zoomTheta lam h rc zc u ((y2.1, y1.2), tau)| := by
      rw [h_sym1, h_sym2]
    _ ≤ (4 * C) * |y2.1 - y1.1| + (4 * C) * |y2.2 - y1.2| :=
      add_le_add hedgeR hedgeZ
    _ ≤ (4 * C) * dist y1 y2 + (4 * C) * dist y1 y2 :=
      add_le_add hstep1 hstep2
    _ = 2 * (4 * C) * dist y1 y2 := by ring
    _ = (8 * C) * dist y1 y2 := by ring

end CIV
