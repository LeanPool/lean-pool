/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.ThetaLipschitz
public import LeanPool.CIVAxisymmetric.Zoom.VRecBoundedRectangle
public import LeanPool.CIVAxisymmetric.Zoom.OmegaEquicontinuous

/-!
# Receding Transport Pairing Bound

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- The recentred zoom point restricted to a fixed time `τ`, as a map of the meridional
plane alone, is smooth. -/
private theorem contDiff_zoomPointRec_atTau_transport (lam h rc zc τ : ℝ) :
    ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomPointRec lam h rc zc (y, τ)) :=
  (contDiff_zoomPointRec lam h rc zc).comp (contDiff_id.prodMk contDiff_const)

/-- The domain on which the recentred zoom point at a fixed time `τ` lies in the unit
cylinder is open. -/
private theorem isOpen_transportDomain (lam h rc zc τ : ℝ) :
    IsOpen {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} :=
  (isOpen_zoomPointRec_preimage lam h rc zc).preimage (continuous_id.prodMk continuous_const)

/-- `Θ_n(·, τ)` is smooth on its natural domain. -/
private theorem contDiffOn_zoomTheta_slice {lam h rc zc τ : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} := by
  have hζ := contDiff_zoomPointRec_atTau_transport lam h rc zc τ
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => azimuthalVorticity u (zoomPointRec lam h rc zc (y, τ)))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} :=
    (contDiffOn_azimuthalVorticity hu).comp hζ.contDiffOn (fun y hy => hy)
  have heq : (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ))
      = fun y : ℝ × ℝ =>
        lam ^ 2 * lam ^ (2 * h) * azimuthalVorticity u (zoomPointRec lam h rc zc (y, τ)) := by
    funext y; rfl
  rw [heq]
  exact hcomp.const_smul (lam ^ 2 * lam ^ (2 * h))

/-- `V_n(·, τ)` is smooth on its natural domain. -/
private theorem contDiffOn_zoomVRec_slice {lam h rc zc τ : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomVRec lam h rc zc u (y, τ))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} := by
  have hζ := contDiff_zoomPointRec_atTau_transport lam h rc zc τ
  have hu0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z 0) unitCylinder := contDiffOn_pi.1 hu 0
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => u (zoomPointRec lam h rc zc (y, τ)) 0)
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} :=
    hu0.comp hζ.contDiffOn (fun y hy => hy)
  have heq : (fun y : ℝ × ℝ => zoomVRec lam h rc zc u (y, τ))
      = fun y : ℝ × ℝ => lam * u (zoomPointRec lam h rc zc (y, τ)) 0 := by
    funext y; rfl
  rw [heq]
  exact hcomp.const_smul lam

/-- `W_n(·, τ)` is smooth on its natural domain. -/
private theorem contDiffOn_zoomWRec_slice {lam h rc zc τ : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomWRec lam h rc zc u (y, τ))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} := by
  have hζ := contDiff_zoomPointRec_atTau_transport lam h rc zc τ
  have hu2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z 2) unitCylinder := contDiffOn_pi.1 hu 2
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => u (zoomPointRec lam h rc zc (y, τ)) 2)
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} :=
    hu2.comp hζ.contDiffOn (fun y hy => hy)
  have heq : (fun y : ℝ × ℝ => zoomWRec lam h rc zc u (y, τ))
      = fun y : ℝ × ℝ => lam * lam ^ (2 * h) * u (zoomPointRec lam h rc zc (y, τ)) 2 := by
    funext y; rfl
  rw [heq]
  exact hcomp.const_smul (lam * lam ^ (2 * h))

/-- The derivative of the first slice of a differentiable function of `ℝ × ℝ` is the first
directional derivative, the local copy of the private helper of
`CIV.Zoom.OmegaEquicontinuous`. -/
private theorem hasDerivAt_slice_fst_local' {F : ℝ × ℝ → ℝ} {y : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F y) :
    HasDerivAt (fun t : ℝ => F (t, y.2)) (fderiv ℝ F y (1, 0)) y.1 := by
  have hline : HasDerivAt (fun t : ℝ => (t, y.2)) ((1 : ℝ), (0 : ℝ)) y.1 :=
    (hasDerivAt_id y.1).prodMk (hasDerivAt_const y.1 y.2)
  exact HasFDerivAt.comp_hasDerivAt_of_eq (hl := hF.hasFDerivAt) (hf := hline) (hy := rfl)

/-- The derivative of the second slice of a differentiable function of `ℝ × ℝ` is the second
directional derivative, the local copy of the private helper of
`CIV.Zoom.OmegaEquicontinuous`. -/
private theorem hasDerivAt_slice_snd_local' {F : ℝ × ℝ → ℝ} {y : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F y) :
    HasDerivAt (fun s : ℝ => F (y.1, s)) (fderiv ℝ F y (0, 1)) y.2 := by
  have hline : HasDerivAt (fun s : ℝ => (y.1, s)) ((0 : ℝ), (1 : ℝ)) y.2 :=
    (hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2)
  exact HasFDerivAt.comp_hasDerivAt_of_eq (hl := hF.hasFDerivAt) (hf := hline) (hy := rfl)

/-- `V_n` is bounded by `C` for `τ ≤ -1`, from `abs_zoomVRec_le`. -/
private theorem abs_zoomVRec_le_const {C h lam rc zc τ : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) {y : ℝ × ℝ}
    (hp : zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder) (htau : τ ≤ -1) :
    |zoomVRec lam h rc zc u (y, τ)| ≤ C := by
  have hbound := abs_zoomVRec_le C h lam rc zc hlam u hb (y, τ) hp
  have hexp : (-(1 / 2 : ℝ) - 0 / 2 - (1 / 2 - h) * 0) = -(1 / 2 : ℝ) := by ring
  rw [hexp] at hbound
  have hτge1 : (1 : ℝ) ≤ -τ := by linarith only [htau]
  have hpow : (-τ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    calc (-τ) ^ (-(1 / 2 : ℝ)) ≤ (-τ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hτge1 (by norm_num)
      _ = 1 := Real.rpow_zero _
  calc |zoomVRec lam h rc zc u (y, τ)| ≤ C * (-τ) ^ (-(1 / 2 : ℝ)) := hbound
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpow hC
    _ = C := mul_one C

/-- `W_n` is bounded by `C` for `τ ≤ -1`, from `abs_zoomWRec_add_abs_zoomSRec_le`. -/
private theorem abs_zoomWRec_le_const {C h lam rc zc τ : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hlam : 0 < lam) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u) {y : ℝ × ℝ}
    (hp : zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder) (htau : τ ≤ -1) :
    |zoomWRec lam h rc zc u (y, τ)| ≤ C := by
  have hbound := abs_zoomWRec_add_abs_zoomSRec_le C h lam rc zc hlam u hb (y, τ) hp
  have hexp : (-(1 / 2 : ℝ) - h - 0 / 2 - (1 / 2 - h) * 0) = -(1 / 2 : ℝ) - h := by ring
  rw [hexp] at hbound
  have hτge1 : (1 : ℝ) ≤ -τ := by linarith only [htau]
  have hpow : (-τ) ^ (-(1 / 2 : ℝ) - h) ≤ 1 := by
    calc (-τ) ^ (-(1 / 2 : ℝ) - h) ≤ (-τ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hτge1 (by linarith only [hh0])
      _ = 1 := Real.rpow_zero _
  have hSnn : (0 : ℝ) ≤ |zoomSRec lam h rc zc u (y, τ)| := abs_nonneg _
  have hWle : |zoomWRec lam h rc zc u (y, τ)| ≤ C * (-τ) ^ (-(1 / 2 : ℝ) - h) := by
    linarith only [hbound, hSnn]
  calc |zoomWRec lam h rc zc u (y, τ)| ≤ C * (-τ) ^ (-(1 / 2 : ℝ) - h) := hWle
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpow hC
    _ = C := mul_one C

/-- `Θ_n` is bounded by `2C` for `τ ≤ -1` and `δ ≤ 1`, from `abs_zoomTheta_le`. -/
private theorem abs_zoomTheta_le_const' {C h lam rc zc τ : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hh1 : h ≤ 1 / 2) (hlam : 0 < lam) (hdelta : lam ^ (2 * h) ≤ 1)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder) {y : ℝ × ℝ}
    (hp : zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder) (htau : τ ≤ -1) :
    |zoomTheta lam h rc zc u (y, τ)| ≤ 2 * C := by
  have hΘ := abs_zoomTheta_le C h lam rc zc hlam u hb hu (y, τ) hp
  have hτpos : (0 : ℝ) < -τ := by linarith only [htau]
  have hτge1 : (1 : ℝ) ≤ -τ := by linarith only [htau]
  have hδnn : (0 : ℝ) ≤ lam ^ (2 * h) := Real.rpow_nonneg hlam.le _
  have hδsq : (lam ^ (2 * h)) ^ 2 ≤ 1 := by nlinarith only [hδnn, hdelta]
  have hpow1 : (-τ) ^ (-1 + h : ℝ) ≤ 1 := by
    calc (-τ) ^ (-1 + h : ℝ) ≤ (-τ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hτge1 (by linarith only [hh1])
      _ = 1 := Real.rpow_zero _
  have hpow2 : (-τ) ^ (-1 - h : ℝ) ≤ 1 := by
    calc (-τ) ^ (-1 - h : ℝ) ≤ (-τ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hτge1 (by linarith only [hh0])
      _ = 1 := Real.rpow_zero _
  have hpow1nn : (0 : ℝ) ≤ (-τ) ^ (-1 + h : ℝ) := Real.rpow_nonneg hτpos.le _
  have hstep : (lam ^ (2 * h)) ^ 2 * (-τ) ^ (-1 + h : ℝ) + (-τ) ^ (-1 - h : ℝ) ≤ 1 + 1 := by
    have h1 : (lam ^ (2 * h)) ^ 2 * (-τ) ^ (-1 + h : ℝ) ≤ 1 * 1 :=
      mul_le_mul hδsq hpow1 hpow1nn (by norm_num)
    nlinarith only [h1, hpow2]
  have hfin : C * ((lam ^ (2 * h)) ^ 2 * (-τ) ^ (-1 + h : ℝ) + (-τ) ^ (-1 - h : ℝ)) ≤ C * (1 + 1) :=
    mul_le_mul_of_nonneg_left hstep hC
  have heq2 : C * (1 + 1) = 2 * C := by ring
  linarith only [hΘ, hfin, heq2]

/-- The product of a function continuous on an open set with a continuous function whose
support closes inside that set is continuous on the whole plane, the local copy of the
private helper of `CIV.Zoom.OmegaEquicontinuous`. -/
private theorem continuous_mul_of_tsupport_subset_local {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {a b : ℝ × ℝ → ℝ} (ha : ContinuousOn a U) (hb : Continuous b) (hbU : tsupport b ⊆ U) :
    Continuous fun y => a y * b y := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ tsupport b
  · exact (ha.continuousAt (hU.mem_nhds (hbU hy))).mul hb.continuousAt
  · have hopen : IsOpen (tsupport b)ᶜ := (isClosed_tsupport b).isOpen_compl
    have hev : (fun y => a y * b y) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hy] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
    exact ContinuousAt.congr continuousAt_const hev.symm

/-- The transport/divergence-term pairing bound at a fixed zoom scale: the integral of
`−(∂_R(V_nΘ_n) + ∂_Z(W_nΘ_n))`, the perfect-divergence transport term of
`zoomTheta_pde_divergenceForm`, against a test function supported in the interior of a
compact set `K` is bounded by `4C²` times the bound `B` on `ψ` and its first two
derivatives, times the volume of `K`. -/
theorem transport_term_pairing_bound_fixed {C h lam rc zc : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hh1 : h ≤ 1 / 2) (hlam : 0 < lam) (hdelta : lam ^ (2 * h) ≤ 1)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {τ : ℝ} (htau : τ ≤ -1)
    (hmem : ∀ y ∈ K, zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ interior K) (B : ℝ) (_ : 0 ≤ B)
    (hψB : ∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) :
    |∫ y : ℝ × ℝ,
        (-(dr (fun q : (ℝ × ℝ) × ℝ => zoomVRec lam h rc zc u q * zoomTheta lam h rc zc u q)
              (y, τ)
            + dz (fun q : (ℝ × ℝ) × ℝ => zoomWRec lam h rc zc u q * zoomTheta lam h rc zc u q)
              (y, τ))) * ψ y|
      ≤ 4 * C ^ 2 * (volume K).toReal * B := by
  set D : Set (ℝ × ℝ) := {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} with hD_def
  set F1 : ℝ × ℝ → ℝ := fun y => zoomVRec lam h rc zc u (y, τ) * zoomTheta lam h rc zc u (y, τ)
    with hF1_def
  set F2 : ℝ × ℝ → ℝ := fun y => zoomWRec lam h rc zc u (y, τ) * zoomTheta lam h rc zc u (y, τ)
    with hF2_def
  set Gp1 : ℝ × ℝ → ℝ := fun y => fderiv ℝ F1 y (1, 0) with hGp1_def
  set Gp2 : ℝ × ℝ → ℝ := fun y => fderiv ℝ F2 y (0, 1) with hGp2_def
  have hDopen : IsOpen D := isOpen_transportDomain lam h rc zc τ
  have hUsubK : interior K ⊆ K := interior_subset
  have hUD : interior K ⊆ D := fun y hy => hmem y (hUsubK hy)
  have hΘsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ)) D :=
    contDiffOn_zoomTheta_slice hu
  have hVsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomVRec lam h rc zc u (y, τ)) D :=
    contDiffOn_zoomVRec_slice hu
  have hWsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomWRec lam h rc zc u (y, τ)) D :=
    contDiffOn_zoomWRec_slice hu
  have hF1smooth : ContDiffOn ℝ (⊤ : ℕ∞) F1 D := hVsmooth.mul hΘsmooth
  have hF2smooth : ContDiffOn ℝ (⊤ : ℕ∞) F2 D := hWsmooth.mul hΘsmooth
  have hF1cont : ContinuousOn F1 (interior K) := hF1smooth.continuousOn.mono hUD
  have hF2cont : ContinuousOn F2 (interior K) := hF2smooth.continuousOn.mono hUD
  have hGp1cont : ContinuousOn Gp1 (interior K) := by
    have hcomp : ContinuousOn
        (fun y : ℝ × ℝ => (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)) (fderiv ℝ F1 y)) D :=
      (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).continuous.comp_continuousOn
        ((hF1smooth.fderiv_of_isOpen (m := 0) hDopen (by norm_num)).continuousOn)
    exact hcomp.mono hUD
  have hGp2cont : ContinuousOn Gp2 (interior K) := by
    have hcomp : ContinuousOn
        (fun y : ℝ × ℝ => (ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)) (fderiv ℝ F2 y)) D :=
      (ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).continuous.comp_continuousOn
        ((hF2smooth.fderiv_of_isOpen (m := 0) hDopen (by norm_num)).continuousOn)
    exact hcomp.mono hUD
  have hF1deriv : ∀ y ∈ interior K, HasDerivAt (fun t : ℝ => F1 (t, y.2)) (Gp1 y) y.1 := by
    intro y hy
    have hFdiff : DifferentiableAt ℝ F1 y :=
      (hF1smooth.differentiableOn (by norm_num) y (hUD hy)).differentiableAt
        (hDopen.mem_nhds (hUD hy))
    exact hasDerivAt_slice_fst_local' hFdiff
  have hF2deriv : ∀ y ∈ interior K, HasDerivAt (fun s : ℝ => F2 (y.1, s)) (Gp2 y) y.2 := by
    intro y hy
    have hFdiff : DifferentiableAt ℝ F2 y :=
      (hF2smooth.differentiableOn (by norm_num) y (hUD hy)).differentiableAt
        (hDopen.mem_nhds (hUD hy))
    exact hasDerivAt_slice_snd_local' hFdiff
  have hIBP1 := integral_partial_fst_mul_eq_neg (isOpen_interior (s := K)) hF1cont hGp1cont
    hF1deriv hψ hψc hψU
  have hIBP2 := integral_partial_snd_mul_eq_neg (isOpen_interior (s := K)) hF2cont hGp2cont
    hF2deriv hψ hψc hψU
  have hGp1_eq : ∀ y ∈ K, Gp1 y =
      dr (fun q : (ℝ × ℝ) × ℝ => zoomVRec lam h rc zc u q * zoomTheta lam h rc zc u q) (y, τ) := by
    intro y hy
    have hFdiff : DifferentiableAt ℝ F1 y :=
      (hF1smooth.differentiableOn (by norm_num) y (hmem y hy)).differentiableAt
        (hDopen.mem_nhds (hmem y hy))
    exact (hasDerivAt_slice_fst_local' hFdiff).deriv.symm
  have hGp2_eq : ∀ y ∈ K, Gp2 y =
      dz (fun q : (ℝ × ℝ) × ℝ => zoomWRec lam h rc zc u q * zoomTheta lam h rc zc u q) (y, τ) := by
    intro y hy
    have hFdiff : DifferentiableAt ℝ F2 y :=
      (hF2smooth.differentiableOn (by norm_num) y (hmem y hy)).differentiableAt
        (hDopen.mem_nhds (hmem y hy))
    exact (hasDerivAt_slice_snd_local' hFdiff).deriv.symm
  have hpointwise : ∀ y : ℝ × ℝ,
      (-(dr (fun q : (ℝ × ℝ) × ℝ => zoomVRec lam h rc zc u q * zoomTheta lam h rc zc u q) (y, τ)
          + dz (fun q : (ℝ × ℝ) × ℝ => zoomWRec lam h rc zc u q * zoomTheta lam h rc zc u q)
            (y, τ))) * ψ y
        = -(Gp1 y * ψ y) - Gp2 y * ψ y := by
    intro y
    by_cases hyK : y ∈ K
    · rw [hGp1_eq y hyK, hGp2_eq y hyK]; ring
    · have hynotsupp : y ∉ tsupport ψ := fun hcontra => hyK (hUsubK (hψU hcontra))
      rw [image_eq_zero_of_notMem_tsupport hynotsupp]; ring
  have hslice1 : ∀ y : ℝ × ℝ,
      HasDerivAt (fun t : ℝ => ψ (t, y.2)) (fderiv ℝ ψ y (1, 0)) y.1 := fun y =>
    hasDerivAt_slice_fst_local' (hψ.differentiable (by simp) y)
  have hslice2 : ∀ y : ℝ × ℝ,
      HasDerivAt (fun s : ℝ => ψ (y.1, s)) (fderiv ℝ ψ y (0, 1)) y.2 := fun y =>
    hasDerivAt_slice_snd_local' (hψ.differentiable (by simp) y)
  have hψ1cont : Continuous fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ2cont : Continuous fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ1supp : tsupport (fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0)) ⊆ tsupport ψ :=
    tsupport_fderiv_apply_subset ℝ (1, 0)
  have hψ2supp : tsupport (fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1)) ⊆ tsupport ψ :=
    tsupport_fderiv_apply_subset ℝ (0, 1)
  have hψ1c : HasCompactSupport fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0) :=
    hψc.of_isClosed_subset (isClosed_tsupport _) hψ1supp
  have hψ2c : HasCompactSupport fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1) :=
    hψc.of_isClosed_subset (isClosed_tsupport _) hψ2supp
  have hint_Gp1ψ : MeasureTheory.Integrable fun y : ℝ × ℝ => Gp1 y * ψ y :=
    (continuous_mul_of_tsupport_subset_local (isOpen_interior (s := K)) hGp1cont hψ.continuous
      hψU).integrable_of_hasCompactSupport hψc.mul_left
  have hint_Gp2ψ : MeasureTheory.Integrable fun y : ℝ × ℝ => Gp2 y * ψ y :=
    (continuous_mul_of_tsupport_subset_local (isOpen_interior (s := K)) hGp2cont hψ.continuous
      hψU).integrable_of_hasCompactSupport hψc.mul_left
  have hintegral_eq : (∫ y : ℝ × ℝ,
      (-(dr (fun q : (ℝ × ℝ) × ℝ => zoomVRec lam h rc zc u q * zoomTheta lam h rc zc u q) (y, τ)
          + dz (fun q : (ℝ × ℝ) × ℝ => zoomWRec lam h rc zc u q * zoomTheta lam h rc zc u q)
            (y, τ))) * ψ y)
      = -(∫ y : ℝ × ℝ, Gp1 y * ψ y) - ∫ y : ℝ × ℝ, Gp2 y * ψ y := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpointwise)]
    have hstep : (∫ a : ℝ × ℝ, -(Gp1 a * ψ a) - Gp2 a * ψ a)
        = (∫ a : ℝ × ℝ, -(Gp1 a * ψ a)) - ∫ a : ℝ × ℝ, Gp2 a * ψ a :=
      integral_sub hint_Gp1ψ.neg hint_Gp2ψ
    rw [hstep, integral_neg]
  rw [hintegral_eq, hIBP1, hIBP2]
  have hF1bound : ∀ y ∈ K, |F1 y| ≤ 2 * C ^ 2 := by
    intro y hy
    have hV := abs_zoomVRec_le_const hC hlam hb (hmem y hy) htau
    have hΘ := abs_zoomTheta_le_const' hC hh0 hh1 hlam hdelta hb (hu.of_le (by norm_num))
      (hmem y hy) htau
    calc |F1 y| = |zoomVRec lam h rc zc u (y, τ)| * |zoomTheta lam h rc zc u (y, τ)| :=
          abs_mul _ _
      _ ≤ C * (2 * C) := mul_le_mul hV hΘ (abs_nonneg _) hC
      _ = 2 * C ^ 2 := by ring
  have hF2bound : ∀ y ∈ K, |F2 y| ≤ 2 * C ^ 2 := by
    intro y hy
    have hW := abs_zoomWRec_le_const hC hh0 hlam hb (hmem y hy) htau
    have hΘ := abs_zoomTheta_le_const' hC hh0 hh1 hlam hdelta hb (hu.of_le (by norm_num))
      (hmem y hy) htau
    calc |F2 y| = |zoomWRec lam h rc zc u (y, τ)| * |zoomTheta lam h rc zc u (y, τ)| :=
          abs_mul _ _
      _ ≤ C * (2 * C) := mul_le_mul hW hΘ (abs_nonneg _) hC
      _ = 2 * C ^ 2 := by ring
  have hψ1_bound : ∀ y, |fderiv ℝ ψ y (1, 0)| ≤ B := by
    intro y
    have hle : ‖fderiv ℝ ψ y (1, 0)‖ ≤ ‖fderiv ℝ ψ y‖ * ‖((1, 0) : ℝ × ℝ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hnorm1 : ‖((1, 0) : ℝ × ℝ)‖ = 1 := by rw [Prod.norm_def]; norm_num
    rw [hnorm1, mul_one] at hle
    calc |fderiv ℝ ψ y (1, 0)| = ‖fderiv ℝ ψ y (1, 0)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ ψ y‖ := hle
      _ ≤ B := (hψB y).2.1
  have hψ2_bound : ∀ y, |fderiv ℝ ψ y (0, 1)| ≤ B := by
    intro y
    have hle : ‖fderiv ℝ ψ y (0, 1)‖ ≤ ‖fderiv ℝ ψ y‖ * ‖((0, 1) : ℝ × ℝ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hnorm1 : ‖((0, 1) : ℝ × ℝ)‖ = 1 := by rw [Prod.norm_def]; norm_num
    rw [hnorm1, mul_one] at hle
    calc |fderiv ℝ ψ y (0, 1)| = ‖fderiv ℝ ψ y (0, 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ ψ y‖ := hle
      _ ≤ B := (hψB y).2.1
  have hbound1 := abs_integral_mul_le_of_tsupport_subset hK.measure_lt_top
    (hψ1supp.trans (hψU.trans hUsubK)) hF1bound hψ1_bound
  have hbound2 := abs_integral_mul_le_of_tsupport_subset hK.measure_lt_top
    (hψ2supp.trans (hψU.trans hUsubK)) hF2bound hψ2_bound
  calc |-(-∫ y : ℝ × ℝ, F1 y * deriv (fun t : ℝ => ψ (t, y.2)) y.1)
        - -∫ y : ℝ × ℝ, F2 y * deriv (fun s : ℝ => ψ (y.1, s)) y.2|
      = |(∫ y : ℝ × ℝ, F1 y * deriv (fun t : ℝ => ψ (t, y.2)) y.1)
          + ∫ y : ℝ × ℝ, F2 y * deriv (fun s : ℝ => ψ (y.1, s)) y.2| := by ring_nf
    _ ≤ |∫ y : ℝ × ℝ, F1 y * deriv (fun t : ℝ => ψ (t, y.2)) y.1|
          + |∫ y : ℝ × ℝ, F2 y * deriv (fun s : ℝ => ψ (y.1, s)) y.2| := abs_add_le _ _
    _ ≤ 2 * C ^ 2 * B * (volume K).toReal + 2 * C ^ 2 * B * (volume K).toReal := by
        have h1 : (fun y : ℝ × ℝ => F1 y * deriv (fun t : ℝ => ψ (t, y.2)) y.1)
            = fun y => F1 y * fderiv ℝ ψ y (1, 0) := funext (fun y => by rw [(hslice1 y).deriv])
        have h2 : (fun y : ℝ × ℝ => F2 y * deriv (fun s : ℝ => ψ (y.1, s)) y.2)
            = fun y => F2 y * fderiv ℝ ψ y (0, 1) := funext (fun y => by rw [(hslice2 y).deriv])
        rw [h1, h2]
        exact add_le_add hbound1 hbound2
    _ = 4 * C ^ 2 * (volume K).toReal * B := by ring

/-- The eventual-in-`n` pairing bound for the transport/divergence term: `C₀ := 4C²` is
chosen before `n`, matching the eventual form of the time-pairing estimate `hpair`. -/
theorem transport_term_pairing_bound {C h : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2)
    {rc zc : ℝ} (lam : ℕ → ℝ) (hlam_pos : ∀ n, 0 < lam n)
    (hlam_le : ∀ᶠ n in atTop, lam n ^ (2 * h) ≤ 1)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {τ : ℝ} (htau : τ ≤ -1)
    (hmem : ∀ᶠ n in atTop, ∀ y ∈ K, zoomPointRec (lam n) h rc zc (y, τ) ∈ unitCylinder) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ interior K →
      ∀ B : ℝ, 0 ≤ B →
        (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
        ∀ᶠ n in atTop,
          |∫ y : ℝ × ℝ,
              (-(dr (fun q : (ℝ × ℝ) × ℝ =>
                      zoomVRec (lam n) h rc zc u q * zoomTheta (lam n) h rc zc u q) (y, τ)
                  + dz (fun q : (ℝ × ℝ) × ℝ =>
                      zoomWRec (lam n) h rc zc u q * zoomTheta (lam n) h rc zc u q) (y, τ)))
                * ψ y|
            ≤ C₀ * B := by
  refine ⟨4 * C ^ 2 * (volume K).toReal, by positivity, fun ψ hψ hψc hψU B hB hψB => ?_⟩
  filter_upwards [hlam_le, hmem] with n hlam_len hmem_n
  exact transport_term_pairing_bound_fixed hC hh0 hh1 (hlam_pos n) hlam_len hb hu hK htau hmem_n ψ
    hψ hψc hψU B hB hψB

end CIV
