/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.ThetaLipschitz
public import LeanPool.CIVAxisymmetric.Zoom.OmegaEquicontinuous

/-!
# Receding Diffusion Pairing Bound

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- The recentred zoom point restricted to a fixed time `τ` is smooth. -/
private theorem contDiff_zoomPointRec_atTau_diff (lam h rc zc τ : ℝ) :
    ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomPointRec lam h rc zc (y, τ)) :=
  (contDiff_zoomPointRec lam h rc zc).comp (contDiff_id.prodMk contDiff_const)

/-- The domain on which the recentred zoom point at a fixed time `τ` lies in the unit
cylinder is open. -/
private theorem isOpen_diffusionDomain (lam h rc zc τ : ℝ) :
    IsOpen {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} :=
  (isOpen_zoomPointRec_preimage lam h rc zc).preimage (continuous_id.prodMk continuous_const)

/-- `Θ_n(·, τ)` is smooth on its natural domain. -/
private theorem contDiffOn_zoomTheta_slice_diff {lam h rc zc τ : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} := by
  have hζ := contDiff_zoomPointRec_atTau_diff lam h rc zc τ
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

/-- The derivative of the first slice of a differentiable function of `ℝ × ℝ` is the first
directional derivative. -/
private theorem hasDerivAt_slice_fst_diff {F : ℝ × ℝ → ℝ} {y : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F y) :
    HasDerivAt (fun t : ℝ => F (t, y.2)) (fderiv ℝ F y (1, 0)) y.1 := by
  have hline : HasDerivAt (fun t : ℝ => (t, y.2)) ((1 : ℝ), (0 : ℝ)) y.1 :=
    (hasDerivAt_id y.1).prodMk (hasDerivAt_const y.1 y.2)
  exact HasFDerivAt.comp_hasDerivAt_of_eq (hl := hF.hasFDerivAt) (hf := hline) (hy := rfl)

/-- The derivative of the second slice of a differentiable function of `ℝ × ℝ` is the second
directional derivative. -/
private theorem hasDerivAt_slice_snd_diff {F : ℝ × ℝ → ℝ} {y : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F y) :
    HasDerivAt (fun s : ℝ => F (y.1, s)) (fderiv ℝ F y (0, 1)) y.2 := by
  have hline : HasDerivAt (fun s : ℝ => (y.1, s)) ((0 : ℝ), (1 : ℝ)) y.2 :=
    (hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2)
  exact HasFDerivAt.comp_hasDerivAt_of_eq (hl := hF.hasFDerivAt) (hf := hline) (hy := rfl)

/-- `Θ_n` is bounded by `2C` for `τ ≤ -1` and `δ ≤ 1`, from `abs_zoomTheta_le`. -/
private theorem abs_zoomTheta_le_const_diff {C h lam rc zc τ : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
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
support closes inside that set is continuous on the whole plane. -/
private theorem continuous_mul_of_tsupport_subset_diff {U : Set (ℝ × ℝ)} (hU : IsOpen U)
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

/-- `z ↦ fderiv ψ z v` differentiates along the first coordinate to
`fderiv (fderiv ψ) y (1, 0) v`. -/
private theorem hasDerivAt_slice_fst_of_fderiv {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (v : ℝ × ℝ) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => fderiv ℝ ψ (t, y.2) v) (fderiv ℝ (fderiv ℝ ψ) y (1, 0) v) y.1 := by
  have hgdiff : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
  have hFdiff : DifferentiableAt ℝ (fun z : ℝ × ℝ => fderiv ℝ ψ z v) y :=
    ((ContinuousLinearMap.apply ℝ ℝ v).differentiableAt).comp y hgdiff
  have hslice := hasDerivAt_slice_fst_diff hFdiff
  have hcomp : HasFDerivAt (fun z : ℝ × ℝ => fderiv ℝ ψ z v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ ψ) y)) y :=
    (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp y hgdiff.hasFDerivAt
  have hval : fderiv ℝ (fun z : ℝ × ℝ => fderiv ℝ ψ z v) y (1, 0)
      = fderiv ℝ (fderiv ℝ ψ) y (1, 0) v := by
    rw [hcomp.fderiv]; rfl
  rwa [hval] at hslice

/-- `z ↦ fderiv ψ z v` differentiates along the second coordinate to
`fderiv (fderiv ψ) y (0, 1) v`. -/
private theorem hasDerivAt_slice_snd_of_fderiv {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (v : ℝ × ℝ) (y : ℝ × ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ ψ (y.1, s) v) (fderiv ℝ (fderiv ℝ ψ) y (0, 1) v) y.2 := by
  have hgdiff : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
  have hFdiff : DifferentiableAt ℝ (fun z : ℝ × ℝ => fderiv ℝ ψ z v) y :=
    ((ContinuousLinearMap.apply ℝ ℝ v).differentiableAt).comp y hgdiff
  have hslice := hasDerivAt_slice_snd_diff hFdiff
  have hcomp : HasFDerivAt (fun z : ℝ × ℝ => fderiv ℝ ψ z v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ ψ) y)) y :=
    (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp y hgdiff.hasFDerivAt
  have hval : fderiv ℝ (fun z : ℝ × ℝ => fderiv ℝ ψ z v) y (0, 1)
      = fderiv ℝ (fderiv ℝ ψ) y (0, 1) v := by
    rw [hcomp.fderiv]; rfl
  rwa [hval] at hslice

/-- The diffusion-term pairing bound at a fixed zoom scale: the integral of
`∂_R∂_R Θ_n + δ² ∂_Z∂_Z Θ_n`, the diffusion term of `zoomTheta_pde`, against a test
function supported in the interior of a compact set `K` is bounded by `4C` times the
bound `B` on `ψ` and its first two derivatives, times the volume of `K`. -/
theorem diffusion_term_pairing_bound_fixed {C h lam rc zc : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hh1 : h ≤ 1 / 2) (hlam : 0 < lam) (hdelta : lam ^ (2 * h) ≤ 1)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {τ : ℝ} (htau : τ ≤ -1)
    (hmem : ∀ y ∈ K, zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ interior K) (B : ℝ) (hB : 0 ≤ B)
    (hψB : ∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) :
    |∫ y : ℝ × ℝ,
        (dr (dr (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q)) (y, τ)
            + (lam ^ (2 * h)) ^ 2 *
              dz (dz (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q)) (y, τ)) * ψ y|
      ≤ 4 * C * (volume K).toReal * B :=
  by
  set D : Set (ℝ × ℝ) := {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} with hD_def
  set Θs : ℝ × ℝ → ℝ := fun y => zoomTheta lam h rc zc u (y, τ) with hΘs_def
  set Gp1R : ℝ × ℝ → ℝ := fun y => fderiv ℝ Θs y (1, 0) with hGp1R_def
  set Gp2R : ℝ × ℝ → ℝ := fun y => fderiv ℝ Gp1R y (1, 0) with hGp2R_def
  set Gp1Z : ℝ × ℝ → ℝ := fun y => fderiv ℝ Θs y (0, 1) with hGp1Z_def
  set Gp2Z : ℝ × ℝ → ℝ := fun y => fderiv ℝ Gp1Z y (0, 1) with hGp2Z_def
  have hDopen : IsOpen D := isOpen_diffusionDomain lam h rc zc τ
  have hUsubK : interior K ⊆ K := interior_subset
  have hUD : interior K ⊆ D := fun y hy => hmem y (hUsubK hy)
  have hΘsmooth : ContDiffOn ℝ (⊤ : ℕ∞) Θs D := contDiffOn_zoomTheta_slice_diff hu
  have hGp1Rsmooth : ContDiffOn ℝ (⊤ : ℕ∞) Gp1R D :=
    (hΘsmooth.fderiv_of_isOpen hDopen (by norm_num)).clm_apply contDiffOn_const
  have hGp1Zsmooth : ContDiffOn ℝ (⊤ : ℕ∞) Gp1Z D :=
    (hΘsmooth.fderiv_of_isOpen hDopen (by norm_num)).clm_apply contDiffOn_const
  -- continuity of the two second-derivative coefficients
  have hGp2Rcont : ContinuousOn Gp2R (interior K) := by
    have hcomp : ContinuousOn
        (fun y : ℝ × ℝ => (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)) (fderiv ℝ Gp1R y)) D :=
      (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).continuous.comp_continuousOn
        ((hGp1Rsmooth.fderiv_of_isOpen (m := 0) hDopen (by norm_num)).continuousOn)
    exact hcomp.mono hUD
  have hGp2Zcont : ContinuousOn Gp2Z (interior K) := by
    have hcomp : ContinuousOn
        (fun y : ℝ × ℝ => (ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)) (fderiv ℝ Gp1Z y)) D :=
      (ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).continuous.comp_continuousOn
        ((hGp1Zsmooth.fderiv_of_isOpen (m := 0) hDopen (by norm_num)).continuousOn)
    exact hcomp.mono hUD
  have hGp1Rcont : ContinuousOn Gp1R (interior K) := hGp1Rsmooth.continuousOn.mono hUD
  have hGp1Zcont : ContinuousOn Gp1Z (interior K) := hGp1Zsmooth.continuousOn.mono hUD
  -- the two double integrations by parts
  have hGp2Rderiv : ∀ y ∈ interior K, HasDerivAt (fun t : ℝ => Gp1R (t, y.2)) (Gp2R y) y.1 := by
    intro y hy
    have hFdiff : DifferentiableAt ℝ Gp1R y :=
      (hGp1Rsmooth.differentiableOn (by norm_num) y (hUD hy)).differentiableAt
        (hDopen.mem_nhds (hUD hy))
    exact hasDerivAt_slice_fst_diff hFdiff
  have hGp2Zderiv : ∀ y ∈ interior K, HasDerivAt (fun s : ℝ => Gp1Z (y.1, s)) (Gp2Z y) y.2 := by
    intro y hy
    have hFdiff : DifferentiableAt ℝ Gp1Z y :=
      (hGp1Zsmooth.differentiableOn (by norm_num) y (hUD hy)).differentiableAt
        (hDopen.mem_nhds (hUD hy))
    exact hasDerivAt_slice_snd_diff hFdiff
  have hIBP_outer_R := integral_partial_fst_mul_eq_neg (isOpen_interior (s := K)) hGp1Rcont
    hGp2Rcont hGp2Rderiv hψ hψc hψU
  have hIBP_outer_Z := integral_partial_snd_mul_eq_neg (isOpen_interior (s := K)) hGp1Zcont
    hGp2Zcont hGp2Zderiv hψ hψc hψU
  -- Gp2R/Gp2Z equal the repository's `dr (dr Θ)`/`dz (dz Θ)` on `K`
  have hGp1R_eq : ∀ y ∈ D, dr (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) (y, τ) =
      Gp1R y := by
    intro y hy
    have hFdiff : DifferentiableAt ℝ Θs y :=
      (hΘsmooth.differentiableOn (by norm_num) y hy).differentiableAt (hDopen.mem_nhds hy)
    exact (hasDerivAt_slice_fst_diff hFdiff).deriv
  have hGp1Z_eq : ∀ y ∈ D, dz (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) (y, τ) =
      Gp1Z y := by
    intro y hy
    have hFdiff : DifferentiableAt ℝ Θs y :=
      (hΘsmooth.differentiableOn (by norm_num) y hy).differentiableAt (hDopen.mem_nhds hy)
    exact (hasDerivAt_slice_snd_diff hFdiff).deriv
  have hGp2R_eq : ∀ y ∈ K, dr (dr (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q)) (y, τ)
      = Gp2R y := by
    intro y hy
    have hSopen : IsOpen {r : ℝ | zoomPointRec lam h rc zc ((r, y.2), τ) ∈ unitCylinder} :=
      hDopen.preimage (continuous_id.prodMk continuous_const)
    have hyS : y.1 ∈ {r : ℝ | zoomPointRec lam h rc zc ((r, y.2), τ) ∈ unitCylinder} :=
      hmem y hy
    have hev : (fun r : ℝ => dr (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) ((r, y.2), τ))
        =ᶠ[𝓝 y.1] fun r : ℝ => Gp1R (r, y.2) := by
      filter_upwards [hSopen.mem_nhds hyS] with r hr
      exact hGp1R_eq (r, y.2) hr
    have hFdiff : DifferentiableAt ℝ Gp1R y :=
      (hGp1Rsmooth.differentiableOn (by norm_num) y (hmem y hy)).differentiableAt
        (hDopen.mem_nhds (hmem y hy))
    have hslice := (hasDerivAt_slice_fst_diff hFdiff).congr_of_eventuallyEq hev
    exact hslice.deriv
  have hGp2Z_eq : ∀ y ∈ K, dz (dz (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q)) (y, τ)
      = Gp2Z y := by
    intro y hy
    have hSopen : IsOpen {s : ℝ | zoomPointRec lam h rc zc ((y.1, s), τ) ∈ unitCylinder} :=
      hDopen.preimage (continuous_const.prodMk continuous_id)
    have hyS : y.2 ∈ {s : ℝ | zoomPointRec lam h rc zc ((y.1, s), τ) ∈ unitCylinder} :=
      hmem y hy
    have hev : (fun s : ℝ => dz (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) ((y.1, s), τ))
        =ᶠ[𝓝 y.2] fun s : ℝ => Gp1Z (y.1, s) := by
      filter_upwards [hSopen.mem_nhds hyS] with s hs
      exact hGp1Z_eq (y.1, s) hs
    have hFdiff : DifferentiableAt ℝ Gp1Z y :=
      (hGp1Zsmooth.differentiableOn (by norm_num) y (hmem y hy)).differentiableAt
        (hDopen.mem_nhds (hmem y hy))
    have hslice := (hasDerivAt_slice_snd_diff hFdiff).congr_of_eventuallyEq hev
    exact hslice.deriv
  -- second application of integration by parts, moving the remaining derivative onto `ψ`
  have hΘscont : ContinuousOn Θs (interior K) := hΘsmooth.continuousOn.mono hUD
  set ψR' : ℝ × ℝ → ℝ := fun y => fderiv ℝ ψ y (1, 0) with hψR'_def
  set ψZ' : ℝ × ℝ → ℝ := fun y => fderiv ℝ ψ y (0, 1) with hψZ'_def
  have hψR'_contdiff : ContDiff ℝ (⊤ : ℕ∞) ψR' :=
    ((ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).contDiff).comp
      (hψ.fderiv_right (by norm_num))
  have hψZ'_contdiff : ContDiff ℝ (⊤ : ℕ∞) ψZ' :=
    ((ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).contDiff).comp
      (hψ.fderiv_right (by norm_num))
  have hψR'_compact : HasCompactSupport ψR' := HasCompactSupport.fderiv_apply ℝ hψc (1, 0)
  have hψZ'_compact : HasCompactSupport ψZ' := HasCompactSupport.fderiv_apply ℝ hψc (0, 1)
  have hψR'_supp : tsupport ψR' ⊆ interior K := (tsupport_fderiv_apply_subset ℝ (1, 0)).trans hψU
  have hψZ'_supp : tsupport ψZ' ⊆ interior K := (tsupport_fderiv_apply_subset ℝ (0, 1)).trans hψU
  have hΘsderiv_R : ∀ y ∈ interior K, HasDerivAt (fun t : ℝ => Θs (t, y.2)) (Gp1R y) y.1 := by
    intro y hy
    have hFdiff : DifferentiableAt ℝ Θs y :=
      (hΘsmooth.differentiableOn (by norm_num) y (hUD hy)).differentiableAt
        (hDopen.mem_nhds (hUD hy))
    exact hasDerivAt_slice_fst_diff hFdiff
  have hΘsderiv_Z : ∀ y ∈ interior K, HasDerivAt (fun s : ℝ => Θs (y.1, s)) (Gp1Z y) y.2 := by
    intro y hy
    have hFdiff : DifferentiableAt ℝ Θs y :=
      (hΘsmooth.differentiableOn (by norm_num) y (hUD hy)).differentiableAt
        (hDopen.mem_nhds (hUD hy))
    exact hasDerivAt_slice_snd_diff hFdiff
  have hInnerIBP_R := integral_partial_fst_mul_eq_neg (isOpen_interior (s := K)) hΘscont
    hGp1Rcont hΘsderiv_R hψR'_contdiff hψR'_compact hψR'_supp
  have hInnerIBP_Z := integral_partial_snd_mul_eq_neg (isOpen_interior (s := K)) hΘscont
    hGp1Zcont hΘsderiv_Z hψZ'_contdiff hψZ'_compact hψZ'_supp
  have houter_eq_R : (fun y : ℝ × ℝ => Gp1R y * deriv (fun t : ℝ => ψ (t, y.2)) y.1)
      = fun y => Gp1R y * ψR' y :=
    funext (fun y => by
      rw [(hasDerivAt_slice_fst_diff (hψ.differentiable (by simp) y)).deriv])
  have houter_eq_Z : (fun y : ℝ × ℝ => Gp1Z y * deriv (fun s : ℝ => ψ (y.1, s)) y.2)
      = fun y => Gp1Z y * ψZ' y :=
    funext (fun y => by
      rw [(hasDerivAt_slice_snd_diff (hψ.differentiable (by simp) y)).deriv])
  rw [houter_eq_R] at hIBP_outer_R
  rw [houter_eq_Z] at hIBP_outer_Z
  have hinner_eq_R : (fun y : ℝ × ℝ => Θs y * deriv (fun t : ℝ => ψR' (t, y.2)) y.1)
      = fun y : ℝ × ℝ => Θs y * fderiv ℝ (fderiv ℝ ψ) y (1, 0) (1, 0) :=
    funext (fun y => by rw [(hasDerivAt_slice_fst_of_fderiv hψ (1, 0) y).deriv])
  have hinner_eq_Z : (fun y : ℝ × ℝ => Θs y * deriv (fun s : ℝ => ψZ' (y.1, s)) y.2)
      = fun y : ℝ × ℝ => Θs y * fderiv ℝ (fderiv ℝ ψ) y (0, 1) (0, 1) :=
    funext (fun y => by rw [(hasDerivAt_slice_snd_of_fderiv hψ (0, 1) y).deriv])
  rw [hinner_eq_R] at hInnerIBP_R
  rw [hinner_eq_Z] at hInnerIBP_Z
  -- assemble: `∫ Gp2R * ψ = ∫ Θs * (∂_R∂_R ψ)`, and similarly for `Z`
  have hGp2R_final : (∫ y : ℝ × ℝ, Gp2R y * ψ y)
      = ∫ y : ℝ × ℝ, Θs y * fderiv ℝ (fderiv ℝ ψ) y (1, 0) (1, 0) := by
    rw [hIBP_outer_R, hInnerIBP_R]; ring_nf
  have hGp2Z_final : (∫ y : ℝ × ℝ, Gp2Z y * ψ y)
      = ∫ y : ℝ × ℝ, Θs y * fderiv ℝ (fderiv ℝ ψ) y (0, 1) (0, 1) := by
    rw [hIBP_outer_Z, hInnerIBP_Z]; ring_nf
  -- rewrite the target integral into the sum `∫ Gp2R * ψ + δ² ∫ Gp2Z * ψ`
  have hpointwise : ∀ y : ℝ × ℝ,
      (dr (dr (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q)) (y, τ)
          + (lam ^ (2 * h)) ^ 2 *
            dz (dz (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q)) (y, τ)) * ψ y
        = Gp2R y * ψ y + (lam ^ (2 * h)) ^ 2 * (Gp2Z y * ψ y) := by
    intro y
    by_cases hyK : y ∈ K
    · rw [hGp2R_eq y hyK, hGp2Z_eq y hyK]; ring
    · have hynotsupp : y ∉ tsupport ψ := fun hcontra => hyK (hUsubK (hψU hcontra))
      rw [image_eq_zero_of_notMem_tsupport hynotsupp]; ring
  have hint_Gp2Rψ : MeasureTheory.Integrable fun y : ℝ × ℝ => Gp2R y * ψ y :=
    (continuous_mul_of_tsupport_subset_diff (isOpen_interior (s := K)) hGp2Rcont hψ.continuous
      hψU).integrable_of_hasCompactSupport hψc.mul_left
  have hint_Gp2Zψ : MeasureTheory.Integrable fun y : ℝ × ℝ => Gp2Z y * ψ y :=
    (continuous_mul_of_tsupport_subset_diff (isOpen_interior (s := K)) hGp2Zcont hψ.continuous
      hψU).integrable_of_hasCompactSupport hψc.mul_left
  have htarget_eq : (∫ y : ℝ × ℝ,
      (dr (dr (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q)) (y, τ)
          + (lam ^ (2 * h)) ^ 2 *
            dz (dz (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q)) (y, τ)) * ψ y)
      = (∫ y : ℝ × ℝ, Gp2R y * ψ y) + (lam ^ (2 * h)) ^ 2 * ∫ y : ℝ × ℝ, Gp2Z y * ψ y := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpointwise)]
    rw [integral_add hint_Gp2Rψ (hint_Gp2Zψ.const_mul _), integral_const_mul]
  rw [htarget_eq, hGp2R_final, hGp2Z_final]
  -- final bound
  have hΘbound : ∀ y ∈ K, |Θs y| ≤ 2 * C :=
    fun y hy => abs_zoomTheta_le_const_diff hC hh0 hh1 hlam hdelta hb (hu.of_le (by norm_num))
      (hmem y hy) htau
  have hψRR_bound : ∀ y, |fderiv ℝ (fderiv ℝ ψ) y (1, 0) (1, 0)| ≤ B := by
    intro y
    have hle1 : ‖fderiv ℝ (fderiv ℝ ψ) y (1, 0)‖
        ≤ ‖fderiv ℝ (fderiv ℝ ψ) y‖ * ‖((1, 0) : ℝ × ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    have hle2 : ‖fderiv ℝ (fderiv ℝ ψ) y (1, 0) (1, 0)‖
        ≤ ‖fderiv ℝ (fderiv ℝ ψ) y (1, 0)‖ * ‖((1, 0) : ℝ × ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    have hnorm1 : ‖((1, 0) : ℝ × ℝ)‖ = 1 := by rw [Prod.norm_def]; norm_num
    rw [hnorm1, mul_one] at hle1 hle2
    calc |fderiv ℝ (fderiv ℝ ψ) y (1, 0) (1, 0)| = ‖fderiv ℝ (fderiv ℝ ψ) y (1, 0) (1, 0)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (fderiv ℝ ψ) y (1, 0)‖ := hle2
      _ ≤ ‖fderiv ℝ (fderiv ℝ ψ) y‖ := hle1
      _ ≤ B := (hψB y).2.2
  have hψZZ_bound : ∀ y, |fderiv ℝ (fderiv ℝ ψ) y (0, 1) (0, 1)| ≤ B := by
    intro y
    have hle1 : ‖fderiv ℝ (fderiv ℝ ψ) y (0, 1)‖
        ≤ ‖fderiv ℝ (fderiv ℝ ψ) y‖ * ‖((0, 1) : ℝ × ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    have hle2 : ‖fderiv ℝ (fderiv ℝ ψ) y (0, 1) (0, 1)‖
        ≤ ‖fderiv ℝ (fderiv ℝ ψ) y (0, 1)‖ * ‖((0, 1) : ℝ × ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    have hnorm1 : ‖((0, 1) : ℝ × ℝ)‖ = 1 := by rw [Prod.norm_def]; norm_num
    rw [hnorm1, mul_one] at hle1 hle2
    calc |fderiv ℝ (fderiv ℝ ψ) y (0, 1) (0, 1)| = ‖fderiv ℝ (fderiv ℝ ψ) y (0, 1) (0, 1)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (fderiv ℝ ψ) y (0, 1)‖ := hle2
      _ ≤ ‖fderiv ℝ (fderiv ℝ ψ) y‖ := hle1
      _ ≤ B := (hψB y).2.2
  have hψRR_fn_eq : (fun y : ℝ × ℝ => fderiv ℝ (fderiv ℝ ψ) y (1, 0) (1, 0))
      = fun y : ℝ × ℝ => fderiv ℝ ψR' y (1, 0) := by
    funext y
    have hgdiff : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
      ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
    have hcomp : HasFDerivAt ψR'
        ((ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).comp (fderiv ℝ (fderiv ℝ ψ) y)) y :=
      (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).hasFDerivAt.comp y hgdiff.hasFDerivAt
    rw [hcomp.fderiv]; rfl
  have hψZZ_fn_eq : (fun y : ℝ × ℝ => fderiv ℝ (fderiv ℝ ψ) y (0, 1) (0, 1))
      = fun y : ℝ × ℝ => fderiv ℝ ψZ' y (0, 1) := by
    funext y
    have hgdiff : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
      ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
    have hcomp : HasFDerivAt ψZ'
        ((ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).comp (fderiv ℝ (fderiv ℝ ψ) y)) y :=
      (ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).hasFDerivAt.comp y hgdiff.hasFDerivAt
    rw [hcomp.fderiv]; rfl
  have hdRRψ_supp : tsupport (fun y : ℝ × ℝ => fderiv ℝ (fderiv ℝ ψ) y (1, 0) (1, 0)) ⊆ K := by
    rw [hψRR_fn_eq]
    exact ((tsupport_fderiv_apply_subset ℝ (1, 0)).trans hψR'_supp).trans hUsubK
  have hdZZψ_supp : tsupport (fun y : ℝ × ℝ => fderiv ℝ (fderiv ℝ ψ) y (0, 1) (0, 1)) ⊆ K := by
    rw [hψZZ_fn_eq]
    exact ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans hψZ'_supp).trans hUsubK
  have hboundR := abs_integral_mul_le_of_tsupport_subset hK.measure_lt_top hdRRψ_supp hΘbound
    hψRR_bound
  have hboundZ := abs_integral_mul_le_of_tsupport_subset hK.measure_lt_top hdZZψ_supp hΘbound
    hψZZ_bound
  have hδnn : (0 : ℝ) ≤ (lam ^ (2 * h)) ^ 2 := by positivity
  calc |(∫ y : ℝ × ℝ, Θs y * fderiv ℝ (fderiv ℝ ψ) y (1, 0) (1, 0))
        + (lam ^ (2 * h)) ^ 2 * ∫ y : ℝ × ℝ, Θs y * fderiv ℝ (fderiv ℝ ψ) y (0, 1) (0, 1)|
      ≤ |∫ y : ℝ × ℝ, Θs y * fderiv ℝ (fderiv ℝ ψ) y (1, 0) (1, 0)|
        + |(lam ^ (2 * h)) ^ 2 * ∫ y : ℝ × ℝ, Θs y * fderiv ℝ (fderiv ℝ ψ) y (0, 1) (0, 1)| :=
        abs_add_le _ _
    _ = |∫ y : ℝ × ℝ, Θs y * fderiv ℝ (fderiv ℝ ψ) y (1, 0) (1, 0)|
        + (lam ^ (2 * h)) ^ 2 *
          |∫ y : ℝ × ℝ, Θs y * fderiv ℝ (fderiv ℝ ψ) y (0, 1) (0, 1)| := by
        rw [abs_mul, abs_of_nonneg hδnn]
    _ ≤ 2 * C * B * (volume K).toReal + (lam ^ (2 * h)) ^ 2 * (2 * C * B * (volume K).toReal) := by
        have hstep := add_le_add hboundR (mul_le_mul_of_nonneg_left hboundZ hδnn)
        linarith only [hstep]
    _ ≤ 2 * C * B * (volume K).toReal + 1 * (2 * C * B * (volume K).toReal) := by
        have hδsq : (lam ^ (2 * h)) ^ 2 ≤ 1 := by
          have hδnn' : (0 : ℝ) ≤ lam ^ (2 * h) := Real.rpow_nonneg hlam.le _
          nlinarith only [hδnn', hdelta]
        have hCB_nonneg : (0 : ℝ) ≤ 2 * C * B * (volume K).toReal := by positivity
        have hstep := mul_le_mul_of_nonneg_right hδsq hCB_nonneg
        linarith only [hstep]
    _ = 4 * C * (volume K).toReal * B := by ring

/-- The eventual-in-`n` pairing bound for the diffusion term: `C₀ := 4C` is chosen before
`n`, matching the eventual form of the time-pairing estimate `hpair`. -/
theorem diffusion_term_pairing_bound {C h : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2)
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
              (dr (dr (fun q : (ℝ × ℝ) × ℝ => zoomTheta (lam n) h rc zc u q)) (y, τ)
                  + (lam n ^ (2 * h)) ^ 2 *
                    dz (dz (fun q : (ℝ × ℝ) × ℝ => zoomTheta (lam n) h rc zc u q)) (y, τ))
                * ψ y|
            ≤ C₀ * B := by
  refine ⟨4 * C * (volume K).toReal, by positivity, fun ψ hψ hψc hψU B hB hψB => ?_⟩
  filter_upwards [hlam_le, hmem] with n hlam_len hmem_n
  exact diffusion_term_pairing_bound_fixed hC hh0 hh1 (hlam_pos n) hlam_len hb hu hK htau hmem_n ψ
    hψ hψc hψU B hB hψB

end CIV
