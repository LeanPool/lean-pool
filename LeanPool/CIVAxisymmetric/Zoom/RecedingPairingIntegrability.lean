/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.ThetaLipschitz
public import LeanPool.CIVAxisymmetric.Zoom.RecedingEquation
public import LeanPool.CIVAxisymmetric.Reduction.CurlCompMultiPartialBridge

/-! ### The transport/divergence term `T1` -/

public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- The recentred zoom point restricted to a fixed time `τ`, as a map of the meridional
plane alone, is smooth. -/
private theorem contDiff_zoomPointRec_atTau_int (lam h rc zc τ : ℝ) :
    ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomPointRec lam h rc zc (y, τ)) :=
  (contDiff_zoomPointRec lam h rc zc).comp (contDiff_id.prodMk contDiff_const)

/-- The domain on which the recentred zoom point at a fixed time `τ` lies in the unit
cylinder is open. -/
private theorem isOpen_zoomDomain_int (lam h rc zc τ : ℝ) :
    IsOpen {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} :=
  (isOpen_zoomPointRec_preimage lam h rc zc).preimage (continuous_id.prodMk continuous_const)

/-- `Θ_n(·, τ)` is smooth on its natural domain. -/
private theorem contDiffOn_zoomTheta_slice_int {lam h rc zc τ : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} := by
  have hζ := contDiff_zoomPointRec_atTau_int lam h rc zc τ
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
private theorem contDiffOn_zoomVRec_slice_int {lam h rc zc τ : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomVRec lam h rc zc u (y, τ))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} := by
  have hζ := contDiff_zoomPointRec_atTau_int lam h rc zc τ
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
private theorem contDiffOn_zoomWRec_slice_int {lam h rc zc τ : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomWRec lam h rc zc u (y, τ))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} := by
  have hζ := contDiff_zoomPointRec_atTau_int lam h rc zc τ
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
directional derivative. -/
private theorem hasDerivAt_slice_fst_int {F : ℝ × ℝ → ℝ} {y : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F y) :
    HasDerivAt (fun t : ℝ => F (t, y.2)) (fderiv ℝ F y (1, 0)) y.1 := by
  have hline : HasDerivAt (fun t : ℝ => (t, y.2)) ((1 : ℝ), (0 : ℝ)) y.1 :=
    (hasDerivAt_id y.1).prodMk (hasDerivAt_const y.1 y.2)
  exact HasFDerivAt.comp_hasDerivAt_of_eq (hl := hF.hasFDerivAt) (hf := hline) (hy := rfl)

/-- The derivative of the second slice of a differentiable function of `ℝ × ℝ` is the second
directional derivative. -/
private theorem hasDerivAt_slice_snd_int {F : ℝ × ℝ → ℝ} {y : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F y) :
    HasDerivAt (fun s : ℝ => F (y.1, s)) (fderiv ℝ F y (0, 1)) y.2 := by
  have hline : HasDerivAt (fun s : ℝ => (y.1, s)) ((0 : ℝ), (1 : ℝ)) y.2 :=
    (hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2)
  exact HasFDerivAt.comp_hasDerivAt_of_eq (hl := hF.hasFDerivAt) (hf := hline) (hy := rfl)

/-- The product of a function continuous on an open set with a continuous function whose
support closes inside that set is continuous on the whole plane. -/
theorem continuous_mul_of_tsupport_subset_pairing {U : Set (ℝ × ℝ)} (hU : IsOpen U)
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



/-- Integrability of the transport/divergence term of `zoomTheta_pde_divergenceForm` against a
test function `ψ` supported in the interior of a compact set `K`, at a fixed zoom scale. Public
restatement of the continuity argument `CIV.RecedingTransportPairingBound`'s private proof
already carries, exposed for `CIV.dtPast_zoomTheta_pairing_bound_fixed`'s `hint1`. -/
theorem integrable_transportTerm_mul_zoomTheta {lam h rc zc : ℝ}
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {K : Set (ℝ × ℝ)} {τ : ℝ}
    (hmem : ∀ y ∈ K, zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ interior K) :
    Integrable fun y : ℝ × ℝ =>
      (-(dr (fun q : (ℝ × ℝ) × ℝ => zoomVRec lam h rc zc u q * zoomTheta lam h rc zc u q) (y, τ)
          + dz (fun q : (ℝ × ℝ) × ℝ => zoomWRec lam h rc zc u q * zoomTheta lam h rc zc u q)
            (y, τ))) * ψ y := by
  set D : Set (ℝ × ℝ) := {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} with hD_def
  set F1 : ℝ × ℝ → ℝ := fun y => zoomVRec lam h rc zc u (y, τ) * zoomTheta lam h rc zc u (y, τ)
    with hF1_def
  set F2 : ℝ × ℝ → ℝ := fun y => zoomWRec lam h rc zc u (y, τ) * zoomTheta lam h rc zc u (y, τ)
    with hF2_def
  set Gp1 : ℝ × ℝ → ℝ := fun y => fderiv ℝ F1 y (1, 0) with hGp1_def
  set Gp2 : ℝ × ℝ → ℝ := fun y => fderiv ℝ F2 y (0, 1) with hGp2_def
  have hDopen : IsOpen D := isOpen_zoomDomain_int lam h rc zc τ
  have hUsubK : interior K ⊆ K := interior_subset
  have hUD : interior K ⊆ D := fun y hy => hmem y (hUsubK hy)
  have hΘsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ)) D :=
    contDiffOn_zoomTheta_slice_int hu
  have hVsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomVRec lam h rc zc u (y, τ)) D :=
    contDiffOn_zoomVRec_slice_int hu
  have hWsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomWRec lam h rc zc u (y, τ)) D :=
    contDiffOn_zoomWRec_slice_int hu
  have hF1smooth : ContDiffOn ℝ (⊤ : ℕ∞) F1 D := hVsmooth.mul hΘsmooth
  have hF2smooth : ContDiffOn ℝ (⊤ : ℕ∞) F2 D := hWsmooth.mul hΘsmooth
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
  have hGp1_eq : ∀ y ∈ K, Gp1 y =
      dr (fun q : (ℝ × ℝ) × ℝ => zoomVRec lam h rc zc u q * zoomTheta lam h rc zc u q) (y, τ) := by
    intro y hy
    have hFdiff : DifferentiableAt ℝ F1 y :=
      (hF1smooth.differentiableOn (by norm_num) y (hmem y hy)).differentiableAt
        (hDopen.mem_nhds (hmem y hy))
    exact (hasDerivAt_slice_fst_int hFdiff).deriv.symm
  have hGp2_eq : ∀ y ∈ K, Gp2 y =
      dz (fun q : (ℝ × ℝ) × ℝ => zoomWRec lam h rc zc u q * zoomTheta lam h rc zc u q) (y, τ) := by
    intro y hy
    have hFdiff : DifferentiableAt ℝ F2 y :=
      (hF2smooth.differentiableOn (by norm_num) y (hmem y hy)).differentiableAt
        (hDopen.mem_nhds (hmem y hy))
    exact (hasDerivAt_slice_snd_int hFdiff).deriv.symm
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
  have hint_Gp1ψ : Integrable fun y : ℝ × ℝ => Gp1 y * ψ y :=
    (continuous_mul_of_tsupport_subset_pairing (isOpen_interior (s := K)) hGp1cont hψ.continuous
      hψU).integrable_of_hasCompactSupport hψc.mul_left
  have hint_Gp2ψ : Integrable fun y : ℝ × ℝ => Gp2 y * ψ y :=
    (continuous_mul_of_tsupport_subset_pairing (isOpen_interior (s := K)) hGp2cont hψ.continuous
      hψU).integrable_of_hasCompactSupport hψc.mul_left
  exact (hint_Gp1ψ.neg.sub hint_Gp2ψ).congr
    (Filter.Eventually.of_forall fun y => (hpointwise y).symm)

/-! ### The diffusion term `T2` -/

/-- `z ↦ fderiv ψ z v` differentiates along the first coordinate to
`fderiv (fderiv ψ) y (1, 0) v`. -/
private theorem hasDerivAt_slice_fst_of_fderiv_int {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (v : ℝ × ℝ) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => fderiv ℝ ψ (t, y.2) v) (fderiv ℝ (fderiv ℝ ψ) y (1, 0) v) y.1 := by
  have hgdiff : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
  have hFdiff : DifferentiableAt ℝ (fun z : ℝ × ℝ => fderiv ℝ ψ z v) y :=
    ((ContinuousLinearMap.apply ℝ ℝ v).differentiableAt).comp y hgdiff
  have hslice := hasDerivAt_slice_fst_int hFdiff
  have hcomp : HasFDerivAt (fun z : ℝ × ℝ => fderiv ℝ ψ z v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ ψ) y)) y :=
    (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp y hgdiff.hasFDerivAt
  have hval : fderiv ℝ (fun z : ℝ × ℝ => fderiv ℝ ψ z v) y (1, 0)
      = fderiv ℝ (fderiv ℝ ψ) y (1, 0) v := by
    rw [hcomp.fderiv]; rfl
  rwa [hval] at hslice

/-- Integrability of the diffusion term of `zoomTheta_pde_divergenceForm` against a test
function `ψ` supported in the interior of a compact set `K`, at a fixed zoom scale. Public
restatement of the continuity argument `CIV.RecedingDiffusionPairingBound`'s private proof
already carries, exposed for `CIV.dtPast_zoomTheta_pairing_bound_fixed`'s `hint2`. -/
theorem integrable_diffusionTerm_mul_zoomTheta {lam h rc zc : ℝ}
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {K : Set (ℝ × ℝ)} {τ : ℝ}
    (hmem : ∀ y ∈ K, zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ interior K) :
    Integrable fun y : ℝ × ℝ =>
      (dr (dr (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q)) (y, τ)
          + (lam ^ (2 * h)) ^ 2 *
            dz (dz (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q)) (y, τ)) * ψ y := by
  set D : Set (ℝ × ℝ) := {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} with hD_def
  set Θs : ℝ × ℝ → ℝ := fun y => zoomTheta lam h rc zc u (y, τ) with hΘs_def
  set Gp1R : ℝ × ℝ → ℝ := fun y => fderiv ℝ Θs y (1, 0) with hGp1R_def
  set Gp2R : ℝ × ℝ → ℝ := fun y => fderiv ℝ Gp1R y (1, 0) with hGp2R_def
  set Gp1Z : ℝ × ℝ → ℝ := fun y => fderiv ℝ Θs y (0, 1) with hGp1Z_def
  set Gp2Z : ℝ × ℝ → ℝ := fun y => fderiv ℝ Gp1Z y (0, 1) with hGp2Z_def
  have hDopen : IsOpen D := isOpen_zoomDomain_int lam h rc zc τ
  have hUsubK : interior K ⊆ K := interior_subset
  have hUD : interior K ⊆ D := fun y hy => hmem y (hUsubK hy)
  have hΘsmooth : ContDiffOn ℝ (⊤ : ℕ∞) Θs D := contDiffOn_zoomTheta_slice_int hu
  have hGp1Rsmooth : ContDiffOn ℝ (⊤ : ℕ∞) Gp1R D :=
    (hΘsmooth.fderiv_of_isOpen hDopen (by norm_num)).clm_apply contDiffOn_const
  have hGp1Zsmooth : ContDiffOn ℝ (⊤ : ℕ∞) Gp1Z D :=
    (hΘsmooth.fderiv_of_isOpen hDopen (by norm_num)).clm_apply contDiffOn_const
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
  have hGp1R_eq : ∀ y ∈ D, dr (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) (y, τ) =
      Gp1R y := by
    intro y hy
    have hFdiff : DifferentiableAt ℝ Θs y :=
      (hΘsmooth.differentiableOn (by norm_num) y hy).differentiableAt (hDopen.mem_nhds hy)
    exact (hasDerivAt_slice_fst_int hFdiff).deriv
  have hGp1Z_eq : ∀ y ∈ D, dz (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) (y, τ) =
      Gp1Z y := by
    intro y hy
    have hFdiff : DifferentiableAt ℝ Θs y :=
      (hΘsmooth.differentiableOn (by norm_num) y hy).differentiableAt (hDopen.mem_nhds hy)
    exact (hasDerivAt_slice_snd_int hFdiff).deriv
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
    have hslice := (hasDerivAt_slice_fst_int hFdiff).congr_of_eventuallyEq hev
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
    have hslice := (hasDerivAt_slice_snd_int hFdiff).congr_of_eventuallyEq hev
    exact hslice.deriv
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
  have hint_Gp2Rψ : Integrable fun y : ℝ × ℝ => Gp2R y * ψ y :=
    (continuous_mul_of_tsupport_subset_pairing (isOpen_interior (s := K)) hGp2Rcont hψ.continuous
      hψU).integrable_of_hasCompactSupport hψc.mul_left
  have hint_Gp2Zψ : Integrable fun y : ℝ × ℝ => Gp2Z y * ψ y :=
    (continuous_mul_of_tsupport_subset_pairing (isOpen_interior (s := K)) hGp2Zcont hψ.continuous
      hψU).integrable_of_hasCompactSupport hψc.mul_left
  exact (hint_Gp2Rψ.add (hint_Gp2Zψ.const_mul _)).congr
    (Filter.Eventually.of_forall fun y => (hpointwise y).symm)

/-! ### The curvature term T3 -/

/-- The curvature-coefficient quotient `Θ(·, τ) / (A + ·)` is smooth on the open set where
the recentred zoom point lies in the unit cylinder and the offset `A + R` is positive. -/
private theorem contDiffOn_curvatureQuotient_int {lam h rc zc τ : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} := by
  set D : Set (ℝ × ℝ) :=
    {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} with hD_def
  have hζ : ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => zoomPointRec lam h rc zc (y, τ)) := contDiff_zoomPointRec_atTau_int lam
        h rc zc τ
  have hTheta : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ)) D := by
    have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y : ℝ × ℝ => azimuthalVorticity u (zoomPointRec lam h rc zc (y, τ))) D :=
      (contDiffOn_azimuthalVorticity hu).comp hζ.contDiffOn (fun y hy => hy.1)
    have heq : (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ))
        = fun y : ℝ × ℝ => lam ^ 2 * lam ^ (2 * h) *
          azimuthalVorticity u (zoomPointRec lam h rc zc (y, τ)) := by
      funext y; rfl
    rw [heq]
    exact hcomp.const_smul (lam ^ 2 * lam ^ (2 * h))
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => rc / lam + y.1) D :=
    (contDiff_const.add contDiff_fst).contDiffOn
  have hAne : ∀ y ∈ D, rc / lam + y.1 ≠ 0 := fun y hy => (hy.2).ne'
  exact hTheta.div hA hAne

/-- The domain of `contDiffOn_curvatureQuotient_int` is open. -/
private theorem isOpen_curvatureDomain_int (lam h rc zc τ : ℝ) :
    IsOpen {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} := by
  have h1 : IsOpen {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} :=
    isOpen_zoomDomain_int lam h rc zc τ
  have h2 : IsOpen {y : ℝ × ℝ | (0 : ℝ) < rc / lam + y.1} :=
    isOpen_lt continuous_const (continuous_const.add continuous_fst)
  exact h1.inter h2

/-- The `fderiv`-bundled derivative of the curvature quotient is continuous on the domain. -/
private theorem continuousOn_fderiv_curvatureQuotient_int {lam h rc zc τ : ℝ}
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z)
      unitCylinder) :
    ContinuousOn
      (fderiv ℝ (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1)))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} :=
  ((contDiffOn_curvatureQuotient_int hu).fderiv_of_isOpen (m := 0)
    (isOpen_curvatureDomain_int lam h rc zc τ) (by norm_num)).continuousOn

/-- The `fderiv`-bundled derivative of the curvature quotient, at the basis vector `(1, 0)`,
agrees with the closed-form curvature term `∂_R Θ_n / (A + R) − Θ_n / (A + R)²`. -/
private theorem hasDerivAt_curvatureQuotient_slice_int {lam h rc zc τ : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {y : ℝ × ℝ} (hp : zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    (hApos : 0 < rc / lam + y.1) :
    HasDerivAt (fun r : ℝ => zoomTheta lam h rc zc u ((r, y.2), τ) / (rc / lam + r))
      (dr (zoomTheta lam h rc zc u) (y, τ) / (rc / lam + y.1)
        - zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1) ^ 2) y.1 := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by norm_num)
  have hΘ' : HasDerivAt (fun r : ℝ => zoomTheta lam h rc zc u ((r, y.2), τ))
      (dr (zoomTheta lam h rc zc u) (y, τ)) y.1 :=
    hasDerivAt_dr_zoomTheta lam h rc zc hlam u hu2 (y, τ) hp
  have hA' : HasDerivAt (fun r : ℝ => rc / lam + r) 1 y.1 :=
    (hasDerivAt_id y.1).const_add (rc / lam)
  have hAne : rc / lam + y.1 ≠ 0 := hApos.ne'
  have hdiv := hΘ'.div hA' hAne
  have heq : (dr (zoomTheta lam h rc zc u) (y, τ) * (rc / lam + y.1)
        - zoomTheta lam h rc zc u (y, τ) * 1) / (rc / lam + y.1) ^ 2
      = dr (zoomTheta lam h rc zc u) (y, τ) / (rc / lam + y.1)
        - zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1) ^ 2 := by
    field_simp
  rwa [heq] at hdiv

/-- The `fderiv`-bundled derivative of the curvature quotient equals the closed-form
curvature term on the domain. -/
private theorem fderiv_curvatureQuotient_eq_int {lam h rc zc τ : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {y : ℝ × ℝ} (hp : zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    (hApos : 0 < rc / lam + y.1) :
    fderiv ℝ (fun y' : ℝ × ℝ => zoomTheta lam h rc zc u (y', τ) / (rc / lam + y'.1)) y (1, 0)
      = dr (zoomTheta lam h rc zc u) (y, τ) / (rc / lam + y.1)
        - zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1) ^ 2 := by
  have hDcontains : y ∈
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} :=
    ⟨hp, hApos⟩
  have hFdiff : DifferentiableAt ℝ
      (fun y' : ℝ × ℝ => zoomTheta lam h rc zc u (y', τ) / (rc / lam + y'.1)) y :=
    ((contDiffOn_curvatureQuotient_int hu).differentiableOn (by norm_num) y hDcontains)
      |>.differentiableAt ((isOpen_curvatureDomain_int lam h rc zc τ).mem_nhds hDcontains)
  have hslice := hasDerivAt_slice_fst_int hFdiff
  have hexplicit := hasDerivAt_curvatureQuotient_slice_int hlam hu hp hApos
  exact hslice.unique hexplicit

/-- Integrability of the curvature term of `zoomTheta_pde_divergenceForm` against a test
function `ψ` supported in the interior of a compact set `K`, at a fixed zoom scale. Public
restatement of the continuity argument `CIV.RecedingCurvaturePairingBound`'s private proof
already carries, exposed for `CIV.dtPast_zoomTheta_pairing_bound_fixed`'s `hint3`. -/
theorem integrable_curvatureTerm_mul_zoomTheta {lam h rc zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {K : Set (ℝ × ℝ)} {τ : ℝ}
    (hmem : ∀ y ∈ K, zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    (hApos : ∀ y ∈ K, (0 : ℝ) < rc / lam + y.1)
    {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ interior K) :
    Integrable fun y : ℝ × ℝ =>
      (dr (zoomTheta lam h rc zc u) (y, τ) / (rc / lam + y.1)
          - zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1) ^ 2) * ψ y := by
  set F : ℝ × ℝ → ℝ := fun y => zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1) with hF_def
  set Gp : ℝ × ℝ → ℝ := fun y => fderiv ℝ F y (1, 0) with hGp_def
  set D : Set (ℝ × ℝ) :=
    {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} with hD_def
  have hUsubK : interior K ⊆ K := interior_subset
  have hUD : interior K ⊆ D := fun y hy => ⟨hmem y (hUsubK hy), hApos y (hUsubK hy)⟩
  have hGcont : ContinuousOn Gp (interior K) := by
    have hcomp : ContinuousOn (fun y : ℝ × ℝ => (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ))
        (fderiv ℝ F y)) D :=
      (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).continuous.comp_continuousOn
        (continuousOn_fderiv_curvatureQuotient_int hu)
    exact hcomp.mono hUD
  have hGp_eq : ∀ y ∈ K, Gp y =
      dr (zoomTheta lam h rc zc u) (y, τ) / (rc / lam + y.1)
        - zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1) ^ 2 := by
    intro y hy
    exact fderiv_curvatureQuotient_eq_int hlam hu (hmem y hy) (hApos y hy)
  have hpointwise : ∀ y : ℝ × ℝ, Gp y * ψ y =
      (dr (zoomTheta lam h rc zc u) (y, τ) / (rc / lam + y.1)
        - zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1) ^ 2) * ψ y := by
    intro y
    by_cases hyK : y ∈ K
    · rw [hGp_eq y hyK]
    · have hynotsupp : y ∉ tsupport ψ := fun hcontra => hyK (hUsubK (hψU hcontra))
      rw [image_eq_zero_of_notMem_tsupport hynotsupp, mul_zero, mul_zero]
  have hintGpψ : Integrable fun y : ℝ × ℝ => Gp y * ψ y :=
    (continuous_mul_of_tsupport_subset_pairing (isOpen_interior (s := K)) hGcont hψ.continuous
      hψU).integrable_of_hasCompactSupport hψc.mul_left
  exact hintGpψ.congr (Filter.Eventually.of_forall hpointwise)

/-! ### The swirl term T4 -/

/-- The conservative swirl source `S_n² / (A + R)` is smooth on the open set where the
recentred zoom point lies in the unit cylinder and the offset `A + R` is positive. -/
private theorem contDiffOn_swirlQuotient_int {lam h rc zc τ : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => zoomSRec lam h rc zc u (y, τ) ^ 2 / (rc / lam + y.1))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} := by
  set D : Set (ℝ × ℝ) :=
    {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} with hD_def
  have hζ : ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => zoomPointRec lam h rc zc (y, τ)) := contDiff_zoomPointRec_atTau_int lam
        h rc zc τ
  have hu1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z 1) unitCylinder :=
    contDiffOn_pi.1 hu 1
  have hSsq : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => zoomSRec lam h rc zc u (y, τ) ^ 2) D := by
    have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y : ℝ × ℝ => u (zoomPointRec lam h rc zc (y, τ)) 1) D :=
      hu1.comp hζ.contDiffOn (fun y hy => hy.1)
    have heq : (fun y : ℝ × ℝ => zoomSRec lam h rc zc u (y, τ) ^ 2)
        = fun y : ℝ × ℝ =>
          (lam * lam ^ (2 * h) * u (zoomPointRec lam h rc zc (y, τ)) 1) ^ 2 := by
      funext y; rfl
    rw [heq]
    exact ((hcomp.const_smul (lam * lam ^ (2 * h))).pow 2)
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ × ℝ => rc / lam + y.1) D :=
    (contDiff_const.add contDiff_fst).contDiffOn
  have hAne : ∀ y ∈ D, rc / lam + y.1 ≠ 0 := fun y hy => (hy.2).ne'
  exact hSsq.div hA hAne

/-- The domain of `contDiffOn_swirlQuotient_int` is open. -/
private theorem isOpen_swirlDomain_int (lam h rc zc τ : ℝ) :
    IsOpen {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} :=
  isOpen_curvatureDomain_int lam h rc zc τ

/-- The `fderiv`-bundled derivative of the swirl quotient is continuous on the domain. -/
private theorem continuousOn_fderiv_swirlQuotient_int {lam h rc zc τ : ℝ}
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z)
      unitCylinder) :
    ContinuousOn
      (fderiv ℝ (fun y : ℝ × ℝ => zoomSRec lam h rc zc u (y, τ) ^ 2 / (rc / lam + y.1)))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} :=
  ((contDiffOn_swirlQuotient_int hu).fderiv_of_isOpen (m := 0)
    (isOpen_swirlDomain_int lam h rc zc τ) (by norm_num)).continuousOn

/-- `S_n²` differentiates in `Z` to the vertical derivative `∂_Z(S_n²)`. -/
private theorem hasDerivAt_dz_zoomSRecSq_int (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => zoomSRec lam h rc zc u ((p.1.1, s), p.2) ^ 2)
      (dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) p) p.1.2 := by
  have hswirlSmooth : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z 1 ^ 2) unitCylinder := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z 1) unitCylinder :=
      contDiffOn_pi.1 hu 1
    exact (h1.pow 2).of_le (by norm_num)
  have heq2 : (fun s : ℝ => zoomSRec lam h rc zc u ((p.1.1, s), p.2) ^ 2)
      = fun s : ℝ =>
        (lam * lam ^ (2 * h) * u (zoomPointRec lam h rc zc ((p.1.1, s), p.2)) 1) ^ 2 := by
    funext s; rfl
  rw [heq2]
  have hderiv := (hasDerivAt_zoomRecScalar_z (Phi := fun w => u w 1 ^ 2) lam h rc zc hswirlSmooth
    p hp).const_mul (lam ^ 2 * (lam ^ (2 * h)) ^ 2)
  have hswirlFun : (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2)
      = fun q : (ℝ × ℝ) × ℝ => lam ^ 2 * (lam ^ (2 * h)) ^ 2 *
          (u (zoomPointRec lam h rc zc q) 1 ^ 2) := by
    funext q; show (lam * lam ^ (2 * h) * u (zoomPointRec lam h rc zc q) 1) ^ 2 = _; ring
  have htarget : dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) p
      = lam ^ 2 * (lam ^ (2 * h)) ^ 2 *
        (lam ^ (1 - 2 * h) *
          spatialPartial (fun w : ParabolicPoint => u w 1 ^ 2) 2 (zoomPointRec lam h rc zc p)) := by
    rw [hswirlFun, dz]
    exact ((hasDerivAt_zoomRecScalar_z (Phi := fun w => u w 1 ^ 2) lam h rc zc hswirlSmooth p
      hp).const_mul (lam ^ 2 * (lam ^ (2 * h)) ^ 2)).deriv
  rw [htarget]
  have hcongr : (fun s : ℝ =>
      (lam * lam ^ (2 * h) * u (zoomPointRec lam h rc zc ((p.1.1, s), p.2)) 1) ^ 2)
      = fun s : ℝ => lam ^ 2 * (lam ^ (2 * h)) ^ 2 *
          u (zoomPointRec lam h rc zc ((p.1.1, s), p.2)) 1 ^ 2 := by
    funext s; ring
  rwa [hcongr]

/-- The swirl quotient's slice derivative in `Z` equals `(1 / (A + R)) ∂_Z(S_n²)`. -/
private theorem hasDerivAt_swirlQuotient_slice_int {lam h rc zc τ : ℝ}
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {y : ℝ × ℝ} (hp : zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => zoomSRec lam h rc zc u ((y.1, s), τ) ^ 2 / (rc / lam + y.1))
      (1 / (rc / lam + y.1) * dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) (y, τ))
      y.2 := by
  have hS' := hasDerivAt_dz_zoomSRecSq_int lam h rc zc u hu (y, τ) hp
  have hconst : HasDerivAt
      (fun s : ℝ => zoomSRec lam h rc zc u ((y.1, s), τ) ^ 2 / (rc / lam + y.1))
      (dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) (y, τ) / (rc / lam + y.1))
      y.2 := hS'.div_const _
  have heq : dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) (y, τ) / (rc / lam + y.1)
      = 1 / (rc / lam + y.1) * dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) (y, τ) := by
    ring
  rwa [heq] at hconst

/-- `fderiv`-bundled derivative of the swirl quotient equals `(1/(A+R)) ∂_Z(S_n²)` on the
domain. -/
private theorem fderiv_swirlQuotient_eq_int {lam h rc zc τ : ℝ}
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {y : ℝ × ℝ} (hp : zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    (hApos : 0 < rc / lam + y.1) :
    fderiv ℝ (fun y' : ℝ × ℝ => zoomSRec lam h rc zc u (y', τ) ^ 2 / (rc / lam + y'.1)) y (0, 1)
      = 1 / (rc / lam + y.1) * dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) (y, τ) := by
  have hDcontains : y ∈
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} :=
    ⟨hp, hApos⟩
  have hFdiff : DifferentiableAt ℝ
      (fun y' : ℝ × ℝ => zoomSRec lam h rc zc u (y', τ) ^ 2 / (rc / lam + y'.1)) y :=
    ((contDiffOn_swirlQuotient_int hu).differentiableOn (by norm_num) y hDcontains)
      |>.differentiableAt ((isOpen_swirlDomain_int lam h rc zc τ).mem_nhds hDcontains)
  have hslice := hasDerivAt_slice_snd_int hFdiff
  have hexplicit := hasDerivAt_swirlQuotient_slice_int hu hp
  exact hslice.unique hexplicit

/-- Integrability of the swirl term of `zoomTheta_pde_divergenceForm` against a test function
`ψ` supported in the interior of a compact set `K`, at a fixed zoom scale. Public restatement
of the continuity argument `CIV.RecedingSwirlPairingBound`'s private proof already carries,
exposed for `CIV.dtPast_zoomTheta_pairing_bound_fixed`'s `hint4`. -/
theorem integrable_swirlTerm_mul_zoomTheta {lam h rc zc : ℝ}
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {K : Set (ℝ × ℝ)} {τ : ℝ}
    (hmem : ∀ y ∈ K, zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    (hApos : ∀ y ∈ K, (0 : ℝ) < rc / lam + y.1)
    {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ interior K) :
    Integrable fun y : ℝ × ℝ =>
      (1 / (rc / lam + y.1) *
          dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) (y, τ)) * ψ y := by
  set F : ℝ × ℝ → ℝ := fun y => zoomSRec lam h rc zc u (y, τ) ^ 2 / (rc / lam + y.1) with hF_def
  set Gp : ℝ × ℝ → ℝ := fun y => fderiv ℝ F y (0, 1) with hGp_def
  set D : Set (ℝ × ℝ) :=
    {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} with hD_def
  have hUsubK : interior K ⊆ K := interior_subset
  have hUD : interior K ⊆ D := fun y hy => ⟨hmem y (hUsubK hy), hApos y (hUsubK hy)⟩
  have hGcont : ContinuousOn Gp (interior K) := by
    have hcomp : ContinuousOn (fun y : ℝ × ℝ => (ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ))
        (fderiv ℝ F y)) D :=
      (ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).continuous.comp_continuousOn
        (continuousOn_fderiv_swirlQuotient_int hu)
    exact hcomp.mono hUD
  have hGp_eq : ∀ y ∈ K, Gp y =
      1 / (rc / lam + y.1) * dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) (y, τ) := by
    intro y hy
    exact fderiv_swirlQuotient_eq_int hu (hmem y hy) (hApos y hy)
  have hpointwise : ∀ y : ℝ × ℝ, Gp y * ψ y =
      (1 / (rc / lam + y.1) *
        dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) (y, τ)) * ψ y := by
    intro y
    by_cases hyK : y ∈ K
    · rw [hGp_eq y hyK]
    · have hynotsupp : y ∉ tsupport ψ := fun hcontra => hyK (hUsubK (hψU hcontra))
      rw [image_eq_zero_of_notMem_tsupport hynotsupp, mul_zero, mul_zero]
  have hintGpψ : Integrable fun y : ℝ × ℝ => Gp y * ψ y :=
    (continuous_mul_of_tsupport_subset_pairing (isOpen_interior (s := K)) hGcont hψ.continuous
      hψU).integrable_of_hasCompactSupport hψc.mul_left
  exact hintGpψ.congr (Filter.Eventually.of_forall hpointwise)

/-! ### The force term `T5` -/

/-- Integrability of the force term of `zoomTheta_pde_divergenceForm` against a test function
`ψ` supported in the interior of a compact set `K`, at a fixed zoom scale. Uses the force's own
smoothness (from `IsClassicalSolutionOn`) composed with the smooth recentred zoom point,
exposed for `CIV.dtPast_zoomTheta_pairing_bound_fixed`'s `hint5`. -/
theorem integrable_forceTerm_mul_zoomTheta {lam h rc zc : ℝ}
    {f : ParabolicPoint → Vec3} (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    {K : Set (ℝ × ℝ)} {τ : ℝ}
    (hmem : ∀ y ∈ K, zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ interior K) :
    Integrable fun y : ℝ × ℝ =>
      (lam ^ 4 * lam ^ (2 * h) * curlComp f 1 (zoomPointRec lam h rc zc (y, τ))) * ψ y := by
  set D : Set (ℝ × ℝ) := {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} with hD_def
  have hUsubK : interior K ⊆ K := interior_subset
  have hUD : interior K ⊆ D := fun y hy => hmem y (hUsubK hy)
  have hζ : ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => zoomPointRec lam h rc zc (y, τ)) := contDiff_zoomPointRec_atTau_int lam
        h rc zc τ
  have hcurlSmooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => curlComp f 1 (zoomPointRec lam h rc zc (y, τ))) D :=
    (contDiffOn_curlComp_public hf 1).comp hζ.contDiffOn (fun y hy => hy)
  have hscaledSmooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => lam ^ 4 * lam ^ (2 * h) * curlComp f 1 (zoomPointRec lam h rc zc (y,
        τ))) D :=
    hcurlSmooth.const_smul (lam ^ 4 * lam ^ (2 * h))
  have hscaledCont : ContinuousOn
      (fun y : ℝ × ℝ => lam ^ 4 * lam ^ (2 * h) * curlComp f 1 (zoomPointRec lam h rc zc (y, τ)))
      (interior K) :=
    hscaledSmooth.continuousOn.mono hUD
  exact (continuous_mul_of_tsupport_subset_pairing (isOpen_interior (s := K)) hscaledCont
    hψ.continuous hψU).integrable_of_hasCompactSupport hψc.mul_left

end CIV
