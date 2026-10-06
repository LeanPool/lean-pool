/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingEquation
public import LeanPool.CIVAxisymmetric.Zoom.OmegaEquicontinuous

/-!
# Receding Swirl Pairing Bound

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- The recentred zoom point restricted to a fixed time `τ`, as a map of the meridional
plane alone, is smooth. -/
private theorem contDiff_zoomPointRec_atTau_swirl (lam h rc zc τ : ℝ) :
    ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞) (fun y : ℝ × ℝ => zoomPointRec lam h rc zc (y, τ)) :=
  (contDiff_zoomPointRec lam h rc zc).comp (contDiff_id.prodMk contDiff_const)

/-- The conservative swirl source `S_n² / (A + R)` is smooth on the open set where the
recentred zoom point lies in the unit cylinder and the offset `A + R` is positive. -/
private theorem contDiffOn_swirlQuotient {lam h rc zc τ : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => zoomSRec lam h rc zc u (y, τ) ^ 2 / (rc / lam + y.1))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} := by
  set D : Set (ℝ × ℝ) :=
    {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} with hD_def
  have hζ : ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => zoomPointRec lam h rc zc (y, τ)) :=
    contDiff_zoomPointRec_atTau_swirl lam h rc zc τ
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

/-- The domain of `contDiffOn_swirlQuotient` is open. -/
private theorem isOpen_swirlDomain (lam h rc zc τ : ℝ) :
    IsOpen {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} := by
  have h1 : IsOpen {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} :=
    (isOpen_zoomPointRec_preimage lam h rc zc).preimage (continuous_id.prodMk continuous_const)
  have h2 : IsOpen {y : ℝ × ℝ | (0 : ℝ) < rc / lam + y.1} :=
    isOpen_lt continuous_const (continuous_const.add continuous_fst)
  exact h1.inter h2

/-- The `fderiv`-bundled derivative of the swirl quotient is continuous on the domain. -/
private theorem continuousOn_fderiv_swirlQuotient {lam h rc zc τ : ℝ}
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z)
      unitCylinder) :
    ContinuousOn
      (fderiv ℝ (fun y : ℝ × ℝ => zoomSRec lam h rc zc u (y, τ) ^ 2 / (rc / lam + y.1)))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} :=
  ((contDiffOn_swirlQuotient hu).fderiv_of_isOpen (m := 0)
    (isOpen_swirlDomain lam h rc zc τ) (by norm_num)).continuousOn

/-- The derivative of the second slice of a differentiable function of `ℝ × ℝ` is the second
directional derivative, the local copy of the private helper of
`CIV.Zoom.OmegaEquicontinuous`. -/
private theorem hasDerivAt_slice_snd_local {F : ℝ × ℝ → ℝ} {y : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F y) :
    HasDerivAt (fun s : ℝ => F (y.1, s)) (fderiv ℝ F y (0, 1)) y.2 := by
  have hline : HasDerivAt (fun s : ℝ => (y.1, s)) ((0 : ℝ), (1 : ℝ)) y.2 :=
    (hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2)
  exact HasFDerivAt.comp_hasDerivAt_of_eq (hl := hF.hasFDerivAt) (hf := hline) (hy := rfl)

/-- `S_n²` differentiates in `Z` to the vertical derivative `∂_Z(S_n²)`, the identity
`zoomTheta_pde`'s own proof establishes inline for the swirl-source term. -/
private theorem hasDerivAt_dz_zoomSRecSq (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
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

/-- The swirl quotient's slice derivative in `Z` equals `(1 / (A + R)) ∂_Z(S_n²)`, the
identity `dz_zoomSRecSq_div_eq` gives for the swirl-source term of `zoomTheta_pde`. -/
private theorem hasDerivAt_swirlQuotient_slice {lam h rc zc τ : ℝ}
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {y : ℝ × ℝ} (hp : zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => zoomSRec lam h rc zc u ((y.1, s), τ) ^ 2 / (rc / lam + y.1))
      (1 / (rc / lam + y.1) * dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) (y, τ))
      y.2 := by
  have hS' := hasDerivAt_dz_zoomSRecSq lam h rc zc u hu (y, τ) hp
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
private theorem fderiv_swirlQuotient_eq {lam h rc zc τ : ℝ}
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
    ((contDiffOn_swirlQuotient hu).differentiableOn (by norm_num) y hDcontains)
      |>.differentiableAt ((isOpen_swirlDomain lam h rc zc τ).mem_nhds hDcontains)
  have hslice := hasDerivAt_slice_snd_local hFdiff
  have hexplicit := hasDerivAt_swirlQuotient_slice hu hp
  exact hslice.unique hexplicit

/-- The swirl quotient `S_n² / (A + R)` is bounded by `CΓ²` once the offset `A + R` is at
least `1` and the scale obeys `δ = lam ^ (2h) ≤ 1`, from `abs_zoomSRecSq_div_le`. -/
private theorem abs_swirlQuotient_le {lam h rc zc CΓ τ : ℝ} (hlam : 0 < lam)
    (hdelta : lam ^ (2 * h) ≤ 1) (hCΓ : 0 ≤ CΓ)
    {u : ParabolicPoint → Vec3} {y : ℝ × ℝ}
    (hΓ : |circulation u (zoomPointRec lam h rc zc (y, τ))| ≤ CΓ)
    (hApos : 1 ≤ rc / lam + y.1) :
    |zoomSRec lam h rc zc u (y, τ) ^ 2 / (rc / lam + y.1)| ≤ CΓ ^ 2 := by
  have hApos' : (0 : ℝ) < rc / lam + y.1 := by linarith only [hApos]
  have hbound := abs_zoomSRecSq_div_le hlam hApos' hCΓ hΓ
  have hδnn : (0 : ℝ) ≤ lam ^ (2 * h) := Real.rpow_nonneg hlam.le _
  have hδsq : (lam ^ (2 * h)) ^ 2 ≤ 1 := by nlinarith only [hδnn, hdelta]
  have hcube : (1 : ℝ) ≤ (rc / lam + y.1) ^ 3 := by
    have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hApos 3
    simpa using h3
  have hcube_pos : (0 : ℝ) < (rc / lam + y.1) ^ 3 := by positivity
  have hCΓsq : (0 : ℝ) ≤ CΓ ^ 2 := sq_nonneg CΓ
  have hratio : (lam ^ (2 * h)) ^ 2 / (rc / lam + y.1) ^ 3 ≤ 1 := by
    rw [div_le_one hcube_pos]
    linarith only [hδsq, hcube]
  calc |zoomSRec lam h rc zc u (y, τ) ^ 2 / (rc / lam + y.1)|
      ≤ CΓ ^ 2 * (lam ^ (2 * h)) ^ 2 / (rc / lam + y.1) ^ 3 := hbound
    _ = CΓ ^ 2 * ((lam ^ (2 * h)) ^ 2 / (rc / lam + y.1) ^ 3) := by rw [mul_div_assoc]
    _ ≤ CΓ ^ 2 * 1 := mul_le_mul_of_nonneg_left hratio hCΓsq
    _ = CΓ ^ 2 := by ring

/-- The swirl-source pairing bound at a fixed zoom scale: the integral of the
divergence-form swirl term `(1/(A+R)) ∂_Z(S_n²)` of `zoomTheta_pde` against a test
function supported in the interior of a compact set `K` is bounded by `CΓ²` times the
bound `B` on `ψ` and its first two derivatives, times the volume of `K`. -/
theorem swirl_term_pairing_bound_fixed {h lam rc zc CΓ : ℝ} (hCΓ : 0 ≤ CΓ) (hlam : 0 < lam)
    (hdelta : lam ^ (2 * h) ≤ 1) {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {τ : ℝ}
    (hmem : ∀ y ∈ K, zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    (hΓ : ∀ y ∈ K, |circulation u (zoomPointRec lam h rc zc (y, τ))| ≤ CΓ)
    (hApos : ∀ y ∈ K, (1 : ℝ) ≤ rc / lam + y.1)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ interior K) (B : ℝ) (_ : 0 ≤ B)
    (hψB : ∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) :
    |∫ y : ℝ × ℝ,
        (1 / (rc / lam + y.1) * dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2)
          (y, τ)) * ψ y|
      ≤ CΓ ^ 2 * (volume K).toReal * B := by
  set F : ℝ × ℝ → ℝ := fun y => zoomSRec lam h rc zc u (y, τ) ^ 2 / (rc / lam + y.1) with hF_def
  set Gp : ℝ × ℝ → ℝ := fun y => fderiv ℝ F y (0, 1) with hGp_def
  set D : Set (ℝ × ℝ) :=
    {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} with hD_def
  have hUsubK : interior K ⊆ K := interior_subset
  have hUD : interior K ⊆ D := fun y hy => ⟨hmem y (hUsubK hy), by
    have := hApos y (hUsubK hy); linarith only [this]⟩
  have hFcont : ContinuousOn F (interior K) :=
    ((contDiffOn_swirlQuotient hu).continuousOn).mono hUD
  have hGcont : ContinuousOn Gp (interior K) := by
    have hcomp : ContinuousOn (fun y : ℝ × ℝ => (ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ))
        (fderiv ℝ F y)) D :=
      (ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).continuous.comp_continuousOn
        (continuousOn_fderiv_swirlQuotient hu)
    exact hcomp.mono hUD
  have hFderiv : ∀ y ∈ interior K, HasDerivAt (fun s : ℝ => F (y.1, s)) (Gp y) y.2 := by
    intro y hy
    have hyD : y ∈ D := hUD hy
    have hFdiff : DifferentiableAt ℝ F y :=
      ((contDiffOn_swirlQuotient hu).differentiableOn (by norm_num) y hyD)
        |>.differentiableAt (isOpen_swirlDomain lam h rc zc τ |>.mem_nhds hyD)
    exact hasDerivAt_slice_snd_local hFdiff
  have hIBP := integral_partial_snd_mul_eq_neg (isOpen_interior (s := K)) hFcont hGcont hFderiv
    hψ hψc hψU
  have hGp_eq : ∀ y ∈ K, Gp y =
      1 / (rc / lam + y.1) * dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) (y, τ) := by
    intro y hy
    have hApos' : (0 : ℝ) < rc / lam + y.1 := by have := hApos y hy; linarith only [this]
    exact fderiv_swirlQuotient_eq hu (hmem y hy) hApos'
  have hpointwise : ∀ y : ℝ × ℝ, Gp y * ψ y =
      (1 / (rc / lam + y.1) * dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) (y, τ))
        * ψ y := by
    intro y
    by_cases hyK : y ∈ K
    · rw [hGp_eq y hyK]
    · have hynotsupp : y ∉ tsupport ψ := fun hcontra => hyK (hUsubK (hψU hcontra))
      rw [image_eq_zero_of_notMem_tsupport hynotsupp, mul_zero, mul_zero]
  have hintegral_eq : (∫ y : ℝ × ℝ, Gp y * ψ y) =
      ∫ y : ℝ × ℝ,
        (1 / (rc / lam + y.1) * dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec lam h rc zc u q ^ 2) (y, τ))
          * ψ y :=
    integral_congr_ae (Filter.Eventually.of_forall hpointwise)
  rw [hintegral_eq] at hIBP
  set ψ₁ : ℝ × ℝ → ℝ := fun y => deriv (fun s : ℝ => ψ (y.1, s)) y.2 with hψ₁_def
  have hψ₁_eq : ∀ y : ℝ × ℝ, ψ₁ y = fderiv ℝ ψ y (0, 1) := fun y =>
    (hasDerivAt_slice_snd_local (hψ.differentiable (by simp) y)).deriv
  have hψ₁_bound : ∀ y, |ψ₁ y| ≤ B := by
    intro y
    rw [hψ₁_eq]
    have hle : ‖fderiv ℝ ψ y (0, 1)‖ ≤ ‖fderiv ℝ ψ y‖ * ‖((0, 1) : ℝ × ℝ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hnorm1 : ‖((0, 1) : ℝ × ℝ)‖ = 1 := by
      rw [Prod.norm_def]
      norm_num
    rw [hnorm1, mul_one] at hle
    calc |fderiv ℝ ψ y (0, 1)| = ‖fderiv ℝ ψ y (0, 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ ψ y‖ := hle
      _ ≤ B := (hψB y).2.1
  have hψ₁_supp : tsupport ψ₁ ⊆ K := by
    have h1 : tsupport ψ₁ ⊆ tsupport ψ := by
      rw [hψ₁_def]
      have hfe : (fun y : ℝ × ℝ => deriv (fun s : ℝ => ψ (y.1, s)) y.2) =
          fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1) := funext hψ₁_eq
      rw [hfe]
      exact tsupport_fderiv_apply_subset ℝ (0, 1)
    exact h1.trans (hψU.trans hUsubK)
  have hFbound : ∀ y ∈ K, |F y| ≤ CΓ ^ 2 := fun y hy =>
    abs_swirlQuotient_le hlam hdelta hCΓ (hΓ y hy) (hApos y hy)
  have hfinal := abs_integral_mul_le_of_tsupport_subset hK.measure_lt_top hψ₁_supp hFbound
    hψ₁_bound
  rw [hIBP, abs_neg]
  refine hfinal.trans_eq ?_
  ring

/-- The eventual-in-`n` pairing bound for the swirl term: `C₀ := CΓ²` is chosen before `n`,
matching the eventual form of the time-pairing estimate `hpair` of the receding compactness. -/
theorem swirl_term_pairing_bound {h : ℝ} {rc zc CΓ : ℝ} (hCΓ : 0 ≤ CΓ)
    (lam : ℕ → ℝ) (hlam_pos : ∀ n, 0 < lam n) (hlam_le : ∀ᶠ n in atTop, lam n ^ (2 * h) ≤ 1)
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {τ : ℝ}
    (hmem : ∀ᶠ n in atTop, ∀ y ∈ K, zoomPointRec (lam n) h rc zc (y, τ) ∈ unitCylinder)
    (hΓ : ∀ᶠ n in atTop, ∀ y ∈ K, |circulation u (zoomPointRec (lam n) h rc zc (y, τ))| ≤ CΓ)
    (hApos : ∀ᶠ n in atTop, ∀ y ∈ K, (1 : ℝ) ≤ rc / lam n + y.1) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ interior K →
      ∀ B : ℝ, 0 ≤ B →
        (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
        ∀ᶠ n in atTop,
          |∫ y : ℝ × ℝ,
              (1 / (rc / lam n + y.1) *
                  dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec (lam n) h rc zc u q ^ 2) (y, τ)) * ψ y|
            ≤ C₀ * B := by
  refine ⟨CΓ ^ 2 * (volume K).toReal, by positivity, fun ψ hψ hψc hψU B hB hψB => ?_⟩
  filter_upwards [hlam_le, hmem, hΓ, hApos] with n hlam_len hmem_n hΓ_n hApos_n
  exact swirl_term_pairing_bound_fixed hCΓ (hlam_pos n) hlam_len hu hK hmem_n hΓ_n hApos_n ψ hψ
    hψc hψU B hB hψB

end CIV
