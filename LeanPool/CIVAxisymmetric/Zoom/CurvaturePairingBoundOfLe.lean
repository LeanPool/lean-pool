/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingCurvatureVanish
public import LeanPool.CIVAxisymmetric.Zoom.ThetaLipschitz
public import LeanPool.CIVAxisymmetric.Zoom.OmegaEquicontinuous

/-!
# The curvature-term pairing bound with a general lower bound on the radius

The fixed-scale curvature-term pairing bound of `CIV.Zoom.RecedingCurvaturePairingBound`, with the
offset `A + R` of `eq:aniso:zoom:receding:equation` bounded below by an arbitrary `ε > 0` rather
than by `1`. With `A = 0` this is the bound used on compact subsets of the open half-plane in the
finite-axis compactness argument `eq:aniso:zoom:finite:compactness`.
-/

public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- The curvature-coefficient quotient `Θ(·, τ) / (A + ·)` is smooth on the open set where
the recentred zoom point lies in the unit cylinder and the offset `A + R` is positive. -/
private theorem contDiffOn_curvatureQuotient {lam h rc zc τ : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} := by
  set D : Set (ℝ × ℝ) :=
    {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} with hD_def
  have hζ : ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞)
      (fun y : ℝ × ℝ => zoomPointRec lam h rc zc (y, τ)) :=
    (contDiff_zoomPointRec lam h rc zc).comp (contDiff_id.prodMk contDiff_const)
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
    (contDiff_const.add (contDiff_fst)).contDiffOn
  have hAne : ∀ y ∈ D, rc / lam + y.1 ≠ 0 := fun y hy => (hy.2).ne'
  exact hTheta.div hA hAne

/-- The domain of `contDiffOn_curvatureQuotient` is open. -/
private theorem isOpen_curvatureDomain (lam h rc zc τ : ℝ) :
    IsOpen {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} := by
  have h1 : IsOpen {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} :=
    (isOpen_zoomPointRec_preimage lam h rc zc).preimage (continuous_id.prodMk continuous_const)
  have h2 : IsOpen {y : ℝ × ℝ | (0 : ℝ) < rc / lam + y.1} :=
    isOpen_lt continuous_const (continuous_const.add continuous_fst)
  exact h1.inter h2

/-- The `fderiv`-bundled derivative of the curvature quotient is itself continuous on the
domain, since the quotient is smooth there. -/
private theorem continuousOn_fderiv_curvatureQuotient {lam h rc zc τ : ℝ}
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z)
      unitCylinder) :
    ContinuousOn
      (fderiv ℝ (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1)))
      {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} :=
  ((contDiffOn_curvatureQuotient hu).fderiv_of_isOpen (m := 0)
    (isOpen_curvatureDomain lam h rc zc τ) (by norm_num)).continuousOn

/-- The derivative of the first slice of a differentiable function of `ℝ × ℝ` is the first
directional derivative, the local copy of the private helper of `CIV.Zoom.OmegaEquicontinuous`
(unavailable there by name since it is declared `private`). -/
private theorem hasDerivAt_slice_fst_local {F : ℝ × ℝ → ℝ} {y : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F y) :
    HasDerivAt (fun t : ℝ => F (t, y.2)) (fderiv ℝ F y (1, 0)) y.1 := by
  have hline : HasDerivAt (fun t : ℝ => (t, y.2)) ((1 : ℝ), (0 : ℝ)) y.1 :=
    (hasDerivAt_id y.1).prodMk (hasDerivAt_const y.1 y.2)
  exact HasFDerivAt.comp_hasDerivAt_of_eq (hl := hF.hasFDerivAt) (hf := hline) (hy := rfl)

/-- The `fderiv`-bundled derivative of the curvature quotient, at the basis vector `(1, 0)`,
agrees with the closed-form curvature term `∂_R Θ_n / (A + R) − Θ_n / (A + R)²` of
`zoomTheta_pde`, by uniqueness of derivatives against `hasDerivAt_curvatureQuotient_slice`. -/
private theorem hasDerivAt_curvatureQuotient_slice {lam h rc zc τ : ℝ} (hlam : 0 < lam)
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
curvature term on the domain, connecting `continuousOn_fderiv_curvatureQuotient`'s continuity
to the algebraic shape `zoomTheta_pde` needs. -/
private theorem fderiv_curvatureQuotient_eq {lam h rc zc τ : ℝ} (hlam : 0 < lam)
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
    ((contDiffOn_curvatureQuotient hu).differentiableOn (by norm_num) y hDcontains)
      |>.differentiableAt ((isOpen_curvatureDomain lam h rc zc τ).mem_nhds hDcontains)
  have hslice := hasDerivAt_slice_fst_local hFdiff
  have hexplicit := hasDerivAt_curvatureQuotient_slice hlam hu hp hApos
  exact hslice.unique hexplicit

/-- The curvature-quotient coefficient `Θ_n / (A + R)` is bounded by `2C` once the offset
`A + R` is at least `1` and the scale obeys `δ = lam ^ (2h) ≤ 1`, from `abs_zoomTheta_le`. -/
private theorem abs_curvatureQuotient_le {C h lam rc zc τ : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hh1 : h ≤ 1 / 2) (hlam : 0 < lam) (hdelta : lam ^ (2 * h) ≤ 1) (htau : τ ≤ -1)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    {y : ℝ × ℝ} (hp : zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder) {ε : ℝ} (hε : 0 < ε)
    (hApos : ε ≤ rc / lam + y.1) :
    |zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1)| ≤ 2 * C / ε := by
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
  have hΘ2C : |zoomTheta lam h rc zc u (y, τ)| ≤ 2 * C := by
    have hstep : (lam ^ (2 * h)) ^ 2 * (-τ) ^ (-1 + h : ℝ) + (-τ) ^ (-1 - h : ℝ) ≤ 1 + 1 := by
      have h1 : (lam ^ (2 * h)) ^ 2 * (-τ) ^ (-1 + h : ℝ) ≤ 1 * 1 :=
        mul_le_mul hδsq hpow1 hpow1nn (by norm_num)
      nlinarith only [h1, hpow2]
    have : C * ((lam ^ (2 * h)) ^ 2 * (-τ) ^ (-1 + h : ℝ) + (-τ) ^ (-1 - h : ℝ)) ≤ C * (1 + 1) :=
      mul_le_mul_of_nonneg_left hstep hC
    have hfinal : C * (1 + 1) = 2 * C := by ring
    linarith only [hΘ, this, hfinal]
  have hApos' : (0 : ℝ) < rc / lam + y.1 := by linarith only [hApos, hε]
  rw [abs_div, abs_of_pos hApos']
  have hCnn : (0 : ℝ) ≤ 2 * C := by linarith only [hC]
  calc |zoomTheta lam h rc zc u (y, τ)| / (rc / lam + y.1)
      ≤ (2 * C) / (rc / lam + y.1) := by
        gcongr
    _ ≤ 2 * C / ε := div_le_div_of_nonneg_left hCnn hε hApos

/-- The curvature-term pairing bound at a fixed zoom scale: the integral of the curvature
term `∂_R Θ_n / (A + R) − Θ_n / (A + R)²` of `zoomTheta_pde` against a test function
supported in the interior of a compact set `K` is bounded by `2C` times the bound `B` on
`ψ` and its first two derivatives, times the volume of `K`. -/
theorem curvature_term_pairing_bound_fixed_of_le {C h lam rc zc : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hh1 : h ≤ 1 / 2) (hlam : 0 < lam) (hdelta : lam ^ (2 * h) ≤ 1)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {τ : ℝ} (htau : τ ≤ -1)
    (hmem : ∀ y ∈ K, zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    {ε : ℝ} (hε : 0 < ε) (hApos : ∀ y ∈ K, ε ≤ rc / lam + y.1)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ interior K) (B : ℝ) (_ : 0 ≤ B)
    (hψB : ∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) :
    |∫ y : ℝ × ℝ,
        (dr (zoomTheta lam h rc zc u) (y, τ) / (rc / lam + y.1)
            - zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1) ^ 2) * ψ y|
      ≤ 2 * C / ε * (volume K).toReal * B := by
  set F : ℝ × ℝ → ℝ := fun y => zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1) with hF_def
  set Gp : ℝ × ℝ → ℝ := fun y => fderiv ℝ F y (1, 0) with hGp_def
  set D : Set (ℝ × ℝ) :=
    {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder ∧ 0 < rc / lam + y.1} with hD_def
  have hUsubK : interior K ⊆ K := interior_subset
  have hUD : interior K ⊆ D := fun y hy => ⟨hmem y (hUsubK hy), by
    have := hApos y (hUsubK hy); linarith only [this, hε]⟩
  have hFcont : ContinuousOn F (interior K) :=
    ((contDiffOn_curvatureQuotient hu).continuousOn).mono hUD
  have hGcont : ContinuousOn Gp (interior K) := by
    have hcomp : ContinuousOn (fun y : ℝ × ℝ => (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ))
        (fderiv ℝ F y)) D :=
      (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).continuous.comp_continuousOn
        (continuousOn_fderiv_curvatureQuotient hu)
    exact hcomp.mono hUD
  have hFderiv : ∀ y ∈ interior K, HasDerivAt (fun t : ℝ => F (t, y.2)) (Gp y) y.1 := by
    intro y hy
    have hyD : y ∈ D := hUD hy
    have hFdiff : DifferentiableAt ℝ F y :=
      ((contDiffOn_curvatureQuotient hu).differentiableOn (by norm_num) y hyD)
        |>.differentiableAt (isOpen_curvatureDomain lam h rc zc τ |>.mem_nhds hyD)
    exact hasDerivAt_slice_fst_local hFdiff
  have hIBP := integral_partial_fst_mul_eq_neg (isOpen_interior (s := K)) hFcont hGcont hFderiv
    hψ hψc hψU
  have hGp_eq : ∀ y ∈ K, Gp y =
      dr (zoomTheta lam h rc zc u) (y, τ) / (rc / lam + y.1)
        - zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1) ^ 2 := by
    intro y hy
    have hApos' : (0 : ℝ) < rc / lam + y.1 := by have := hApos y hy; linarith only [this, hε]
    exact fderiv_curvatureQuotient_eq hlam hu (hmem y hy) hApos'
  have hpointwise : ∀ y : ℝ × ℝ, Gp y * ψ y =
      (dr (zoomTheta lam h rc zc u) (y, τ) / (rc / lam + y.1)
        - zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1) ^ 2) * ψ y := by
    intro y
    by_cases hyK : y ∈ K
    · rw [hGp_eq y hyK]
    · have hynotsupp : y ∉ tsupport ψ := fun hcontra => hyK (hUsubK (hψU hcontra))
      rw [image_eq_zero_of_notMem_tsupport hynotsupp, mul_zero, mul_zero]
  have hintegral_eq : (∫ y : ℝ × ℝ, Gp y * ψ y) =
      ∫ y : ℝ × ℝ,
        (dr (zoomTheta lam h rc zc u) (y, τ) / (rc / lam + y.1)
            - zoomTheta lam h rc zc u (y, τ) / (rc / lam + y.1) ^ 2) * ψ y :=
    integral_congr_ae (Filter.Eventually.of_forall hpointwise)
  rw [hintegral_eq] at hIBP
  set ψ₁ : ℝ × ℝ → ℝ := fun y => deriv (fun t : ℝ => ψ (t, y.2)) y.1 with hψ₁_def
  have hψ₁_eq : ∀ y : ℝ × ℝ, ψ₁ y = fderiv ℝ ψ y (1, 0) := fun y =>
    (hasDerivAt_slice_fst_local (hψ.differentiable (by simp) y)).deriv
  have hψ₁_bound : ∀ y, |ψ₁ y| ≤ B := by
    intro y
    rw [hψ₁_eq]
    have hle : ‖fderiv ℝ ψ y (1, 0)‖ ≤ ‖fderiv ℝ ψ y‖ * ‖((1, 0) : ℝ × ℝ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hnorm1 : ‖((1, 0) : ℝ × ℝ)‖ = 1 := by
      rw [Prod.norm_def]
      norm_num
    rw [hnorm1, mul_one] at hle
    calc |fderiv ℝ ψ y (1, 0)| = ‖fderiv ℝ ψ y (1, 0)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ ψ y‖ := hle
      _ ≤ B := (hψB y).2.1
  have hψ₁_supp : tsupport ψ₁ ⊆ K := by
    have h1 : tsupport ψ₁ ⊆ tsupport ψ := by
      rw [hψ₁_def]
      have hfe : (fun y : ℝ × ℝ => deriv (fun t : ℝ => ψ (t, y.2)) y.1) =
          fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0) := funext hψ₁_eq
      rw [hfe]
      exact tsupport_fderiv_apply_subset ℝ (1, 0)
    exact h1.trans (hψU.trans hUsubK)
  have hFbound : ∀ y ∈ K, |F y| ≤ 2 * C / ε := fun y hy =>
    abs_curvatureQuotient_le hC hh0 hh1 hlam hdelta htau hb (hu.of_le (by norm_num))
      (hmem y hy) hε (hApos y hy)
  have hfinal := abs_integral_mul_le_of_tsupport_subset hK.measure_lt_top hψ₁_supp hFbound
    hψ₁_bound
  rw [hIBP, abs_neg]
  refine hfinal.trans_eq ?_
  ring

end CIV
