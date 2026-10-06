/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingCompactnessMovingCentre
public import LeanPool.CIVAxisymmetric.Zoom.RecedingWRecValueBound
public import LeanPool.CIVAxisymmetric.Zoom.ZoomLimitComparisonVanishing
public import LeanPool.CIVAxisymmetric.Zoom.VRecLipschitz
public import LeanPool.CIVAxisymmetric.Zoom.WRecLipschitz
public import LeanPool.CIVAxisymmetric.Zoom.EndpointFiniteAxis
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The receding-branch drift and its continuity, boundedness, and measurability inputs

At the receding zoom centre `x_n = (r_n, z_n)` of the proof of `prop:aniso:small`
(`eq:aniso:zoom:receding:variables`), this file packages the meridional drift `(V_n, W_n)`
and its divergence `eq:aniso:zoom:receding:div` as a genuine drift pair on `Vec 2 × ℝ`, and
proves the eventual continuity/Lipschitz/weak-divergence inputs and the eventual
measurability/boundedness inputs that the extraction of an admissible drift limit
(`CIV.exists_subseq_admissibleDrift`) needs at this branch, at the moving zoom centre
`(rc n, zc n)` with `r_n / λ_n → ∞`.
-/

public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The receding drift `(V_n, W_n)` on `Vec 2 × ℝ`, lifted from the meridional plane. -/
@[expose] def recDrift (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3) (z : Vec 2 × ℝ) : Vec 2 :=
  ![zoomVRec lam h rc zc u (planeLiftPoint z), zoomWRec lam h rc zc u (planeLiftPoint z)]

/-- Its divergence `∂_R V_n + ∂_Z W_n = -V_n / (A_n + R)` (`eq:aniso:zoom:receding:div`). -/
@[expose] def recDriftDiv (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3) (z : Vec 2 × ℝ) : ℝ :=
  -(zoomVRec lam h rc zc u (planeLiftPoint z) / (rc / lam + z.1 0))

/-! ### Enclosing a compact subset of `Vec 2 × ℝ` in a plane-and-time box -/

/-- A compact subset of `Vec 2 × ℝ` with time bounded by `-1` is contained in the box
`Kp ×ˢ J` of its projections, with `J` also bounded by `-1`. -/
private theorem exists_box_of_isCompact_vec2 {K : Set (Vec 2 × ℝ)} (hK : IsCompact K)
    (hKsub : K ⊆ univ ×ˢ Iic (-1 : ℝ)) :
    ∃ (Kp : Set (ℝ × ℝ)) (J : Set ℝ), IsCompact Kp ∧ IsCompact J ∧ (∀ τ ∈ J, τ ≤ -1) ∧
      ∀ z ∈ K, (z.1 0, z.1 1) ∈ Kp ∧ z.2 ∈ J := by
  have hc0 : Continuous (fun z : Vec 2 × ℝ => z.1 0) := (continuous_apply 0).comp continuous_fst
  have hc1 : Continuous (fun z : Vec 2 × ℝ => z.1 1) := (continuous_apply 1).comp continuous_fst
  have hcp : Continuous (fun z : Vec 2 × ℝ => (z.1 0, z.1 1)) := hc0.prodMk hc1
  refine ⟨(fun z : Vec 2 × ℝ => (z.1 0, z.1 1)) '' K, Prod.snd '' K,
    hK.image hcp, hK.image continuous_snd, ?_, fun z hz => ⟨⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩⟩
  rintro τ ⟨z, hz, rfl⟩
  exact (hKsub hz).2

/-- Eventually in `n`, the receding zoom point of every point of a compact `K ⊆ Vec 2 × ℝ`
with `K ⊆ univ ×ˢ Iic (-1)` lies in the unit cylinder. -/
private theorem eventually_mem_unitCylinder_of_isCompact_vec2
    {h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {rc zc : ℕ → ℝ} (hcz : ∀ n, rc n ^ 2 + zc n ^ 2 ≤ ρ ^ 2)
    (lam : ℕ → ℝ) (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    {K : Set (Vec 2 × ℝ)} (hK : IsCompact K) (hKsub : K ⊆ univ ×ˢ Iic (-1 : ℝ)) :
    ∀ᶠ n in atTop, ∀ z ∈ K,
      zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint z) ∈ unitCylinder := by
  obtain ⟨Kp, J, hKp, hJ, hJsub, hbox⟩ := exists_box_of_isCompact_vec2 hK hKsub
  filter_upwards [eventually_zoomPointRec_mem_unitCylinder_moving hh hρ0 hρ1 hcz lam hlam_lim Kp
    hKp J hJ hJsub] with n hn
  intro z hz
  obtain ⟨hzp, hzτ⟩ := hbox z hz
  exact hn (z.1 0, z.1 1) hzp z.2 hzτ

/-- Eventually in `n`, `A_n + R ≥ 1` for `R` ranging over the radial projection of a
compact `K ⊆ Vec 2 × ℝ`. -/
private theorem eventually_one_le_ratio_add_of_isCompact_vec2
    {rc : ℕ → ℝ} {lam : ℕ → ℝ} (hA : Tendsto (fun n => rc n / lam n) atTop atTop)
    {K : Set (Vec 2 × ℝ)} (hK : IsCompact K) :
    ∀ᶠ n in atTop, ∀ z ∈ K, (1 : ℝ) ≤ rc n / lam n + z.1 0 := by
  have hc0 : Continuous (fun z : Vec 2 × ℝ => z.1 0) := (continuous_apply 0).comp continuous_fst
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc0.continuousOn
  filter_upwards [hA.eventually_ge_atTop (B + 1)] with n hn
  intro z hz
  have h1 : |z.1 0| ≤ B := by
    have := hB z hz
    rwa [Real.norm_eq_abs] at this
  linarith only [hn, (abs_le.mp h1).1]

/-- The rescaled azimuthal vorticity `Θ_n` is bounded by `2C` at `τ ≤ -1` and `λ ≤ 1`. -/
private theorem abs_zoomTheta_le_two_mul {C h lam rc zc : ℝ} (hh : 0 < h ∧ h < 1 / 2)
    (hC : 0 ≤ C) (hlam_pos : 0 < lam) (hlam_le : lam ≤ 1) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {p : (ℝ × ℝ) × ℝ} (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (hτ : p.2 ≤ -1) :
    |zoomTheta lam h rc zc u p| ≤ 2 * C := by
  have hΘ := abs_zoomTheta_le C h lam rc zc hlam_pos u hb (hu.of_le (by norm_num)) p hp
  have hτ1 : (1 : ℝ) ≤ -p.2 := by linarith only [hτ]
  have e1 : (-p.2) ^ (-1 + h : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by
    linarith only [hh.2])
  have e2 : (-p.2) ^ (-1 - h : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by
    linarith only [hh.1])
  have e1' : 0 ≤ (-p.2) ^ (-1 + h : ℝ) := Real.rpow_nonneg (by linarith only [hτ1]) _
  have hd0 : 0 ≤ lam ^ (2 * h) := Real.rpow_nonneg hlam_pos.le _
  have hd1 : lam ^ (2 * h) ≤ 1 := Real.rpow_le_one hlam_pos.le hlam_le (by linarith only [hh.1])
  have hd2 : (lam ^ (2 * h)) ^ 2 ≤ 1 := by nlinarith only [hd0, hd1]
  have hprod : (lam ^ (2 * h)) ^ 2 * (-p.2) ^ (-1 + h : ℝ) ≤ 1 := by
    nlinarith only [hd2, e1, e1', sq_nonneg (lam ^ (2 * h))]
  have hsum : (lam ^ (2 * h)) ^ 2 * (-p.2) ^ (-1 + h : ℝ) + (-p.2) ^ (-1 - h : ℝ) ≤ 2 := by
    linarith only [hprod, e2]
  calc |zoomTheta lam h rc zc u p|
      ≤ C * ((lam ^ (2 * h)) ^ 2 * (-p.2) ^ (-1 + h : ℝ) + (-p.2) ^ (-1 - h : ℝ)) := hΘ
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left hsum hC
    _ = 2 * C := by ring

/-! ### R2-B: bounds and measurability of the receding sequences -/

/-- R2-B: local bounds and measurability of the receding sequences `Θ_n`, `(V_n, W_n)`, and
the divergence `-V_n / (A_n + R)`, at the moving zoom centre `(rc n, zc n)`. -/
theorem recDrift_bounds
    {h ρ Rstar C : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ) (hρR : ρ < Rstar) (hR1 : Rstar ≤ 1)
    {rc zc : ℕ → ℝ} (hcz : ∀ n, rc n ^ 2 + zc n ^ 2 ≤ ρ ^ 2) (hC : 0 ≤ C)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {lam : ℕ → ℝ} (hlam_pos : ∀ n, 0 < lam n)
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (hA : Tendsto (fun n => rc n / lam n) atTop atTop) :
    ∀ K : Set (Vec 2 × ℝ), IsCompact K → K ⊆ univ ×ˢ Iio (-1 : ℝ) → ∃ M : ℝ,
      ∀ᶠ n in atTop,
        AEStronglyMeasurable (fun z => zoomTheta (lam n) h (rc n) (zc n) u (planeLiftPoint z))
          (volume.restrict K) ∧
        AEStronglyMeasurable (recDrift (lam n) h (rc n) (zc n) u) (volume.restrict K) ∧
        AEStronglyMeasurable (recDriftDiv (lam n) h (rc n) (zc n) u) (volume.restrict K) ∧
        ∀ z ∈ K, |zoomTheta (lam n) h (rc n) (zc n) u (planeLiftPoint z)| ≤ M ∧
          ‖recDrift (lam n) h (rc n) (zc n) u z‖ ≤ M ∧
          |recDriftDiv (lam n) h (rc n) (zc n) u z| ≤ M := by
  intro K hK hKsub
  refine ⟨2 * C, ?_⟩
  have hρ1 : ρ < 1 := hρR.trans_le hR1
  have hKsub' : K ⊆ univ ×ˢ Iic (-1 : ℝ) :=
    fun z hz => ⟨(hKsub hz).1, Set.mem_Iic.mpr (le_of_lt (hKsub hz).2)⟩
  have hmem := eventually_mem_unitCylinder_of_isCompact_vec2 hh hρ0 hρ1 hcz lam hlam_lim hK hKsub'
  have hApos := eventually_one_le_ratio_add_of_isCompact_vec2 hA hK
  have hlamlt : ∀ᶠ n in atTop, lam n < 1 :=
    (hlam_lim.mono_right nhdsWithin_le_nhds).eventually_mem
      (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Iio (1 : ℝ)))
  have hKclosed : IsClosed K := hK.isClosed
  have hKmeas : MeasurableSet K := hKclosed.measurableSet
  filter_upwards [hmem, hApos, hlamlt] with n hmem_n hApos_n hlamlt_n
  have hτ : ∀ z ∈ K, z.2 ≤ -1 := fun z hz => le_of_lt (hKsub hz).2
  -- continuity on `K`
  have hzpc : Continuous (Y := Vec3 × ℝ) (fun z : Vec 2 × ℝ =>
      zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint z)) :=
    (contDiff_zoomPointRec (lam n) h (rc n) (zc n)).continuous.comp continuous_planeLiftPoint
  have hΘcont : ContinuousOn (fun z => zoomTheta (lam n) h (rc n) (zc n) u (planeLiftPoint z)) K
    := by
    have hcomp : ContinuousOn (fun z : Vec 2 × ℝ =>
        azimuthalVorticity u (zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint z))) K :=
      (contDiffOn_azimuthalVorticity hu).continuousOn.comp hzpc.continuousOn hmem_n
    exact continuousOn_const.mul hcomp
  have hVcont : ContinuousOn (fun z : Vec 2 × ℝ =>
      zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint z)) K := by
    have hcomp : ContinuousOn (fun z : Vec 2 × ℝ =>
        u (zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint z)) 0) K :=
      (contDiffOn_pi.1 hu 0).continuousOn.comp hzpc.continuousOn hmem_n
    exact continuousOn_const.mul hcomp
  have hWcont : ContinuousOn (fun z : Vec 2 × ℝ =>
      zoomWRec (lam n) h (rc n) (zc n) u (planeLiftPoint z)) K := by
    have hcomp : ContinuousOn (fun z : Vec 2 × ℝ =>
        u (zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint z)) 2) K :=
      (contDiffOn_pi.1 hu 2).continuousOn.comp hzpc.continuousOn hmem_n
    exact continuousOn_const.mul hcomp
  have hdriftCont : ContinuousOn (recDrift (lam n) h (rc n) (zc n) u) K := by
    rw [continuousOn_pi]
    intro i
    fin_cases i
    · simpa [recDrift] using hVcont
    · simpa [recDrift] using hWcont
  have hdenom_ne : ∀ z ∈ K, rc n / lam n + z.1 0 ≠ 0 := fun z hz =>
    ne_of_gt (lt_of_lt_of_le one_pos (hApos_n z hz))
  have hdivCont : ContinuousOn (recDriftDiv (lam n) h (rc n) (zc n) u) K := by
    have hc0 : ContinuousOn (fun z : Vec 2 × ℝ => rc n / lam n + z.1 0) K :=
      continuousOn_const.add
        (((continuous_apply 0).comp continuous_fst).continuousOn)
    exact (hVcont.div hc0 hdenom_ne).neg
  refine ⟨hΘcont.aestronglyMeasurable hKmeas, hdriftCont.aestronglyMeasurable hKmeas,
    hdivCont.aestronglyMeasurable hKmeas, ?_⟩
  intro z hz
  have hpz : zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint z) ∈ unitCylinder := hmem_n z hz
  have hτz : (planeLiftPoint z).2 ≤ -1 := hτ z hz
  have hΘb : |zoomTheta (lam n) h (rc n) (zc n) u (planeLiftPoint z)| ≤ 2 * C :=
    abs_zoomTheta_le_two_mul hh hC (hlam_pos n) hlamlt_n.le hb hu hpz hτz
  have hVb : |zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint z)| ≤ C := by
    have hbound := abs_zoomVRec_le C h (lam n) (rc n) (zc n) (hlam_pos n) u hb (planeLiftPoint z)
      hpz
    have hexp : (-(1 / 2 : ℝ) - 0 / 2 - (1 / 2 - h) * 0) = -(1 / 2 : ℝ) := by ring
    rw [hexp] at hbound
    have hτge1 : (1 : ℝ) ≤ -(planeLiftPoint z).2 := by linarith only [hτz]
    have hpow : (-(planeLiftPoint z).2) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hτge1 (by norm_num)
    calc |zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint z)|
        ≤ C * (-(planeLiftPoint z).2) ^ (-(1 / 2 : ℝ)) := hbound
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpow hC
      _ = C := mul_one C
  have hWb : |zoomWRec (lam n) h (rc n) (zc n) u (planeLiftPoint z)| ≤ C := by
    have hbound := abs_zoomWRec_le_rpow_neg_half (hlam_pos n) hb hpz hC hh.1.le hτz
    have hτge1 : (1 : ℝ) ≤ -(planeLiftPoint z).2 := by linarith only [hτz]
    have hpow : (-(planeLiftPoint z).2) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hτge1 (by norm_num)
    calc |zoomWRec (lam n) h (rc n) (zc n) u (planeLiftPoint z)|
        ≤ C * (-(planeLiftPoint z).2) ^ (-(1 / 2 : ℝ)) := hbound
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpow hC
      _ = C := mul_one C
  have hnormle : ‖recDrift (lam n) h (rc n) (zc n) u z‖ ≤ 2 * C := by
    rw [pi_norm_le_iff_of_nonneg (by linarith only [hC])]
    intro i
    fin_cases i
    · simpa [recDrift, Real.norm_eq_abs] using hVb.trans (by linarith only [hC])
    · simpa [recDrift, Real.norm_eq_abs] using hWb.trans (by linarith only [hC])
  have hApos_z : (0 : ℝ) < rc n / lam n + z.1 0 := lt_of_lt_of_le one_pos (hApos_n z hz)
  have hdivb : |recDriftDiv (lam n) h (rc n) (zc n) u z| ≤ 2 * C := by
    have heq : recDriftDiv (lam n) h (rc n) (zc n) u z
        = -(zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint z) / (rc n / lam n + z.1 0)) := rfl
    rw [heq, abs_neg, abs_div, abs_of_pos hApos_z]
    calc |zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint z)| / (rc n / lam n + z.1 0)
        ≤ |zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint z)| :=
          div_le_self (abs_nonneg _) (hApos_n z hz)
      _ ≤ C := hVb
      _ ≤ 2 * C := by linarith only [hC]
  exact ⟨hΘb, hnormle, hdivb⟩

/-! ### R2-H: continuity, Lipschitz bound, and weak divergence of the receding drift -/

/-- `V_n` is bounded by `C` for `τ ≤ -1` (companion of `abs_zoomTheta_le_two_mul`, extracted so
`recDrift_extraction_hypotheses` can reuse it). -/
private theorem abs_zoomVRec_le_of_tau_le_neg_one {C h lam rc zc : ℝ} (hC : 0 ≤ C)
    (hlam_pos : 0 < lam) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    {p : (ℝ × ℝ) × ℝ} (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (hτ : p.2 ≤ -1) :
    |zoomVRec lam h rc zc u p| ≤ C := by
  have hbound := abs_zoomVRec_le C h lam rc zc hlam_pos u hb p hp
  have hexp : (-(1 / 2 : ℝ) - 0 / 2 - (1 / 2 - h) * 0) = -(1 / 2 : ℝ) := by ring
  rw [hexp] at hbound
  have hτge1 : (1 : ℝ) ≤ -p.2 := by linarith only [hτ]
  have hpow : (-p.2) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτge1 (by
    norm_num)
  calc |zoomVRec lam h rc zc u p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := hbound
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpow hC
    _ = C := mul_one C

/-- `W_n` is bounded by `C` for `τ ≤ -1`. -/
private theorem abs_zoomWRec_le_of_tau_le_neg_one {C h lam rc zc : ℝ} (hC : 0 ≤ C) (hh0 : 0 ≤ h)
    (hlam_pos : 0 < lam) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    {p : (ℝ × ℝ) × ℝ} (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (hτ : p.2 ≤ -1) :
    |zoomWRec lam h rc zc u p| ≤ C := by
  have hbound := abs_zoomWRec_le_rpow_neg_half hlam_pos hb hp hC hh0 hτ
  have hτge1 : (1 : ℝ) ≤ -p.2 := by linarith only [hτ]
  have hpow : (-p.2) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτge1 (by
    norm_num)
  calc |zoomWRec lam h rc zc u p| ≤ C * (-p.2) ^ (-(1 / 2 : ℝ)) := hbound
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpow hC
    _ = C := mul_one C

/-- Continuity of the receding drift and its divergence on a set where the zoom point lies
in the unit cylinder and the recentring ratio keeps the divergence denominator positive. -/
private theorem continuousOn_recDrift_recDriftDiv {lam h rc zc : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) {K : Set (Vec 2 × ℝ)}
    (hmem : ∀ z ∈ K, zoomPointRec lam h rc zc (planeLiftPoint z) ∈ unitCylinder)
    (hApos : ∀ z ∈ K, (1 : ℝ) ≤ rc / lam + z.1 0) :
    ContinuousOn (recDrift lam h rc zc u) K ∧ ContinuousOn (recDriftDiv lam h rc zc u) K := by
  have hzpc : Continuous (Y := Vec3 × ℝ)
      (fun z : Vec 2 × ℝ => zoomPointRec lam h rc zc (planeLiftPoint z)) :=
    (contDiff_zoomPointRec lam h rc zc).continuous.comp continuous_planeLiftPoint
  have hVcont : ContinuousOn (fun z : Vec 2 × ℝ =>
      zoomVRec lam h rc zc u (planeLiftPoint z)) K := by
    have hcomp : ContinuousOn (fun z : Vec 2 × ℝ =>
        u (zoomPointRec lam h rc zc (planeLiftPoint z)) 0) K :=
      (contDiffOn_pi.1 hu 0).continuousOn.comp hzpc.continuousOn hmem
    exact continuousOn_const.mul hcomp
  have hWcont : ContinuousOn (fun z : Vec 2 × ℝ =>
      zoomWRec lam h rc zc u (planeLiftPoint z)) K := by
    have hcomp : ContinuousOn (fun z : Vec 2 × ℝ =>
        u (zoomPointRec lam h rc zc (planeLiftPoint z)) 2) K :=
      (contDiffOn_pi.1 hu 2).continuousOn.comp hzpc.continuousOn hmem
    exact continuousOn_const.mul hcomp
  have hdriftCont : ContinuousOn (recDrift lam h rc zc u) K := by
    rw [continuousOn_pi]
    intro i
    fin_cases i
    · simpa [recDrift] using hVcont
    · simpa [recDrift] using hWcont
  have hdenom_ne : ∀ z ∈ K, rc / lam + z.1 0 ≠ 0 := fun z hz =>
    ne_of_gt (lt_of_lt_of_le one_pos (hApos z hz))
  have hdivCont : ContinuousOn (recDriftDiv lam h rc zc u) K := by
    have hc0 : ContinuousOn (fun z : Vec 2 × ℝ => rc / lam + z.1 0) K :=
      continuousOn_const.add (((continuous_apply 0).comp continuous_fst).continuousOn)
    exact (hVcont.div hc0 hdenom_ne).neg
  exact ⟨hdriftCont, hdivCont⟩

/-- Each coordinate of the difference of two `Vec 2` points is bounded by the norm of the
difference (the sup norm's dual bound, componentwise). -/
private theorem abs_apply_sub_le_norm_sub (x y : Vec 2) (i : Fin 2) :
    |x i - y i| ≤ ‖x - y‖ := by
  have h := norm_le_pi_norm (x - y) i
  simpa [Real.norm_eq_abs] using h

/-! ### The coordinate bridge between `Vec 2` calculus and the plane operators `dr`, `dz` -/

/-- The coordinate projection `Vec 2 → ℝ × ℝ`, as a continuous linear map. -/
private theorem planeCoordCLM_eq :
    (fun x' : Vec 2 => ((x' 0, x' 1) : ℝ × ℝ))
      = ⇑((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).prod
          (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2))) := by
  funext x'
  simp [ContinuousLinearMap.prod_apply, ContinuousLinearMap.proj_apply]

private theorem planeCoordCLM_hasFDerivAt (x : Vec 2) :
    HasFDerivAt (fun x' : Vec 2 => ((x' 0, x' 1) : ℝ × ℝ))
      ((ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)).prod
        (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2))) x := by
  rw [planeCoordCLM_eq]
  exact ContinuousLinearMap.hasFDerivAt _

/-- The `Vec 2` derivative in the direction `basisVec 0` of a plane function composed with
`planeLiftPoint` at fixed time is its radial derivative `dr`. -/
private theorem fderiv_comp_planeLift_basisVec0 {F : (ℝ × ℝ) × ℝ → ℝ} {τ : ℝ} {x : Vec 2}
    (hF : DifferentiableAt ℝ (fun p : ℝ × ℝ => F (p, τ)) (x 0, x 1)) :
    fderiv ℝ (fun x' : Vec 2 => F (planeLiftPoint (x', τ))) x (basisVec 0)
      = dr F (planeLiftPoint (x, τ)) := by
  have hF' := hF.hasFDerivAt
  have hcomp := HasFDerivAt.comp x hF' (planeCoordCLM_hasFDerivAt x)
  rw [show (fun x' : Vec 2 => F (planeLiftPoint (x', τ))) =
      (fun p : ℝ × ℝ => F (p, τ)) ∘ (fun x' : Vec 2 => ((x' 0, x' 1) : ℝ × ℝ)) from rfl]
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.proj_apply, basisVec_apply]
  norm_num
  exact (dr_eq_of_hasFDerivAt F τ hF').symm

/-- The `Vec 2` derivative in the direction `basisVec 1` of a plane function composed with
`planeLiftPoint` at fixed time is its vertical derivative `dz`. -/
private theorem fderiv_comp_planeLift_basisVec1 {F : (ℝ × ℝ) × ℝ → ℝ} {τ : ℝ} {x : Vec 2}
    (hF : DifferentiableAt ℝ (fun p : ℝ × ℝ => F (p, τ)) (x 0, x 1)) :
    fderiv ℝ (fun x' : Vec 2 => F (planeLiftPoint (x', τ))) x (basisVec 1)
      = dz F (planeLiftPoint (x, τ)) := by
  have hF' := hF.hasFDerivAt
  have hcomp := HasFDerivAt.comp x hF' (planeCoordCLM_hasFDerivAt x)
  rw [show (fun x' : Vec 2 => F (planeLiftPoint (x', τ))) =
      (fun p : ℝ × ℝ => F (p, τ)) ∘ (fun x' : Vec 2 => ((x' 0, x' 1) : ℝ × ℝ)) from rfl]
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.proj_apply, basisVec_apply]
  norm_num
  exact (dz_eq_of_hasFDerivAt F τ hF').symm

/-- The product of a function continuous on an open set of `Vec 2` with a continuous function
whose support closes inside that set is continuous on all of `Vec 2`. -/
private theorem continuous_mul_of_tsupport_subset_vec2 {U : Set (Vec 2)} (hU : IsOpen U)
    {a b : Vec 2 → ℝ} (ha : ContinuousOn a U) (hb : Continuous b) (hbU : tsupport b ⊆ U) :
    Continuous fun x => a x * b x := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ tsupport b
  · exact (ha.continuousAt (hU.mem_nhds (hbU hx))).mul hb.continuousAt
  · have hopen : IsOpen (tsupport b)ᶜ := (isClosed_tsupport b).isOpen_compl
    have hev : (fun x => a x * b x) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hx] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
    exact ContinuousAt.congr continuousAt_const hev.symm

private theorem recDrift_eventual_bounds
    {h ρ C : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {rc zc : ℕ → ℝ} (hcz : ∀ n, rc n ^ 2 + zc n ^ 2 ≤ ρ ^ 2) (hC : 0 ≤ C)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {lam : ℕ → ℝ} (hlam_pos : ∀ n, 0 < lam n)
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (hA : Tendsto (fun n => rc n / lam n) atTop atTop) :
    ∀ J : Set ℝ, IsCompact J → J ⊆ Iic (-1 : ℝ) → ∃ Λ : ℝ, ∀ r : ℝ, ∀ᶠ n in atTop,
      ∀ τ ∈ J, ∀ x ∈ Metric.closedBall (0 : Vec 2) r, ∀ y ∈ Metric.closedBall (0 : Vec 2) r,
        ‖recDrift (lam n) h (rc n) (zc n) u (x, τ)‖ ≤ Λ ∧
        |recDriftDiv (lam n) h (rc n) (zc n) u (x, τ)| ≤ Λ ∧
        ‖recDrift (lam n) h (rc n) (zc n) u (x, τ) - recDrift (lam n) h (rc n) (zc n) u (y, τ)‖
          ≤ Λ * ‖x - y‖ ∧
        |recDriftDiv (lam n) h (rc n) (zc n) u (x, τ) -
          recDriftDiv (lam n) h (rc n) (zc n) u (y, τ)| ≤ Λ * ‖x - y‖ := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by norm_num)
  intro J hJ hJsub
  refine ⟨4 * C, fun r => ?_⟩
  by_cases hr0 : 0 ≤ r
  · have hKr : IsCompact (Metric.closedBall (0 : Vec 2) r ×ˢ J) :=
      (isCompact_closedBall _ _).prod hJ
    have hKrsub : Metric.closedBall (0 : Vec 2) r ×ˢ J ⊆ univ ×ˢ Iic (-1 : ℝ) :=
      fun z hz => ⟨mem_univ _, hJsub hz.2⟩
    have hmem := eventually_mem_unitCylinder_of_isCompact_vec2 hh hρ0 hρ1 hcz lam hlam_lim hKr
      hKrsub
    have hApos := eventually_one_le_ratio_add_of_isCompact_vec2 hA hKr
    have hlamlt : ∀ᶠ n in atTop, lam n < 1 :=
      (hlam_lim.mono_right nhdsWithin_le_nhds).eventually_mem
        (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Iio (1 : ℝ)))
    filter_upwards [hmem, hApos, hlamlt] with n hmem_n hApos_n hlamlt_n
    intro τ hτ x hx y hy
    have hτ1 : τ ≤ -1 := hJsub hτ
    have hrect : ∀ y' ∈ Icc (-r) r ×ˢ Icc (-r) r,
        zoomPointRec (lam n) h (rc n) (zc n) (y', τ) ∈ unitCylinder := by
      rintro ⟨a, bb⟩ ⟨ha, hbb⟩
      have hxv : (![a, bb] : Vec 2) ∈ Metric.closedBall (0 : Vec 2) r := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, pi_norm_le_iff_of_nonneg hr0]
        intro i
        fin_cases i
        · simpa using abs_le.mpr ha
        · simpa using abs_le.mpr hbb
      have hm := hmem_n (![a, bb], τ) ⟨hxv, hτ⟩
      simpa [planeLiftPoint] using hm
    have hVlip := lipschitzOnWith_zoomVRec (C := C) (h := h) (rc := rc n) (zc := zc n)
      (hlam_pos n) hb hu2 hC hh.2.le hτ1 hrect
    have hWlip := lipschitzOnWith_zoomWRec (hlam_pos n) u hb hu2 hC hh.1.le hτ1 hrect
    have hxmem : (x 0, x 1) ∈ Icc (-r) r ×ˢ Icc (-r) r := by
      have h0 := abs_apply_sub_le_norm_sub x 0 0
      have h1 := abs_apply_sub_le_norm_sub x 0 1
      simp only [Pi.zero_apply, sub_zero] at h0 h1
      have hxr : ‖x‖ ≤ r := by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hx
      exact ⟨abs_le.mp (h0.trans hxr), abs_le.mp (h1.trans hxr)⟩
    have hymem : (y 0, y 1) ∈ Icc (-r) r ×ˢ Icc (-r) r := by
      have h0 := abs_apply_sub_le_norm_sub y 0 0
      have h1 := abs_apply_sub_le_norm_sub y 0 1
      simp only [Pi.zero_apply, sub_zero] at h0 h1
      have hyr : ‖y‖ ≤ r := by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hy
      exact ⟨abs_le.mp (h0.trans hyr), abs_le.mp (h1.trans hyr)⟩
    have hpx : zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint (x, τ)) ∈ unitCylinder :=
      hmem_n (x, τ) ⟨hx, hτ⟩
    have hpy : zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint (y, τ)) ∈ unitCylinder :=
      hmem_n (y, τ) ⟨hy, hτ⟩
    have heqx : planeLiftPoint (x, τ) = ((x 0, x 1), τ) := rfl
    have heqy : planeLiftPoint (y, τ) = ((y 0, y 1), τ) := rfl
    rw [heqx] at hpx
    rw [heqy] at hpy
    have hVbx : |zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (x, τ))| ≤ C := by
      rw [heqx]; exact abs_zoomVRec_le_of_tau_le_neg_one hC (hlam_pos n) hb hpx hτ1
    have hVby : |zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (y, τ))| ≤ C := by
      rw [heqy]; exact abs_zoomVRec_le_of_tau_le_neg_one hC (hlam_pos n) hb hpy hτ1
    have hWbx : |zoomWRec (lam n) h (rc n) (zc n) u (planeLiftPoint (x, τ))| ≤ C := by
      rw [heqx]; exact abs_zoomWRec_le_of_tau_le_neg_one hC hh.1.le (hlam_pos n) hb hpx hτ1
    have hWby : |zoomWRec (lam n) h (rc n) (zc n) u (planeLiftPoint (y, τ))| ≤ C := by
      rw [heqy]; exact abs_zoomWRec_le_of_tau_le_neg_one hC hh.1.le (hlam_pos n) hb hpy hτ1
    have hAx1 : (1 : ℝ) ≤ rc n / lam n + x 0 := hApos_n (x, τ) ⟨hx, hτ⟩
    have hAy1 : (1 : ℝ) ≤ rc n / lam n + y 0 := hApos_n (y, τ) ⟨hy, hτ⟩
    have hAx0 : (0 : ℝ) < rc n / lam n + x 0 := lt_of_lt_of_le one_pos hAx1
    have hAy0 : (0 : ℝ) < rc n / lam n + y 0 := lt_of_lt_of_le one_pos hAy1
    -- the plane distance between the two projected points equals `‖x - y‖`
    have hdist_le : dist ((x 0, x 1) : ℝ × ℝ) (y 0, y 1) ≤ ‖x - y‖ := by
      rw [Prod.dist_eq]
      exact max_le (by simpa [Real.dist_eq] using abs_apply_sub_le_norm_sub x y 0)
        (by simpa [Real.dist_eq] using abs_apply_sub_le_norm_sub x y 1)
    have hVdist := lipschitzOnWith_iff_dist_le_mul.mp hVlip _ hxmem _ hymem
    have hWdist := lipschitzOnWith_iff_dist_le_mul.mp hWlip _ hxmem _ hymem
    rw [Real.dist_eq] at hVdist hWdist
    simp only [Real.coe_toNNReal', max_eq_left (by positivity : (0:ℝ) ≤ 2*C)]
      at hVdist hWdist
    have hVdiff : |zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (x, τ)) -
        zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (y, τ))| ≤ 2 * C * ‖x - y‖ := by
      rw [heqx, heqy]
      exact hVdist.trans (mul_le_mul_of_nonneg_left hdist_le (by positivity))
    have hWdiff : |zoomWRec (lam n) h (rc n) (zc n) u (planeLiftPoint (x, τ)) -
        zoomWRec (lam n) h (rc n) (zc n) u (planeLiftPoint (y, τ))| ≤ 2 * C * ‖x - y‖ := by
      rw [heqx, heqy]
      exact hWdist.trans (mul_le_mul_of_nonneg_left hdist_le (by positivity))
    have hxynn : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pi_norm_le_iff_of_nonneg (by positivity : (0:ℝ) ≤ 4 * C)]
      intro i
      fin_cases i
      · simpa [recDrift, Real.norm_eq_abs] using hVbx.trans (by linarith only [hC])
      · simpa [recDrift, Real.norm_eq_abs] using hWbx.trans (by linarith only [hC])
    · have heq : recDriftDiv (lam n) h (rc n) (zc n) u (x, τ)
          = -(zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (x, τ)) /
              (rc n / lam n + x 0)) := rfl
      rw [heq, abs_neg, abs_div, abs_of_pos hAx0]
      calc |zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (x, τ))| / (rc n / lam n + x 0)
          ≤ |zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (x, τ))| :=
            div_le_self (abs_nonneg _) hAx1
        _ ≤ C := hVbx
        _ ≤ 4 * C := by linarith only [hC]
    · rw [pi_norm_le_iff_of_nonneg (by positivity : (0:ℝ) ≤ 4 * C * ‖x - y‖)]
      intro i
      fin_cases i
      · simpa [recDrift, Real.norm_eq_abs] using hVdiff.trans (by nlinarith only [hxynn, hC])
      · simpa [recDrift, Real.norm_eq_abs] using hWdiff.trans (by nlinarith only [hxynn, hC])
    · have hAxy : |1 / (rc n / lam n + x 0) - 1 / (rc n / lam n + y 0)|
          ≤ |x 0 - y 0| := by
        have hne_x : rc n / lam n + x 0 ≠ 0 := hAx0.ne'
        have hne_y : rc n / lam n + y 0 ≠ 0 := hAy0.ne'
        have heq : 1 / (rc n / lam n + x 0) - 1 / (rc n / lam n + y 0)
            = (y 0 - x 0) / ((rc n / lam n + x 0) * (rc n / lam n + y 0)) := by
          field_simp
          ring
        rw [heq, abs_div]
        have hprod1 : (1 : ℝ) ≤ (rc n / lam n + x 0) * (rc n / lam n + y 0) := by
          nlinarith only [hAx1, hAy1]
        have hprodpos : (0 : ℝ) < (rc n / lam n + x 0) * (rc n / lam n + y 0) :=
          mul_pos hAx0 hAy0
        rw [abs_of_pos hprodpos, abs_sub_comm (y 0) (x 0)]
        exact div_le_self (abs_nonneg _) hprod1
      have hx0y0 : |x 0 - y 0| ≤ ‖x - y‖ := abs_apply_sub_le_norm_sub x y 0
      have heqdiv : recDriftDiv (lam n) h (rc n) (zc n) u (x, τ) -
          recDriftDiv (lam n) h (rc n) (zc n) u (y, τ)
          = -((zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (x, τ)) -
                zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (y, τ))) /
              (rc n / lam n + x 0))
            - zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (y, τ)) *
              (1 / (rc n / lam n + x 0) - 1 / (rc n / lam n + y 0)) := by
        simp only [recDriftDiv]
        field_simp
        ring
      rw [heqdiv]
      set A : ℝ := (zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (x, τ)) -
            zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (y, τ))) /
            (rc n / lam n + x 0) with hA_def
      set B : ℝ := zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (y, τ)) *
            (1 / (rc n / lam n + x 0) - 1 / (rc n / lam n + y 0)) with hB_def
      have hterm1 : |A| ≤ 2 * C * ‖x - y‖ := by
        rw [hA_def, abs_div, abs_of_pos hAx0]
        have hle : |zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (x, τ)) -
            zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (y, τ))| /
            (rc n / lam n + x 0)
            ≤ |zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (x, τ)) -
              zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (y, τ))| :=
          div_le_self (abs_nonneg _) hAx1
        exact hle.trans hVdiff
      have hterm2 : |B| ≤ C * ‖x - y‖ := by
        rw [hB_def, abs_mul]
        exact mul_le_mul hVby (hAxy.trans hx0y0) (abs_nonneg _) hC
      have hrw : -A - B = -(A + B) := by ring
      rw [hrw, abs_neg]
      calc |A + B| ≤ |A| + |B| := abs_add_le _ _
        _ ≤ 2 * C * ‖x - y‖ + C * ‖x - y‖ := add_le_add hterm1 hterm2
        _ ≤ 4 * C * ‖x - y‖ := by nlinarith only [hxynn, hC]
  · have hempty : Metric.closedBall (0 : Vec 2) r = ∅ :=
      Metric.closedBall_eq_empty.mpr (not_le.mp hr0)
    filter_upwards with n τ hτ x hx
    simp [hempty] at hx

/-- R2-H: the hypotheses of G-DRIFT at the receding zoom fields. -/
theorem recDrift_extraction_hypotheses
    {h ρ Rstar C : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ) (hρR : ρ < Rstar) (hR1 : Rstar ≤ 1)
    {rc zc : ℕ → ℝ} (hcz : ∀ n, rc n ^ 2 + zc n ^ 2 ≤ ρ ^ 2) (hC : 0 ≤ C)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    {lam : ℕ → ℝ} (hlam_pos : ∀ n, 0 < lam n)
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (hA : Tendsto (fun n => rc n / lam n) atTop atTop) :
    (∀ K : Set (Vec 2 × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic (-1 : ℝ) →
      ∀ᶠ n in atTop, ContinuousOn (recDrift (lam n) h (rc n) (zc n) u) K ∧
        ContinuousOn (recDriftDiv (lam n) h (rc n) (zc n) u) K) ∧
    (∀ J : Set ℝ, IsCompact J → J ⊆ Iic (-1 : ℝ) → ∃ Λ : ℝ, ∀ r : ℝ, ∀ᶠ n in atTop,
      ∀ τ ∈ J, ∀ x ∈ Metric.closedBall (0 : Vec 2) r, ∀ y ∈ Metric.closedBall (0 : Vec 2) r,
        ‖recDrift (lam n) h (rc n) (zc n) u (x, τ)‖ ≤ Λ ∧
        |recDriftDiv (lam n) h (rc n) (zc n) u (x, τ)| ≤ Λ ∧
        ‖recDrift (lam n) h (rc n) (zc n) u (x, τ) - recDrift (lam n) h (rc n) (zc n) u (y, τ)‖
          ≤ Λ * ‖x - y‖ ∧
        |recDriftDiv (lam n) h (rc n) (zc n) u (x, τ) -
          recDriftDiv (lam n) h (rc n) (zc n) u (y, τ)| ≤ Λ * ‖x - y‖) ∧
    (∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ J : Set ℝ, IsCompact J → J ⊆ Iic (-1 : ℝ) → ∀ᶠ n in atTop, ∀ τ ∈ J,
        ∫ x, recDriftDiv (lam n) h (rc n) (zc n) u (x, τ) * ψ x =
          -∫ x, ∑ i, recDrift (lam n) h (rc n) (zc n) u (x, τ) i * fderiv ℝ ψ x (basisVec i)) := by
  have hρ1 : ρ < 1 := hρR.trans_le hR1
  refine ⟨?_, recDrift_eventual_bounds hh hρ0 hρ1 hcz hC hb hu hlam_pos hlam_lim hA, ?_⟩
  · intro K hK hKsub
    have hmem := eventually_mem_unitCylinder_of_isCompact_vec2 hh hρ0 hρ1 hcz lam hlam_lim hK hKsub
    have hApos := eventually_one_le_ratio_add_of_isCompact_vec2 hA hK
    filter_upwards [hmem, hApos] with n hmem_n hApos_n
    exact continuousOn_recDrift_recDriftDiv hu hmem_n hApos_n
  · intro ψ hψ hψc J hJ hJsub
    have hK : IsCompact (tsupport ψ ×ˢ J) := hψc.prod hJ
    have hKsub : tsupport ψ ×ˢ J ⊆ univ ×ˢ Iic (-1 : ℝ) := fun z hz => ⟨mem_univ _, hJsub hz.2⟩
    have hmem := eventually_mem_unitCylinder_of_isCompact_vec2 hh hρ0 hρ1 hcz lam hlam_lim hK hKsub
    have hApos := eventually_one_le_ratio_add_of_isCompact_vec2 hA hK
    filter_upwards [hmem, hApos] with n hmem_n hApos_n
    intro τ hτ
    set FV : Vec 2 → ℝ := fun x => zoomVRec (lam n) h (rc n) (zc n) u (planeLiftPoint (x, τ))
      with hFV_def
    set FW : Vec 2 → ℝ := fun x => zoomWRec (lam n) h (rc n) (zc n) u (planeLiftPoint (x, τ))
      with hFW_def
    set U : Set (Vec 2) :=
      {x : Vec 2 | zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint (x, τ)) ∈ unitCylinder}
      with hU_def
    have hzc0 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => planeLiftPoint (x, τ)) := by
      have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => ((x 0, x 1) : ℝ × ℝ)) := by
        rw [planeCoordCLM_eq]; exact ContinuousLinearMap.contDiff _
      exact h1.prodMk contDiff_const
    have hzp : ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞)
        (fun x : Vec 2 => zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint (x, τ))) :=
      (contDiff_zoomPointRec (lam n) h (rc n) (zc n)).comp hzc0
    have hUopen : IsOpen U := isOpen_unitCylinder_prod.preimage hzp.continuous
    have hUsupp : tsupport ψ ⊆ U := fun x hx => hmem_n (x, τ) ⟨hx, hτ⟩
    have hFVsmooth : ContDiffOn ℝ (⊤ : ℕ∞) FV U := by
      have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun x : Vec 2 => u (zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint (x, τ))) 0)
          U := (contDiffOn_pi.1 hu 0).comp hzp.contDiffOn (fun x hx => hx)
      exact contDiffOn_const.mul hcomp
    have hFWsmooth : ContDiffOn ℝ (⊤ : ℕ∞) FW U := by
      have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun x : Vec 2 => u (zoomPointRec (lam n) h (rc n) (zc n) (planeLiftPoint (x, τ))) 2)
          U := (contDiffOn_pi.1 hu 2).comp hzp.contDiffOn (fun x hx => hx)
      exact contDiffOn_const.mul hcomp
    have hFVdiff : ∀ x ∈ tsupport ψ, DifferentiableAt ℝ FV x := fun x hx =>
      (hFVsmooth.differentiableOn (by norm_num) x (hUsupp hx)).differentiableAt
        (hUopen.mem_nhds (hUsupp hx))
    have hFWdiff : ∀ x ∈ tsupport ψ, DifferentiableAt ℝ FW x := fun x hx =>
      (hFWsmooth.differentiableOn (by norm_num) x (hUsupp hx)).differentiableAt
        (hUopen.mem_nhds (hUsupp hx))
    have hψdiff : ∀ x, DifferentiableAt ℝ ψ x := fun x => hψ.differentiable (by norm_num) x
    -- the slice at fixed `τ` is differentiable on the open plane domain, feeding the bridge
    have hVslice_diff : ∀ x ∈ U,
        DifferentiableAt ℝ (fun p : ℝ × ℝ => zoomVRec (lam n) h (rc n) (zc n) u (p, τ)) (x 0, x
          1) := by
      intro x hx
      have hζ : ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞)
          (fun y : ℝ × ℝ => zoomPointRec (lam n) h (rc n) (zc n) (y, τ)) :=
        (contDiff_zoomPointRec (lam n) h (rc n) (zc n)).comp (contDiff_id.prodMk contDiff_const)
      have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun y : ℝ × ℝ => u (zoomPointRec (lam n) h (rc n) (zc n) (y, τ)) 0)
          {y : ℝ × ℝ | zoomPointRec (lam n) h (rc n) (zc n) (y, τ) ∈ unitCylinder} :=
        (contDiffOn_pi.1 hu 0).comp hζ.contDiffOn (fun y hy => hy)
      have hVsl : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun y : ℝ × ℝ => zoomVRec (lam n) h (rc n) (zc n) u (y, τ))
          {y : ℝ × ℝ | zoomPointRec (lam n) h (rc n) (zc n) (y, τ) ∈ unitCylinder} :=
        contDiffOn_const.mul hcomp
      have hyopen : IsOpen {y : ℝ × ℝ | zoomPointRec (lam n) h (rc n) (zc n) (y, τ) ∈
        unitCylinder} :=
        isOpen_unitCylinder_prod.preimage hζ.continuous
      exact (hVsl.differentiableOn (by norm_num) (x 0, x 1) hx).differentiableAt
        (hyopen.mem_nhds hx)
    have hWslice_diff : ∀ x ∈ U,
        DifferentiableAt ℝ (fun p : ℝ × ℝ => zoomWRec (lam n) h (rc n) (zc n) u (p, τ)) (x 0, x
          1) := by
      intro x hx
      have hζ : ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞)
          (fun y : ℝ × ℝ => zoomPointRec (lam n) h (rc n) (zc n) (y, τ)) :=
        (contDiff_zoomPointRec (lam n) h (rc n) (zc n)).comp (contDiff_id.prodMk contDiff_const)
      have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun y : ℝ × ℝ => u (zoomPointRec (lam n) h (rc n) (zc n) (y, τ)) 2)
          {y : ℝ × ℝ | zoomPointRec (lam n) h (rc n) (zc n) (y, τ) ∈ unitCylinder} :=
        (contDiffOn_pi.1 hu 2).comp hζ.contDiffOn (fun y hy => hy)
      have hWsl : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun y : ℝ × ℝ => zoomWRec (lam n) h (rc n) (zc n) u (y, τ))
          {y : ℝ × ℝ | zoomPointRec (lam n) h (rc n) (zc n) (y, τ) ∈ unitCylinder} :=
        contDiffOn_const.mul hcomp
      have hyopen : IsOpen {y : ℝ × ℝ | zoomPointRec (lam n) h (rc n) (zc n) (y, τ) ∈
        unitCylinder} :=
        isOpen_unitCylinder_prod.preimage hζ.continuous
      exact (hWsl.differentiableOn (by norm_num) (x 0, x 1) hx).differentiableAt
        (hyopen.mem_nhds hx)
    have hFVfderiv : ∀ x ∈ U,
        fderiv ℝ FV x (basisVec 0) = dr (zoomVRec (lam n) h (rc n) (zc n) u) (planeLiftPoint (x,
          τ)) :=
      fun x hx => fderiv_comp_planeLift_basisVec0 (hVslice_diff x hx)
    have hFWfderiv : ∀ x ∈ U,
        fderiv ℝ FW x (basisVec 1) = dz (zoomWRec (lam n) h (rc n) (zc n) u) (planeLiftPoint (x,
          τ)) :=
      fun x hx => fderiv_comp_planeLift_basisVec1 (hWslice_diff x hx)
    set GV : Vec 2 → ℝ := fun x => fderiv ℝ FV x (basisVec 0) with hGV_def
    set GW : Vec 2 → ℝ := fun x => fderiv ℝ FW x (basisVec 1) with hGW_def
    -- continuity of `GV`, `GW` on `U`
    have hGVcont : ContinuousOn GV U := by
      have h1 : ContDiffOn ℝ 0 (fderiv ℝ FV) U := hFVsmooth.fderiv_of_isOpen hUopen (by norm_num)
      exact (ContinuousLinearMap.apply ℝ ℝ (basisVec (0 : Fin 2))).continuous.comp_continuousOn
        h1.continuousOn
    have hGWcont : ContinuousOn GW U := by
      have h1 : ContDiffOn ℝ 0 (fderiv ℝ FW) U := hFWsmooth.fderiv_of_isOpen hUopen (by norm_num)
      exact (ContinuousLinearMap.apply ℝ ℝ (basisVec (1 : Fin 2))).continuous.comp_continuousOn
        h1.continuousOn
    have hψcont : Continuous ψ := hψ.continuous
    have hψ0cont : Continuous (fun x : Vec 2 => fderiv ℝ ψ x (basisVec 0)) :=
      (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hψ1cont : Continuous (fun x : Vec 2 => fderiv ℝ ψ x (basisVec 1)) :=
      (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hψ0supp : tsupport (fun x : Vec 2 => fderiv ℝ ψ x (basisVec 0)) ⊆ U :=
      (tsupport_fderiv_apply_subset ℝ (basisVec 0)).trans hUsupp
    have hψ1supp : tsupport (fun x : Vec 2 => fderiv ℝ ψ x (basisVec 1)) ⊆ U :=
      (tsupport_fderiv_apply_subset ℝ (basisVec 1)).trans hUsupp
    have hψ0c : HasCompactSupport (fun x : Vec 2 => fderiv ℝ ψ x (basisVec 0)) :=
      hψc.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset ℝ (basisVec 0))
    have hψ1c : HasCompactSupport (fun x : Vec 2 => fderiv ℝ ψ x (basisVec 1)) :=
      hψc.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset ℝ (basisVec 1))
    have hintGVψ : Integrable fun x => GV x * ψ x :=
      (continuous_mul_of_tsupport_subset_vec2 hUopen hGVcont hψcont
        hUsupp).integrable_of_hasCompactSupport hψc.mul_left
    have hintGWψ : Integrable fun x => GW x * ψ x :=
      (continuous_mul_of_tsupport_subset_vec2 hUopen hGWcont hψcont
        hUsupp).integrable_of_hasCompactSupport hψc.mul_left
    have hintFVψ0 : Integrable fun x => FV x * fderiv ℝ ψ x (basisVec 0) :=
      (continuous_mul_of_tsupport_subset_vec2 hUopen hFVsmooth.continuousOn hψ0cont
        hψ0supp).integrable_of_hasCompactSupport hψ0c.mul_left
    have hintFWψ1 : Integrable fun x => FW x * fderiv ℝ ψ x (basisVec 1) :=
      (continuous_mul_of_tsupport_subset_vec2 hUopen hFWsmooth.continuousOn hψ1cont
        hψ1supp).integrable_of_hasCompactSupport hψ1c.mul_left
    have hintFVψ : Integrable fun x => FV x * ψ x :=
      (continuous_mul_of_tsupport_subset_vec2 hUopen hFVsmooth.continuousOn hψcont
        hUsupp).integrable_of_hasCompactSupport hψc.mul_left
    have hintFWψ : Integrable fun x => FW x * ψ x :=
      (continuous_mul_of_tsupport_subset_vec2 hUopen hFWsmooth.continuousOn hψcont
        hUsupp).integrable_of_hasCompactSupport hψc.mul_left
    have hFVdiff' : ∀ x ∈ tsupport ψ, DifferentiableAt ℝ FV x := fun x hx => hFVdiff x hx
    have hFWdiff' : ∀ x ∈ tsupport ψ, DifferentiableAt ℝ FW x := fun x hx => hFWdiff x hx
    have hψdiffOn : ∀ x ∈ tsupport FV, DifferentiableAt ℝ ψ x := fun x _ => hψdiff x
    have hψdiffOnW : ∀ x ∈ tsupport FW, DifferentiableAt ℝ ψ x := fun x _ => hψdiff x
    have hVstep : ∫ x, FV x * fderiv ℝ ψ x (basisVec 0) = -∫ x, GV x * ψ x :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hintGVψ hintFVψ0 hintFVψ hFVdiff'
        hψdiffOn
    have hWstep : ∫ x, FW x * fderiv ℝ ψ x (basisVec 1) = -∫ x, GW x * ψ x :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hintGWψ hintFWψ1 hintFWψ hFWdiff'
        hψdiffOnW
    -- assembling the right-hand side of the target identity
    have hsum_eq : (fun x : Vec 2 => ∑ i, recDrift (lam n) h (rc n) (zc n) u (x, τ) i *
        fderiv ℝ ψ x (basisVec i))
        = fun x : Vec 2 => FV x * fderiv ℝ ψ x (basisVec 0) + FW x * fderiv ℝ ψ x (basisVec 1) := by
      funext x
      simp [Fin.sum_univ_two, recDrift, FV, FW]
    have hstep2 : (∫ x, FV x * fderiv ℝ ψ x (basisVec 0) + FW x * fderiv ℝ ψ x (basisVec 1))
        = (∫ x, FV x * fderiv ℝ ψ x (basisVec 0)) + ∫ x, FW x * fderiv ℝ ψ x (basisVec 1) :=
      integral_add hintFVψ0 hintFWψ1
    have hrhs : (-∫ x, ∑ i, recDrift (lam n) h (rc n) (zc n) u (x, τ) i * fderiv ℝ ψ x (basisVec i))
        = (∫ x, GV x * ψ x) + ∫ x, GW x * ψ x := by
      rw [hsum_eq, hstep2, hVstep, hWstep]
      ring
    have hGsum : (∫ x, GV x * ψ x) + ∫ x, GW x * ψ x = ∫ x, (GV x + GW x) * ψ x := by
      have heq : (∫ x, (GV x + GW x) * ψ x) = (∫ x, GV x * ψ x) + ∫ x, GW x * ψ x := by
        have hfe : (fun x : Vec 2 => (GV x + GW x) * ψ x)
            = fun x : Vec 2 => GV x * ψ x + GW x * ψ x := by
          funext x; ring
        rw [hfe]
        exact integral_add hintGVψ hintGWψ
      exact heq.symm
    have hpointwise : ∀ x, (GV x + GW x) * ψ x
        = recDriftDiv (lam n) h (rc n) (zc n) u (x, τ) * ψ x := by
      intro x
      by_cases hx : x ∈ tsupport ψ
      · have hxU : x ∈ U := hUsupp hx
        have hVeq := hFVfderiv x hxU
        have hWeq := hFWfderiv x hxU
        have hApos_x : (1 : ℝ) ≤ rc n / lam n + x 0 := hApos_n (x, τ) ⟨hx, hτ⟩
        have hRne : x 0 ≠ -(rc n / lam n) := by
          intro hc
          have hz : rc n / lam n + x 0 = 0 := by rw [hc]; ring
          linarith only [hApos_x, hz]
        have hdiv := zoomRec_divergence_identity (lam n) h (rc n) (zc n) (hlam_pos n) u pr f
          hsol haxi (planeLiftPoint (x, τ)) hxU hRne
        have hp11 : (planeLiftPoint (x, τ)).1.1 = x 0 := rfl
        rw [hp11] at hdiv
        have heqdiv : dr (zoomVRec (lam n) h (rc n) (zc n) u) (planeLiftPoint (x, τ)) +
            dz (zoomWRec (lam n) h (rc n) (zc n) u) (planeLiftPoint (x, τ))
            = recDriftDiv (lam n) h (rc n) (zc n) u (x, τ) := by
          simp only [recDriftDiv]
          linarith only [hdiv]
        change (fderiv ℝ FV x (basisVec 0) + fderiv ℝ FW x (basisVec 1)) * ψ x
            = recDriftDiv (lam n) h (rc n) (zc n) u (x, τ) * ψ x
        rw [hVeq, hWeq, heqdiv]
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
    have hfin : ∫ x, (GV x + GW x) * ψ x
        = ∫ x, recDriftDiv (lam n) h (rc n) (zc n) u (x, τ) * ψ x :=
      integral_congr_ae (Filter.Eventually.of_forall hpointwise)
    rw [hrhs, hGsum, hfin]

end CIV
