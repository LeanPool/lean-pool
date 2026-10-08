/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingCompactnessMovingCentre
public import LeanPool.CIVAxisymmetric.Zoom.CurvaturePairingBoundOfLe
public import LeanPool.CIVAxisymmetric.Zoom.SwirlPairingBoundOfLe
public import LeanPool.CIVAxisymmetric.Zoom.DtPastPairingOfPos
public import LeanPool.CIVAxisymmetric.Zoom.HalfPlaneCompactnessEventual
public import LeanPool.CIVAxisymmetric.Zoom.PotentialVorticityRescaled

/-!
# Compactness of the rescaled potential vorticities at the moving axis points

The compactness step `eq:aniso:zoom:finite:compactness` of Step 2 of the proof of
`prop:aniso:small`, at the moving axis points `(0, z_n)` of `eq:aniso:zoom:finite:variables`.

Off the axis the rescaled potential vorticity is `Ω_n = Θ_n / R`, where `Θ_n = λ_n² δ_n ω_θ` is the
rescaled azimuthal vorticity of `eq:aniso:zoom:receding:vorticity` taken about the axis point
itself (no radial offset). On a compact subset of the open half-plane `R` is bounded below, so
the time-pairing estimate of `Θ_n`, obtained from `eq:aniso:zoom:receding:equation` with `A = 0`
exactly as in the receding-axis case, holds with constants depending on that lower bound. The
half-plane compactness theorem then gives locally uniform convergence of `Θ_n` on
`{R > 0, τ ≤ -1}`, and dividing by `R` gives that of `Ω_n`.
-/

public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- The time-pairing estimate for the rescaled azimuthal vorticity about the moving axis points
`(0, zc n)`, on compact subsets of the open half-plane. -/
theorem hpair_zoomTheta_axis_eventual {C h CΓ ρ Rstar tstar : ℝ} (hh : 0 < h ∧ h < 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρR : ρ < Rstar) (hR1 : Rstar ≤ 1) (htstar : tstar < 0)
    {zc : ℕ → ℝ} (hzc : ∀ n, |zc n| ≤ ρ)
    (hCnn : 0 ≤ C) (hCΓnn : 0 ≤ CΓ)
    {u : ParabolicPoint → Vec3} (haniso : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    (hΓ : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, ∀ t ∈ Ioo tstar (0 : ℝ), |circulation u (x, t)| ≤ CΓ)
    (hforce : ForceC2Bounded f)
    (lam : ℕ → ℝ) (hlam_pos : ∀ n, 0 < lam n)
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0))) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → (∀ y ∈ K, 0 < y.1) → ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ
      ≤ -1) →
      ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧ ∀ᶠ n in atTop,
        ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ interior K →
        ∀ B : ℝ, 0 ≤ B →
          (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
          ∀ τ ∈ J, ∀ τ' ∈ J,
            |∫ y : ℝ × ℝ,
                (zoomTheta (lam n) h 0 (zc n) u (y, τ)
                  - zoomTheta (lam n) h 0 (zc n) u (y, τ')) * ψ y|
              ≤ Cₒ * B * |τ - τ'| := by
  have hcz : ∀ n, (0 : ℝ) ^ 2 + zc n ^ 2 ≤ ρ ^ 2 := fun n => by
    have := sq_le_sq' (abs_le.mp (hzc n)).1 (abs_le.mp (hzc n)).2
    simpa using this
  obtain ⟨M, hM⟩ := hforce
  have hMmax : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ max M 0 :=
    fun z hz i α hα => (hM z hz i α hα).trans (le_max_left _ _)
  intro K hK hKp J hJ hJsub
  obtain ⟨ε, hε, hεK⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ K, ε ≤ y.1 := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun y hy => by rw [hKe] at hy; exact absurd hy (by simp)⟩
    obtain ⟨y0, hy0, hmin⟩ := hK.exists_isMinOn hKne continuous_fst.continuousOn
    exact ⟨y0.1, hKp y0 hy0, fun y hy => hmin hy⟩
  set C₀ : ℝ := 4 * C ^ 2 * (volume K).toReal + 4 * C * (volume K).toReal
      + 2 * C / ε * (volume K).toReal + CΓ ^ 2 / ε ^ 3 * (volume K).toReal
      + 2 * max M 0 * (volume K).toReal with hC₀_def
  have hC₀nn : 0 ≤ C₀ := by rw [hC₀_def]; positivity
  refine ⟨C₀, hC₀nn, ?_⟩
  rcases J.eq_empty_or_nonempty with hJempty | hJne
  · refine Filter.Eventually.of_forall (fun n ψ _ _ _ B hB _ τ hτ => ?_)
    rw [hJempty] at hτ; exact absurd hτ (by simp)
  · set a : ℝ := sInf J with ha_def
    set b : ℝ := sSup J with hb_def
    have hJbdd : BddBelow J ∧ BddAbove J := ⟨hJ.bddBelow, hJ.bddAbove⟩
    have hab : a ≤ b := csInf_le_csSup hJne hJbdd.1 hJbdd.2
    have hb1 : b ≤ -1 := csSup_le hJne (fun τ hτ => hJsub τ hτ)
    have hJsubIcc : J ⊆ Icc a b := fun τ hτ => ⟨csInf_le hJbdd.1 hτ, le_csSup hJbdd.2 hτ⟩
    have hbigK : IsCompact (K ×ˢ Icc (a - 1 / 2) (b + 1 / 2)) := hK.prod isCompact_Icc
    have hbigKt : ∀ p ∈ K ×ˢ Icc (a - 1 / 2) (b + 1 / 2), p.2 < 0 := fun p hp => by
      have := hp.2.2; linarith only [this, hb1]
    have hwin := eventually_mem_zoomPointRec_moving hh hρ0 hρR htstar hcz hlam_lim _ hbigK hbigKt
    have hApos_ev : ∀ᶠ n in atTop, ∀ y ∈ K, ε ≤ 0 / lam n + y.1 :=
      Eventually.of_forall fun n y hy => by rw [zero_div, zero_add]; exact hεK y hy
    have hlam0 : Tendsto lam atTop (𝓝 (0 : ℝ)) := hlam_lim.mono_right nhdsWithin_le_nhds
    have hlam_le_ev : ∀ᶠ n in atTop, lam n < 1 :=
      hlam0.eventually_mem (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Iio (1 : ℝ)))
    have hunit := eventually_mem_zoomPointRec_moving hh hρ0 (hρR.trans_le hR1) (by norm_num :
      (-1 : ℝ) < 0) hcz hlam_lim _
      hbigK hbigKt
    filter_upwards [hwin, hunit, hApos_ev, hlam_le_ev] with n hwin_n hunit_n hApos_n hlam_lt
    have hwin' : ∀ y ∈ K, ∀ τ ∈ Icc (a - 1 / 2) (b + 1 / 2),
        (zoomPointRec (lam n) h 0 (zc n) (y, τ)).1 ∈ vec3Ball 0 Rstar ∧
          (zoomPointRec (lam n) h 0 (zc n) (y, τ)).2 ∈ Ioo tstar 0 :=
      fun y hy τ hτ => hwin_n (y, τ) ⟨hy, hτ⟩
    have hmem_n : ∀ y ∈ K, ∀ τ ∈ Icc (a - 1 / 2) (b + 1 / 2),
        zoomPointRec (lam n) h 0 (zc n) (y, τ) ∈ unitCylinder := by
      intro y hy τ hτ
      have := hunit_n (y, τ) ⟨hy, hτ⟩
      exact ⟨this.1, this.2⟩
    have hΓ' : ∀ z ∈ unitCylinder, z.1 ∈ vec3Ball 0 Rstar → z.2 ∈ Ioo tstar 0 →
        |circulation u z| ≤ CΓ := fun z _ h1 h2 => hΓ z.1 h1 z.2 h2
    have hlam_len : lam n ≤ 1 := hlam_lt.le
    intro ψ hψ hψc hψU B hB hψB
    have hdom : ∀ τ ∈ Icc a b,
        |∫ y : ℝ × ℝ, dtPast (fun q : (ℝ × ℝ) × ℝ => zoomTheta (lam n) h 0 (zc n) u q) (y, τ) * ψ y|
          ≤ C₀ * B := by
      intro τ hτ
      have hτbig : τ ∈ Icc (a - 1 / 2) (b + 1 / 2) :=
        ⟨by linarith only [hτ.1], by linarith only [hτ.2]⟩
      have hτm1 : τ ≤ -1 := by linarith only [hτ.2, hb1]
      have hmemτ : ∀ y ∈ K, zoomPointRec (lam n) h 0 (zc n) (y, τ) ∈ unitCylinder :=
        fun y hy => hmem_n y hy τ hτbig
      have hdelta : lam n ^ (2 * h) ≤ 1 :=
        Real.rpow_le_one (hlam_pos n).le hlam_len (by linarith only [hh.1])
      have hbT := transport_term_pairing_bound_fixed hCnn hh.1.le hh.2.le (hlam_pos n) hdelta
        haniso hu hK hτm1 hmemτ ψ hψ hψc hψU B hB hψB
      have hbD := diffusion_term_pairing_bound_fixed hCnn hh.1.le hh.2.le (hlam_pos n) hdelta
        haniso hu hK hτm1 hmemτ ψ hψ hψc hψU B hB hψB
      have hbC := curvature_term_pairing_bound_fixed_of_le hCnn hh.1.le hh.2.le (hlam_pos n) hdelta
        haniso hu hK hτm1 hmemτ hε hApos_n ψ hψ hψc hψU B hB hψB
      have hbS := swirl_term_pairing_bound_fixed_of_le hCΓnn (hlam_pos n) hdelta hu hK hmemτ
        (fun y hy => hΓ' _ (hmemτ y hy) (hwin' y hy τ hτbig).1 (hwin' y hy τ hτbig).2) hε
          hApos_n ψ hψ hψc hψU B
        hB hψB
      have hbF := forceTerm_pairing_bound_fixed_moving hh.1 (hlam_pos n) hlam_len
        (le_max_right M 0) hMmax hK τ hmemτ ψ hψ hψc hψU B hB hψB
      have hi1 := integrable_transportTerm_mul_zoomTheta (lam := lam n) hu hmemτ hψ hψc hψU
      have hi2 := integrable_diffusionTerm_mul_zoomTheta (lam := lam n) hu hmemτ hψ hψc hψU
      have hApos_n' : ∀ y ∈ K, (0 : ℝ) < 0 / lam n + y.1 :=
        fun y hy => by linarith only [hApos_n y hy, hε]
      have hi3 := integrable_curvatureTerm_mul_zoomTheta (hlam_pos n) hu hmemτ hApos_n' hψ hψc
        hψU
      have hi4 := integrable_swirlTerm_mul_zoomTheta (lam := lam n) hu hmemτ hApos_n' hψ hψc hψU
      have hi5 := integrable_forceTerm_mul_zoomTheta (lam := lam n) hsol.2.2.1 hmemτ hψ hψc hψU
      have hfin := dtPast_zoomTheta_pairing_bound_fixed_of_pos (hlam_pos n) hsol haxi hmemτ
        hApos_n' ψ hψU B (4 * C ^ 2 * (volume K).toReal) (4 * C * (volume K).toReal)
        (2 * C / ε * (volume K).toReal) (CΓ ^ 2 / ε ^ 3 * (volume K).toReal) (2 * max M 0 *
          (volume K).toReal)
        (fun y => -(dr (fun q : (ℝ × ℝ) × ℝ =>
            zoomVRec (lam n) h 0 (zc n) u q * zoomTheta (lam n) h 0 (zc n) u q) (y, τ)
          + dz (fun q : (ℝ × ℝ) × ℝ =>
            zoomWRec (lam n) h 0 (zc n) u q * zoomTheta (lam n) h 0 (zc n) u q) (y, τ)))
        (fun y => dr (dr (fun q : (ℝ × ℝ) × ℝ => zoomTheta (lam n) h 0 (zc n) u q)) (y, τ)
          + (lam n ^ (2 * h)) ^ 2 *
            dz (dz (fun q : (ℝ × ℝ) × ℝ => zoomTheta (lam n) h 0 (zc n) u q)) (y, τ))
        (fun y => dr (zoomTheta (lam n) h 0 (zc n) u) (y, τ) / (0 / lam n + y.1)
          - zoomTheta (lam n) h 0 (zc n) u (y, τ) / (0 / lam n + y.1) ^ 2)
        (fun y => 1 / (0 / lam n + y.1) *
          dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec (lam n) h 0 (zc n) u q ^ 2) (y, τ))
        (fun y => lam n ^ 4 * lam n ^ (2 * h) *
          curlComp f 1 (zoomPointRec (lam n) h 0 (zc n) (y, τ)))
        rfl rfl rfl rfl rfl hi1 hi2 hi3 hi4 hi5 hbT hbD hbC hbS hbF
      rw [hC₀_def]
      exact hfin
    exact fun τ hτ τ' hτ' => by
      have := exists_time_pairing_bound_of_dtPast_bound_zoomTheta hu hK hab hb1 hmem_n hC₀nn hB
        ψ hψ hψc hψU hdom τ (hJsubIcc hτ) τ' (hJsubIcc hτ')
      simpa using this

/-- Off the axis the rescaled potential vorticity is the rescaled azimuthal vorticity about the
axis point divided by `R`. -/
theorem zoomOmega_eq_zoomTheta_div (lam h zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (p : (ℝ × ℝ) × ℝ) (hR : p.1.1 ≠ 0) :
    zoomOmega lam h zc u p = zoomTheta lam h 0 zc u p / p.1.1 := by
  have hpt : zoomPointRec lam h 0 zc p = zoomPoint lam h zc p := by
    unfold zoomPointRec zoomPoint; rw [zero_add]
  have h0 : (zoomPoint lam h zc p).1 0 = lam * p.1.1 := by simp [zoomPoint, meridional]
  have hne : lam * p.1.1 ≠ 0 := mul_ne_zero hlam.ne' hR
  unfold zoomOmega zoomTheta potentialVorticity
  have hc : ¬ ((zoomPoint lam h zc p).1 0 = 0) := by rw [h0]; exact hne
  rw [hpt]
  simp only [hc, ↓reduceIte]
  rw [h0]
  field_simp

/-- `eq:aniso:zoom:finite:compactness` at the moving axis points: along a subsequence the
rescaled potential vorticities converge uniformly on every compact subset of
`{R > 0, τ ≤ -1}`, to a limit continuous there. -/
theorem exists_subseq_tendstoUniformlyOn_zoomOmega_moving {C h CΓ ρ Rstar tstar : ℝ}
    (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ) (hρR : ρ < Rstar) (hR1 : Rstar ≤ 1)
    (htstar : tstar < 0) {zc : ℕ → ℝ} (hzc : ∀ n, |zc n| ≤ ρ)
    (hCnn : 0 ≤ C) (hCΓnn : 0 ≤ CΓ)
    {u : ParabolicPoint → Vec3} (haniso : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    (hΓ : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, ∀ t ∈ Ioo tstar (0 : ℝ), |circulation u (x, t)| ≤ CΓ)
    (hforce : ForceC2Bounded f)
    (lam : ℕ → ℝ) (hlam_pos : ∀ n, 0 < lam n)
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ω : (ℝ × ℝ) × ℝ → ℝ,
      ContinuousOn Ω {p : (ℝ × ℝ) × ℝ | 0 < p.1.1 ∧ p.2 ≤ -1} ∧
      ∀ K : Set ((ℝ × ℝ) × ℝ), IsCompact K → K ⊆ {p : (ℝ × ℝ) × ℝ | 0 < p.1.1 ∧ p.2 ≤ -1} →
        TendstoUniformlyOn (fun n => zoomOmega (lam (φ n)) h (zc (φ n)) u) Ω atTop K := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  have hρ1 : ρ < 1 := hρR.trans_le hR1
  have hcz : ∀ n, (0 : ℝ) ^ 2 + zc n ^ 2 ≤ ρ ^ 2 := fun n => by
    have := sq_le_sq' (abs_le.mp (hzc n)).1 (abs_le.mp (hzc n)).2
    simpa using this
  have hlamlt : ∀ᶠ n in atTop, lam n < 1 :=
    (hlam_lim.mono_right nhdsWithin_le_nhds).eventually_mem
      (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Iio (1 : ℝ)))
  have hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → (∀ y ∈ K, 0 < y.1) →
      ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ ≤ -1) →
      ∃ M : ℝ, ∀ᶠ n in atTop, ∀ y ∈ K, ∀ τ ∈ J, |zoomTheta (lam n) h 0 (zc n) u (y, τ)| ≤ M := by
    intro K hK _ J hJ hJs
    refine ⟨C * 2, ?_⟩
    filter_upwards [eventually_zoomPointRec_mem_unitCylinder_moving hh hρ0 hρ1 hcz lam hlam_lim
      K hK J hJ hJs, hlamlt] with n hn hl
    intro y hy τ hτ
    have hb := abs_zoomTheta_le C h (lam n) 0 (zc n) (hlam_pos n) u haniso hu2 (y, τ)
      (hn y hy τ hτ)
    have hτ1 : (1 : ℝ) ≤ -τ := by have := hJs τ hτ; linarith only [this]
    have e1 : (-(y, τ).2) ^ (-1 + h) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by linarith only [hh.2])
    have e2 : (-(y, τ).2) ^ (-1 - h) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by linarith only [hh.1])
    have e1' : 0 ≤ (-(y, τ).2) ^ (-1 + h) := Real.rpow_nonneg (by linarith only [hτ1]) _
    have hd0 : 0 ≤ lam n ^ (2 * h) := Real.rpow_nonneg (hlam_pos n).le _
    have hd1 : lam n ^ (2 * h) ≤ 1 :=
      Real.rpow_le_one (hlam_pos n).le hl.le (by linarith only [hh.1])
    have hd2 : (lam n ^ (2 * h)) ^ 2 ≤ 1 := by nlinarith only [hd0, hd1]
    have hprod : (lam n ^ (2 * h)) ^ 2 * (-(y, τ).2) ^ (-1 + h) ≤ 1 := by
      nlinarith only [hd2, e1, e1', sq_nonneg (lam n ^ (2 * h))]
    have hsum : (lam n ^ (2 * h)) ^ 2 * (-(y, τ).2) ^ (-1 + h) + (-(y, τ).2) ^ (-1 - h) ≤ 2 := by
      linarith only [hprod, e2]
    exact hb.trans (by
      have := mul_le_mul_of_nonneg_left hsum hCnn
      linarith only [this])
  have hlip : ∀ K : Set (ℝ × ℝ), IsCompact K → (∀ y ∈ K, 0 < y.1) →
      ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ ≤ -1) →
      ∃ L : ℝ, ∀ᶠ n in atTop, ∀ τ ∈ J,
        LipschitzOnWith (Real.toNNReal L) (fun y => zoomTheta (lam n) h 0 (zc n) u (y, τ)) K := by
    intro K hK _ J hJ hJs
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn (s := K))
    set Rt : Set (ℝ × ℝ) := Icc (-B) B ×ˢ Icc (-B) B
    have hKR : K ⊆ Rt := fun y hy => by
      have h1 : ‖y‖ ≤ B := hB y hy
      have ha : |y.1| ≤ B := le_trans (by simpa using norm_fst_le y) h1
      have hb' : |y.2| ≤ B := le_trans (by simpa using norm_snd_le y) h1
      exact ⟨abs_le.mp ha, abs_le.mp hb'⟩
    refine ⟨8 * C, ?_⟩
    filter_upwards [eventually_zoomPointRec_mem_unitCylinder_moving hh hρ0 hρ1 hcz lam hlam_lim Rt
      (isCompact_Icc.prod isCompact_Icc) J hJ hJs, hlamlt] with n hn hl
    intro τ hτ
    have hd1 : lam n ^ (2 * h) ≤ 1 :=
      Real.rpow_le_one (hlam_pos n).le hl.le (by linarith only [hh.1])
    exact (lipschitzOnWith_zoomTheta (hlam_pos n) haniso hu2 hCnn hh.1.le hh.2.le hd1 (hJs τ hτ)
      (fun y hy => hn y hy τ hτ)).mono hKR
  obtain ⟨φ, hφ, Θ, hΘc, hΘconv⟩ :=
    exists_subseq_tendstoUniformlyOn_of_lipschitz_of_pairings_eventually
    (fun n => zoomTheta (lam n) h 0 (zc n) u) hbdd hlip
    (hpair_zoomTheta_axis_eventual hh hρ0 hρR hR1 htstar hzc hCnn hCΓnn haniso hu hsol haxi hΓ
      hforce lam hlam_pos hlam_lim)
  refine ⟨φ, hφ, fun p => Θ p / p.1.1, ?_, ?_⟩
  · exact hΘc.div (continuous_fst.comp continuous_fst).continuousOn fun p hp => hp.1.ne'
  · intro K hK hKs
    have hconv := hΘconv K hK hKs
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · rw [hKe]; exact tendstoUniformlyOn_empty
    obtain ⟨p0, hp0, hmin⟩ := hK.exists_isMinOn hKne
      (continuous_fst.comp continuous_fst).continuousOn
    have hε : 0 < p0.1.1 := (hKs hp0).1
    rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
    intro δ hδ
    filter_upwards [hconv (δ * p0.1.1) (mul_pos hδ hε)] with n hn p hp
    have hp1 : 0 < p.1.1 := (hKs hp).1
    have hle : p0.1.1 ≤ p.1.1 := hmin hp
    rw [zoomOmega_eq_zoomTheta_div _ _ _ (hlam_pos (φ n)) u p hp1.ne', Real.dist_eq,
      ← sub_div, abs_div, abs_of_pos hp1, div_lt_iff₀ hp1]
    have h1 := hn p hp
    rw [Real.dist_eq] at h1
    nlinarith only [h1, hle, hδ]

end CIV
