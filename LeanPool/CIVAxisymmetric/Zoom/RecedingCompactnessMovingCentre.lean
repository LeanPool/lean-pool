/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingTransportPairingBound
public import LeanPool.CIVAxisymmetric.Zoom.RecedingDiffusionPairingBound
public import LeanPool.CIVAxisymmetric.Zoom.RecedingCurvaturePairingBound
public import LeanPool.CIVAxisymmetric.Zoom.RecedingSwirlPairingBound
public import LeanPool.CIVAxisymmetric.Zoom.RecedingForcePairingBound
public import LeanPool.CIVAxisymmetric.Zoom.RecedingPairingIntegrability
public import LeanPool.CIVAxisymmetric.Zoom.RecedingDtPastPairingAssembly
public import LeanPool.CIVAxisymmetric.Zoom.RecedingTimePairingWiring
public import LeanPool.CIVAxisymmetric.Zoom.RecedingWholePlaneCompactness
public import LeanPool.CIVAxisymmetric.Zoom.ThetaLipschitz

/-!
# Receding-branch compactness at a moving zoom centre

The receding zoom of the proof of `prop:aniso:small` is taken about the selected points
`x_n = (r_n, z_n)`, which move with `n` (`eq:aniso:zoom:receding:variables`). This module restates
the time-pairing estimate for the rescaled vorticity quotient at a moving centre `(rc n, zc n)`
with `r_n / λ_n → ∞`, using the circulation bound only on the window `B(R_*) × (t_*, 0)` of
`eq:aniso:zoom:circulation`, and concludes the locally uniform convergence of the rescaled
quotients on `ℝ² × (−∞, −1]` along a subsequence.
-/

public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

theorem forceTerm_pairing_bound_fixed_moving {h lam rc zc M : ℝ} (hh0 : 0 < h)
    (hlam_pos : 0 < lam) (hlam_le : lam ≤ 1)
    {f : ParabolicPoint → Vec3}
    (hMnn : 0 ≤ M)
    (hMmax : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ M)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (τ : ℝ)
    (hmem : ∀ y ∈ K, zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    (ψ : ℝ × ℝ → ℝ) (_ : ContDiff ℝ (⊤ : ℕ∞) ψ) (_ : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ interior K) (B : ℝ) (_ : 0 ≤ B)
    (hψB : ∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) :
    |∫ y : ℝ × ℝ,
        (lam ^ 4 * lam ^ (2 * h) * curlComp f 1 (zoomPointRec lam h rc zc (y, τ))) * ψ y|
      ≤ 2 * M * (volume K).toReal * B := by
  have h4nn : (0 : ℝ) ≤ lam ^ 4 := pow_nonneg hlam_pos.le 4
  have h2hnn : (0 : ℝ) ≤ lam ^ (2 * h) := Real.rpow_nonneg hlam_pos.le _
  have hAle : lam ^ 4 * lam ^ (2 * h) ≤ 1 := by
    have h4 : lam ^ 4 ≤ 1 := pow_le_one₀ hlam_pos.le hlam_le
    have h2h : lam ^ (2 * h) ≤ 1 := Real.rpow_le_one hlam_pos.le hlam_le (by linarith only [hh0])
    calc lam ^ 4 * lam ^ (2 * h) ≤ 1 * 1 := mul_le_mul h4 h2h h2hnn (by norm_num)
      _ = 1 := by norm_num
  have ha : ∀ y ∈ K, |lam ^ 4 * lam ^ (2 * h) * curlComp f 1 (zoomPointRec lam h rc zc (y, τ))|
      ≤ 2 * M := by
    intro y hy
    have hp : zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder := hmem y hy
    have hbound := abs_recedingForce_le (lam := lam) (h := h) (rc := rc) (zc := zc)
      hlam_pos hMmax (p := (y, τ)) hp
    have hfactor : lam ^ 4 * lam ^ (2 * h) * (2 * M) ≤ 1 * (2 * M) :=
      mul_le_mul_of_nonneg_right hAle (by linarith only [hMnn])
    calc |lam ^ 4 * lam ^ (2 * h) * curlComp f 1 (zoomPointRec lam h rc zc (y, τ))|
          ≤ 2 * M * (lam ^ 4 * lam ^ (2 * h)) := hbound
      _ = lam ^ 4 * lam ^ (2 * h) * (2 * M) := by ring
      _ ≤ 1 * (2 * M) := hfactor
      _ = 2 * M := by ring
  have hψBK : ∀ y, |ψ y| ≤ B := fun y => (hψB y).1
  have hψsub : tsupport ψ ⊆ K := hψU.trans interior_subset
  have hfinal := abs_integral_mul_le_of_tsupport_subset hK.measure_lt_top hψsub ha hψBK
  calc |∫ y : ℝ × ℝ,
        (lam ^ 4 * lam ^ (2 * h) * curlComp f 1 (zoomPointRec lam h rc zc (y, τ))) * ψ y|
      ≤ 2 * M * B * (volume K).toReal := hfinal
    _ = 2 * M * (volume K).toReal * B := by ring


theorem eventually_mem_zoomPointRec_moving {h ρ Rstar tstar : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0 :
    0 ≤ ρ)
    (hρ : ρ < Rstar) (htstar : tstar < 0) {rc zc : ℕ → ℝ}
    (hcz : ∀ n, rc n ^ 2 + zc n ^ 2 ≤ ρ ^ 2) {lam : ℕ → ℝ}
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (K : Set ((ℝ × ℝ) × ℝ)) (hK : IsCompact K) (hKt : ∀ p ∈ K, p.2 < 0) :
    ∀ᶠ n in atTop, ∀ p ∈ K,
      (zoomPointRec (lam n) h (rc n) (zc n) p).1 ∈ vec3Ball 0 Rstar ∧
        (zoomPointRec (lam n) h (rc n) (zc n) p).2 ∈ Ioo tstar 0 := by
  have hexp : 0 < 1 - 2 * h := by linarith only [hh.2]
  have hRpos : 0 < Rstar := lt_of_le_of_lt hρ0 hρ
  have ht := hlam_lim.eventually (eventually_zoomPointRec_time_mem 0 (h := h) (zc := 0) htstar K
    hK hKt)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_fst.continuousOn (s := K))
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  set g := Rstar ^ 2 - ρ ^ 2 with hg
  have hgpos : 0 < g := by nlinarith only [hρ0, hρ]
  set ε := min 1 (g / (2 * (2 * ρ + 1))) with hε
  have hεpos : 0 < ε := lt_min one_pos (div_pos hgpos (by linarith only [hρ0]))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεg : (2 * ρ + 1) * ε ≤ g / 2 := by
    have := min_le_right 1 (g / (2 * (2 * ρ + 1)))
    rw [← hε] at this
    have h2 : 0 < 2 * ρ + 1 := by linarith only [hρ0]
    calc (2 * ρ + 1) * ε ≤ (2 * ρ + 1) * (g / (2 * (2 * ρ + 1))) :=
          mul_le_mul_of_nonneg_left this h2.le
      _ = g / 2 := by field_simp
  set δ := ε / (2 * B' + 1) with hδ
  have hδpos : 0 < δ := div_pos hεpos (by linarith only [hB'0])
  have h2Bδ : 2 * B' * δ ≤ ε := by
    rw [hδ]
    have h1 : 0 < 2 * B' + 1 := by linarith only [hB'0]
    rw [← mul_div_assoc, div_le_iff₀ h1]
    nlinarith only [hεpos, hB'0]
  have hlam0 : Tendsto lam atTop (nhds 0) := hlam_lim.mono_right nhdsWithin_le_nhds
  have hrp : Tendsto (fun n => lam n ^ (1 - 2 * h)) atTop (nhds 0) := by
    have := ((Real.continuousAt_rpow_const 0 (1 - 2 * h) (Or.inr hexp.le)).tendsto).comp hlam0
    rw [Real.zero_rpow (ne_of_gt hexp)] at this
    exact this
  have hpos := hlam_lim.eventually self_mem_nhdsWithin
  filter_upwards [ht, hpos, hlam0.eventually (gt_mem_nhds hδpos),
    hrp.eventually (gt_mem_nhds hδpos)] with n htn hposn hl1 hl2 p hp
  refine ⟨?_, htn p hp⟩
  have hlpos : 0 < lam n := hposn
  have hnp : ‖p.1‖ ≤ B' := (hB p hp).trans (le_max_left _ _)
  have hx : |p.1.1| ≤ B' := le_trans (by simpa using norm_fst_le p.1) hnp
  have hy : |p.1.2| ≤ B' := le_trans (by simpa using norm_snd_le p.1) hnp
  have hrp0 : 0 ≤ lam n ^ (1 - 2 * h) := Real.rpow_nonneg hlpos.le _
  set c := lam n * p.1.1
  set d := lam n ^ (1 - 2 * h) * p.1.2
  have hc : |c| ≤ δ * B' := by
    simp only [c, abs_mul, abs_of_pos hlpos]
    exact mul_le_mul hl1.le hx (abs_nonneg _) hδpos.le
  have hd : |d| ≤ δ * B' := by
    simp only [d, abs_mul, abs_of_nonneg hrp0]
    exact mul_le_mul hl2.le hy (abs_nonneg _) hδpos.le
  have ha : |rc n| ≤ ρ := abs_le_of_sq_le_sq (by nlinarith only [hcz n, sq_nonneg (zc n)]) hρ0
  have hb : |zc n| ≤ ρ := abs_le_of_sq_le_sq (by nlinarith only [hcz n, sq_nonneg (rc n)]) hρ0
  have he : |c| + |d| ≤ ε := by linarith only [hc, hd, h2Bδ]
  have hac : rc n * c ≤ ρ * |c| := by
    calc rc n * c ≤ |rc n * c| := le_abs_self _
      _ = |rc n| * |c| := abs_mul _ _
      _ ≤ ρ * |c| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have hbd : zc n * d ≤ ρ * |d| := by
    calc zc n * d ≤ |zc n * d| := le_abs_self _
      _ = |zc n| * |d| := abs_mul _ _
      _ ≤ ρ * |d| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have hcd : c ^ 2 + d ^ 2 ≤ (|c| + |d|) ^ 2 := by
    nlinarith only [sq_abs c, sq_abs d, abs_nonneg c, abs_nonneg d]
  have hee : (|c| + |d|) ^ 2 ≤ ε := by
    have h0 : 0 ≤ |c| + |d| := by positivity
    nlinarith only [he, h0, hε1]
  have hsum : (rc n + c) ^ 2 + (zc n + d) ^ 2 < Rstar ^ 2 := by
    have hρe : ρ * (|c| + |d|) ≤ ρ * ε := mul_le_mul_of_nonneg_left he hρ0
    nlinarith only [hcz n, hac, hbd, hcd, hee, hρe, hεg, hgpos, hg]
  show meridional (rc n + lam n * p.1.1) (zc n + lam n ^ (1 - 2 * h) * p.1.2) ∈ vec3Ball 0 Rstar
  rw [meridional_mem_vec3Ball_zero_iff]
  exact ⟨hsum, hRpos⟩

/-- `hpair` for `zoomTheta` at the paper's MOVING centre `x_n = (rc n, zc n)`, with the
circulation bound only on the window `B(R_*) × (t_*, 0)` of `eq:aniso:zoom:circulation`. -/
theorem hpair_zoomTheta_eventual_moving {C h CΓ ρ Rstar tstar : ℝ} (hh : 0 < h ∧ h < 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρR : ρ < Rstar) (hR1 : Rstar ≤ 1) (htstar : tstar < 0)
    {rc zc : ℕ → ℝ} (hcz : ∀ n, rc n ^ 2 + zc n ^ 2 ≤ ρ ^ 2)
    (hCnn : 0 ≤ C) (hCΓnn : 0 ≤ CΓ)
    {u : ParabolicPoint → Vec3} (haniso : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    (hΓ : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, ∀ t ∈ Ioo tstar (0 : ℝ), |circulation u (x, t)| ≤ CΓ)
    (hforce : ForceC2Bounded f)
    (lam : ℕ → ℝ) (hlam_pos : ∀ n, 0 < lam n)
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (hA : Tendsto (fun n => rc n / lam n) atTop atTop) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ ≤ -1) →
      ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧ ∀ᶠ n in atTop,
        ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ interior K →
        ∀ B : ℝ, 0 ≤ B →
          (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
          ∀ τ ∈ J, ∀ τ' ∈ J,
            |∫ y : ℝ × ℝ,
                (zoomTheta (lam n) h (rc n) (zc n) u (y, τ)
                  - zoomTheta (lam n) h (rc n) (zc n) u (y, τ')) * ψ y|
              ≤ Cₒ * B * |τ - τ'| := by
  obtain ⟨M, hM⟩ := hforce
  have hMmax : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ max M 0 :=
    fun z hz i α hα => (hM z hz i α hα).trans (le_max_left _ _)
  intro K hK J hJ hJsub
  set C₀ : ℝ := 4 * C ^ 2 * (volume K).toReal + 4 * C * (volume K).toReal
      + 2 * C * (volume K).toReal + CΓ ^ 2 * (volume K).toReal
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
    have hApos_ev : ∀ᶠ n in atTop, ∀ y ∈ K, (1 : ℝ) ≤ rc n / lam n + y.1 := by
      obtain ⟨B', hB'⟩ := hK.exists_bound_of_continuousOn (continuous_fst.continuousOn (s := K))
      filter_upwards [hA.eventually_ge_atTop (B' + 1)] with n hn y hy
      have hy1 : |y.1| ≤ B' := by have := hB' y hy; rwa [Real.norm_eq_abs] at this
      linarith only [hn, (abs_le.mp hy1).1]
    have hlam0 : Tendsto lam atTop (𝓝 (0 : ℝ)) := hlam_lim.mono_right nhdsWithin_le_nhds
    have hlam_le_ev : ∀ᶠ n in atTop, lam n < 1 :=
      hlam0.eventually_mem (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Iio (1 : ℝ)))
    have hunit := eventually_mem_zoomPointRec_moving hh hρ0 (hρR.trans_le hR1) (by norm_num :
      (-1 : ℝ) < 0) hcz hlam_lim _
      hbigK hbigKt
    filter_upwards [hwin, hunit, hApos_ev, hlam_le_ev] with n hwin_n hunit_n hApos_n hlam_lt
    have hwin' : ∀ y ∈ K, ∀ τ ∈ Icc (a - 1 / 2) (b + 1 / 2),
        (zoomPointRec (lam n) h (rc n) (zc n) (y, τ)).1 ∈ vec3Ball 0 Rstar ∧
          (zoomPointRec (lam n) h (rc n) (zc n) (y, τ)).2 ∈ Ioo tstar 0 :=
      fun y hy τ hτ => hwin_n (y, τ) ⟨hy, hτ⟩
    have hmem_n : ∀ y ∈ K, ∀ τ ∈ Icc (a - 1 / 2) (b + 1 / 2),
        zoomPointRec (lam n) h (rc n) (zc n) (y, τ) ∈ unitCylinder := by
      intro y hy τ hτ
      have := hunit_n (y, τ) ⟨hy, hτ⟩
      exact ⟨this.1, this.2⟩
    have hΓ' : ∀ z ∈ unitCylinder, z.1 ∈ vec3Ball 0 Rstar → z.2 ∈ Ioo tstar 0 →
        |circulation u z| ≤ CΓ := fun z _ h1 h2 => hΓ z.1 h1 z.2 h2
    have hlam_len : lam n ≤ 1 := hlam_lt.le
    intro ψ hψ hψc hψU B hB hψB
    have hdom : ∀ τ ∈ Icc a b,
        |∫ y : ℝ × ℝ, dtPast (fun q : (ℝ × ℝ) × ℝ => zoomTheta (lam n) h (rc n) (zc n) u q) (y,
          τ) * ψ y|
          ≤ C₀ * B := by
      intro τ hτ
      have hτbig : τ ∈ Icc (a - 1 / 2) (b + 1 / 2) :=
        ⟨by linarith only [hτ.1], by linarith only [hτ.2]⟩
      have hτm1 : τ ≤ -1 := by linarith only [hτ.2, hb1]
      have hmemτ : ∀ y ∈ K, zoomPointRec (lam n) h (rc n) (zc n) (y, τ) ∈ unitCylinder :=
        fun y hy => hmem_n y hy τ hτbig
      have hdelta : lam n ^ (2 * h) ≤ 1 :=
        Real.rpow_le_one (hlam_pos n).le hlam_len (by linarith only [hh.1])
      have hbT := transport_term_pairing_bound_fixed hCnn hh.1.le hh.2.le (hlam_pos n) hdelta
        haniso hu hK hτm1 hmemτ ψ hψ hψc hψU B hB hψB
      have hbD := diffusion_term_pairing_bound_fixed hCnn hh.1.le hh.2.le (hlam_pos n) hdelta
        haniso hu hK hτm1 hmemτ ψ hψ hψc hψU B hB hψB
      have hbC := curvature_term_pairing_bound_fixed hCnn hh.1.le hh.2.le (hlam_pos n) hdelta
        haniso hu hK hτm1 hmemτ hApos_n ψ hψ hψc hψU B hB hψB
      have hbS := swirl_term_pairing_bound_fixed hCΓnn (hlam_pos n) hdelta hu hK hmemτ
        (fun y hy => hΓ' _ (hmemτ y hy) (hwin' y hy τ hτbig).1 (hwin' y hy τ hτbig).2) hApos_n ψ
          hψ hψc hψU B
        hB hψB
      have hbF := forceTerm_pairing_bound_fixed_moving hh.1 (hlam_pos n) hlam_len
        (le_max_right M 0) hMmax hK τ hmemτ ψ hψ hψc hψU B hB hψB
      have hi1 := integrable_transportTerm_mul_zoomTheta (lam := lam n) hu hmemτ hψ hψc hψU
      have hi2 := integrable_diffusionTerm_mul_zoomTheta (lam := lam n) hu hmemτ hψ hψc hψU
      have hApos_n' : ∀ y ∈ K, (0 : ℝ) < rc n / lam n + y.1 :=
        fun y hy => by linarith only [hApos_n y hy]
      have hi3 := integrable_curvatureTerm_mul_zoomTheta (hlam_pos n) hu hmemτ hApos_n' hψ hψc
        hψU
      have hi4 := integrable_swirlTerm_mul_zoomTheta (lam := lam n) hu hmemτ hApos_n' hψ hψc hψU
      have hi5 := integrable_forceTerm_mul_zoomTheta (lam := lam n) hsol.2.2.1 hmemτ hψ hψc hψU
      have hfin := dtPast_zoomTheta_pairing_bound_fixed (hlam_pos n) hsol haxi hmemτ hApos_n ψ
        hψU B (4 * C ^ 2 * (volume K).toReal) (4 * C * (volume K).toReal)
        (2 * C * (volume K).toReal) (CΓ ^ 2 * (volume K).toReal) (2 * max M 0 * (volume K).toReal)
        (fun y => -(dr (fun q : (ℝ × ℝ) × ℝ =>
            zoomVRec (lam n) h (rc n) (zc n) u q * zoomTheta (lam n) h (rc n) (zc n) u q) (y, τ)
          + dz (fun q : (ℝ × ℝ) × ℝ =>
            zoomWRec (lam n) h (rc n) (zc n) u q * zoomTheta (lam n) h (rc n) (zc n) u q) (y, τ)))
        (fun y => dr (dr (fun q : (ℝ × ℝ) × ℝ => zoomTheta (lam n) h (rc n) (zc n) u q)) (y, τ)
          + (lam n ^ (2 * h)) ^ 2 *
            dz (dz (fun q : (ℝ × ℝ) × ℝ => zoomTheta (lam n) h (rc n) (zc n) u q)) (y, τ))
        (fun y => dr (zoomTheta (lam n) h (rc n) (zc n) u) (y, τ) / (rc n / lam n + y.1)
          - zoomTheta (lam n) h (rc n) (zc n) u (y, τ) / (rc n / lam n + y.1) ^ 2)
        (fun y => 1 / (rc n / lam n + y.1) *
          dz (fun q : (ℝ × ℝ) × ℝ => zoomSRec (lam n) h (rc n) (zc n) u q ^ 2) (y, τ))
        (fun y => lam n ^ 4 * lam n ^ (2 * h) *
          curlComp f 1 (zoomPointRec (lam n) h (rc n) (zc n) (y, τ)))
        rfl rfl rfl rfl rfl hi1 hi2 hi3 hi4 hi5 hbT hbD hbC hbS hbF
      rw [hC₀_def]
      exact hfin
    exact fun τ hτ τ' hτ' => by
      have := exists_time_pairing_bound_of_dtPast_bound_zoomTheta hu hK hab hb1 hmem_n hC₀nn hB
        ψ hψ hψc hψU hdom τ (hJsubIcc hτ) τ' (hJsubIcc hτ')
      simpa using this



theorem eventually_zoomPointRec_mem_unitCylinder_moving {h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0
    : 0 ≤ ρ) (hρ1 : ρ < 1)
    {rc zc : ℕ → ℝ} (hcz : ∀ n, rc n ^ 2 + zc n ^ 2 ≤ ρ ^ 2)
    (lam : ℕ → ℝ) (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (J : Set ℝ) (hJ : IsCompact J) (hJs : ∀ τ ∈ J, τ ≤ -1) :
    ∀ᶠ n in atTop, ∀ y ∈ K, ∀ τ ∈ J,
      zoomPointRec (lam n) h (rc n) (zc n) (y, τ) ∈ unitCylinder := by
  filter_upwards [eventually_mem_zoomPointRec_moving hh hρ0 hρ1 (by norm_num : (-1 : ℝ) < 0) hcz
    hlam_lim (K ×ˢ J)
    (hK.prod hJ) (fun p hp => by have := hJs p.2 hp.2; linarith only [this])] with n hn y hy τ hτ
  have hp := hn (y, τ) ⟨hy, hτ⟩
  exact ⟨hp.1, hp.2⟩

/-- The compactness statement at the paper's moving centre, circulation on the window only. -/
theorem exists_subseq_tendstoUniformlyOn_zoomTheta_moving {C h CΓ ρ Rstar tstar : ℝ} (hh : 0 < h
    ∧ h < 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρR : ρ < Rstar) (hR1 : Rstar ≤ 1) (htstar : tstar < 0)
    {rc zc : ℕ → ℝ} (hcz : ∀ n, rc n ^ 2 + zc n ^ 2 ≤ ρ ^ 2)
    (hCnn : 0 ≤ C) (hCΓnn : 0 ≤ CΓ)
    {u : ParabolicPoint → Vec3} (haniso : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {pr : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u pr f unitCylinder) (haxi : IsAxisymmetricOn u unitCylinder)
    (hΓ : ∀ x ∈ vec3Ball (0 : Vec3) Rstar, ∀ t ∈ Ioo tstar (0 : ℝ), |circulation u (x, t)| ≤ CΓ)
    (hforce : ForceC2Bounded f)
    (lam : ℕ → ℝ) (hlam_pos : ∀ n, 0 < lam n)
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (hA : Tendsto (fun n => rc n / lam n) atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ω : (ℝ × ℝ) × ℝ → ℝ,
      ContinuousOn Ω {q : (ℝ × ℝ) × ℝ | q.2 ≤ -1} ∧
      ∀ K : Set ((ℝ × ℝ) × ℝ), IsCompact K → K ⊆ {q : (ℝ × ℝ) × ℝ | q.2 ≤ -1} →
        TendstoUniformlyOn (fun n => zoomTheta (lam (φ n)) h (rc (φ n)) (zc (φ n)) u) Ω atTop K
          := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  have hρ1 : ρ < 1 := hρR.trans_le hR1
  have hlamlt : ∀ᶠ n in atTop, lam n < 1 :=
    (hlam_lim.mono_right nhdsWithin_le_nhds).eventually_mem
      (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Iio (1 : ℝ)))
  refine exists_subseq_tendstoUniformlyOn_of_lipschitz_of_pairings_plane_eventually
    (fun n => zoomTheta (lam n) h (rc n) (zc n) u) ?_ ?_
    (hpair_zoomTheta_eventual_moving hh hρ0 hρR hR1 htstar hcz hCnn hCΓnn haniso hu hsol haxi hΓ
      hforce lam hlam_pos hlam_lim hA)
  · intro K hK J hJ hJs
    refine ⟨C * 2, ?_⟩
    filter_upwards [eventually_zoomPointRec_mem_unitCylinder_moving hh hρ0 hρ1 hcz lam hlam_lim
      K hK J hJ hJs, hlamlt] with n hn hl
    intro y hy τ hτ
    have hb := abs_zoomTheta_le C h (lam n) (rc n) (zc n) (hlam_pos n) u haniso hu2 (y, τ)
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
  · intro K hK J hJ hJs
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn (s := K))
    set Rt : Set (ℝ × ℝ) := Icc (-B) B ×ˢ Icc (-B) B
    have hKR : K ⊆ Rt := fun y hy => by
      have h1 : ‖y‖ ≤ B := hB y hy
      have ha : |y.1| ≤ B := le_trans (by simpa using norm_fst_le y) h1
      have hb' : |y.2| ≤ B := le_trans (by simpa using norm_snd_le y) h1
      exact ⟨abs_le.mp ha, abs_le.mp hb'⟩
    refine ⟨8 * C, ?_⟩
    filter_upwards [eventually_zoomPointRec_mem_unitCylinder_moving hh hρ0 hρ1 hcz lam hlam_lim
      Rt (isCompact_Icc.prod isCompact_Icc)
      J hJ hJs, hlamlt] with n hn hl
    intro τ hτ
    have hd1 : lam n ^ (2 * h) ≤ 1 :=
      Real.rpow_le_one (hlam_pos n).le hl.le (by linarith only [hh.1])
    exact (lipschitzOnWith_zoomTheta (hlam_pos n) haniso hu2 hCnn hh.1.le hh.2.le hd1 (hJs τ hτ)
      (fun y hy => hn y hy τ hτ)).mono hKR

end CIV
