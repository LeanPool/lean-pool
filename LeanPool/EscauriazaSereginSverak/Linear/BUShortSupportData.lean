/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffL2Basis
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortRescalingValues

/-!
# Quadratic data on the cutoff support

The shifted field and its specified weak derivatives have finite quadratic
energy on the compact support of the short-time scalar cutoff.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The rescaled field and its three derivative fields belong to `L²` on
the compact support of the smooth short-time cutoff. -/
theorem bu_short_support_memLp_data
    (scale R ε : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1))
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    let κ := buShortFullCutoff scale R hR ε
    let K := buCutSupportSet κ
    MemLp (buAffineField (-scale ^ 2 / 2) scale w) 2 (volume.restrict K) ∧
      MemLp (buAffineDw (-scale ^ 2 / 2) scale Dw) 2 (volume.restrict K) ∧
      MemLp (buAffineD2w (-scale ^ 2 / 2) scale D2w) 2 (volume.restrict K) ∧
      MemLp (buAffineDtw (-scale ^ 2 / 2) scale Dtw) 2 (volume.restrict K) := by
  let κ := buShortFullCutoff scale R hR ε
  let K := buCutSupportSet κ
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  let D2v := buAffineD2w (-scale ^ 2 / 2) scale D2w
  let Dtv := buAffineDtw (-scale ^ 2 / 2) scale Dtw
  obtain ⟨hκcompact, hκts⟩ :=
    buShortFullCutoff_compact_support hscale hscale1 hR hε
  have hKcompact : IsCompact K := by
    dsimp [K, buCutSupportSet]
    exact parabolicHomeomorph.isCompact_preimage.mpr hκcompact.isCompact
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  have hKsub : K ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
      (Ioo (1 / 2 : ℝ) 1) := by
    intro z hz
    have hq := hκts hz
    rcases z with ⟨y, s⟩
    change 1 < y 2 ∧ s ∈ Ioo (1 / 2 : ℝ) 1 at hq
    exact ⟨lt_trans (by norm_num : (0 : ℝ) < 1) hq.1, hq.2⟩
  have hKIco : K ⊆ {x : Vec3 | 0 < x 2} ×ˢ Ico (1 / 2 : ℝ) 1 := by
    intro z hz
    exact ⟨(hKsub hz).1, (hKsub hz).2.1.le, (hKsub hz).2.2⟩
  have hweakv := bu_short_weak_derivatives scale hscale hscale1
    w Dw D2w Dtw hweak
  have hcontv := bu_short_field_continuousOn scale hscale hscale1 w hcont
  have hmeasv : AEStronglyMeasurable v (volume.restrict K) :=
    (hweakv.1.mono_set hKsub).aestronglyMeasurable
  have hcontK : ContinuousOn v K := hcontv.mono hKIco
  obtain ⟨C, hC⟩ := hKcompact.bddAbove_image hcontK.norm
  have hbound : ∀ᵐ z ∂(volume.restrict K), ‖v z‖ ≤ C := by
    filter_upwards [ae_restrict_mem hKmeas] with z hz
    exact hC (mem_image_of_mem (fun z => ‖v z‖) hz)
  have hfin : IsFiniteMeasure (volume.restrict K) :=
    CKN.isFiniteMeasure_restrict_of_isCompact hKcompact
  have hvLp : MemLp v 2 (volume.restrict K) :=
    @MemLp.of_bound ParabolicPoint Vec3 _ (2 : ℝ≥0∞)
      (volume.restrict K) _ hfin v hmeasv C hbound
  have hsum : (∫⁻ z in K,
      ‖Dv z‖ₑ ^ (2 : ℝ) + ‖D2v z‖ₑ ^ (2 : ℝ) +
        ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    bu_short_derivative_l2 scale hscale hscale1 w Dw D2w Dtw
      hweak hL2 K hKsub hKcompact.isBounded
  have hDlin : (∫⁻ z in K, ‖Dv z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt hsum
    exact le_add_of_nonneg_right (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity))
  have hD2lin : (∫⁻ z in K, ‖D2v z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt hsum
    exact le_add_of_nonneg_left (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity))
  have hDtlin : (∫⁻ z in K, ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt hsum
    exact le_add_of_nonneg_left (by positivity)
  have hDmeas : AEStronglyMeasurable Dv (volume.restrict K) :=
    (hweakv.2.1.mono_set hKsub).aestronglyMeasurable
  have hD2meas : AEStronglyMeasurable D2v (volume.restrict K) :=
    (hweakv.2.2.1.mono_set hKsub).aestronglyMeasurable
  have hDtmeas : AEStronglyMeasurable Dtv (volume.restrict K) :=
    (hweakv.2.2.2.1.mono_set hKsub).aestronglyMeasurable
  have hDLp : MemLp Dv 2 (volume.restrict K) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hDmeas).2
    simpa using hDlin
  have hD2Lp : MemLp D2v 2 (volume.restrict K) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hD2meas).2
    simpa using hD2lin
  have hDtLp : MemLp Dtv 2 (volume.restrict K) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hDtmeas).2
    simpa using hDtlin
  exact ⟨hvLp, hDLp, hD2Lp, hDtLp⟩

end ESS
