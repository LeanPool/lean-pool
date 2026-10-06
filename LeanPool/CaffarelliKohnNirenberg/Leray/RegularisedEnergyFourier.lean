/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedMildEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedRealFourierCutoff

/-!
# Exact energy balance for divergence-free mild data

The Fourier energy identity loses no initial energy when the datum already
lies in the range of the Leray projection.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- The forced mild equation has an exact energy balance when its initial field
lies in the divergence-free subspace. -/
theorem forcedMild_energy_balance_eq (b : RealVectorL2) (hb : RegularizedMildJData b)
    {F : ℝ → RealTensorL2} (hF : StronglyMeasurable F) {h : ℝ → RealVectorL2}
    (hh : StronglyMeasurable h) {T C : ℝ} (hC : 0 ≤ C) (hFC : ∀ s ∈ Ioc 0 T, ‖F s‖ ≤ C)
    (hH2 : IntegrableOn (fun s => ‖h s‖ ^ 2) (Ioc 0 T)) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    (∀ᵐ s ∂(volume.restrict (Ioc 0 t)), Integrable (fun ξ => forcedFourierLam ξ *
      ‖(Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (forcedComplexCurve b F h s) :
        L2Vec3 → ComplexVec3) ξ‖ ^ 2)) ∧
    IntegrableOn (fun s => forcedFourierDissipation (forcedComplexCurve b F h s)) (Ioc 0 t) ∧
    ‖forcedComplexCurve b F h t‖ ^ 2 +
        2 * ∫ s in Ioc 0 t, forcedFourierDissipation (forcedComplexCurve b F h s) =
      ‖b‖ ^ 2 + 2 * (∫ s in Ioc 0 t,
          forcedStokesPairing (forcedComplexCurve b F h s) (complexifyTensorL2 (F s))) +
        2 * ∫ s in Ioc 0 t, inner ℝ (forcedMildCurve b h F s) (h s) := by
  set ℱV := Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 with hℱV
  set bh := ℱV (complexifyVectorL2 b) with hbh
  set Fc := forcedFourierTensorCurve F with hFc
  set Hc := forcedFourierForceCurve h with hHc
  obtain ⟨Fh, hFh, hrepF⟩ := exists_jointRep_of_stronglyMeasurable (μ := volume) Fc
    (stronglyMeasurable_forcedFourierTensorCurve hF)
  obtain ⟨Hh, hHh, hrepH⟩ := exists_jointRep_of_stronglyMeasurable (μ := volume) Hc
    (stronglyMeasurable_forcedFourierForceCurve hh)
  set B : L2Vec3 → ComplexVec3 := fun η => leraySymbol η ((bh : L2Vec3 → ComplexVec3) η)
    with hBdef
  have hBm : Measurable B := by
    have h1 : Measurable fun η : L2Vec3 => (η, (bh : L2Vec3 → ComplexVec3) η) :=
      measurable_id.prodMk (Lp.stronglyMeasurable bh).measurable
    have h2 := measurable_leraySymbol_uncurry.comp h1
    exact h2
  have hBP : ∀ ξ, leraySymbol ξ (B ξ) = B ξ := fun ξ =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _)
  have hbsq : Integrable (fun ξ => ‖(bh : L2Vec3 → ComplexVec3) ξ‖ ^ 2) :=
    (Lp.memLp bh).integrable_norm_pow two_ne_zero
  have hBsq : Integrable (fun ξ => ‖B ξ‖ ^ 2) := by
    refine Integrable.mono' hbsq (hBm.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (leraySymbol_norm_le ξ _) 2
  have hH1 : IntegrableOn (fun s => ‖h s‖) (Ioc 0 T) := integrableOn_norm_of_sq hh hH2
  have hHc1 : IntegrableOn (fun s => ‖Hc s‖) (Ioc 0 T) :=
    Integrable.mono' hH1 (stronglyMeasurable_forcedFourierForceCurve hh).norm.aestronglyMeasurable
      (Eventually.of_forall fun s => by
        rw [norm_norm]; exact norm_forcedFourierForceCurve_le h s)
  have hFcC : ∀ s ∈ Ioc 0 T, ‖Fc s‖ ≤ C := fun s hs =>
    (norm_forcedFourierTensorCurve_le F s).trans (hFC s hs)
  have hbJ := ae_leraySymbol_fourier_of_mildJData b hb
  set Y := forcedFourierRep B Fh Hh with hYdef
  have hrepW : ∀ s (hs : 0 ≤ s), s ≤ T →
      (forcedFourierMild bh Fc Hc s hs : L2Vec3 → ComplexVec3) =ᵐ[volume]
        fun ξ => Y (ξ, s) := fun s hs hsT =>
    forcedFourierMild_ae_eq_rep bh hbJ hFh.measurable hrepF hHh.measurable hrepH hs
      (fun r hr => hFcC r ⟨hr.1, hr.2.trans hsT⟩)
      (hHc1.mono_set (Ioc_subset_Ioc_right hsT))
  have hvW : ∀ s (hs : 0 ≤ s), ℱV (forcedComplexCurve b F h s) =
      forcedFourierMild bh Fc Hc s hs := fun s hs => forcedComplexCurve_fourier b F h hs
  have hrepV : ∀ s ∈ Ioc 0 t, (fun ξ => Y (ξ, s)) =ᵐ[volume]
      (ℱV (forcedComplexCurve b F h s) : L2Vec3 → ComplexVec3) := by
    intro s hs
    rw [hvW s hs.1.le]
    exact (hrepW s hs.1.le (hs.2.trans htT)).symm
  set K := ‖bh‖ + 2 * (C / Real.sqrt (2 * Real.exp 1)) * Real.sqrt T +
    ∫ s in Ioc 0 T, ‖Hc s‖ with hK
  have hWK : ∀ s ∈ Ioc 0 t, ‖ℱV (forcedComplexCurve b F h s)‖ ^ 2 ≤ K ^ 2 := by
    intro s hs
    rw [hvW s hs.1.le]
    have hn := norm_forcedFourierMild_le bh hs.1.le (hs.2.trans htT) hFcC hHc1 hC
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hYsm : StronglyMeasurable Y := stronglyMeasurable_forcedFourierRep hBm
    hFh.measurable hHh.measurable
  have hYint : Integrable (fun p => ‖Y p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 t))) :=
    integrable_sq_jointRep_prod Y hYsm (fun s => ℱV (forcedComplexCurve b F h s)) hrepV
      (fun _ => K ^ 2) (integrableOn_const (by simp) ) hWK
  have hFint : Integrable (fun p => ‖Fh p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 t))) :=
    integrable_sq_jointRep_prod Fh hFh Fc (fun s _ => hrepF s) (fun _ => C ^ 2)
      (integrableOn_const (by simp)) (fun s hs =>
        pow_le_pow_left₀ (norm_nonneg _) (hFcC s ⟨hs.1, hs.2.trans htT⟩) 2)
  have hHint : Integrable (fun p => ‖Hh p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 t))) :=
    integrable_sq_jointRep_prod Hh hHh Hc (fun s _ => hrepH s) (fun s => ‖h s‖ ^ 2)
      (hH2.mono_set (Ioc_subset_Ioc_right htT)) (fun s _ =>
        pow_le_pow_left₀ (norm_nonneg _) (norm_forcedFourierForceCurve_le h s) 2)
  have hYt : Integrable (fun ξ => ‖Y (ξ, t)‖ ^ 2) := by
    refine ((Lp.memLp (forcedFourierMild bh Fc Hc t ht)).integrable_norm_pow two_ne_zero).congr ?_
    filter_upwards [hrepW t ht htT] with ξ hξ
    rw [hξ]
  obtain ⟨hlam, hid⟩ := forcedFourierRep_energy_identity hBm hBsq hFh.measurable hHh.measurable
    hBP ht hFint hHint hYint hYt
  have hA : ∫ ξ, ‖Y (ξ, t)‖ ^ 2 = ‖forcedComplexCurve b F h t‖ ^ 2 := by
    rw [← LinearIsometryEquiv.norm_map ℱV, ← integral_norm_sq_eq_norm_sq_Lp]
    refine integral_congr_ae ?_
    filter_upwards [hrepW t ht htT] with ξ hξ
    rw [hvW t ht, hξ]
  have hD : ∫ ξ, forcedFourierLam ξ * ∫ s in Ioc 0 t, ‖Y (ξ, s)‖ ^ 2 =
      ∫ s in Ioc 0 t, forcedFourierDissipation (forcedComplexCurve b F h s) := by
    have h1 : ∫ ξ, forcedFourierLam ξ * ∫ s in Ioc 0 t, ‖Y (ξ, s)‖ ^ 2 =
        ∫ ξ, ∫ s in Ioc 0 t, forcedFourierLam ξ * ‖Y (ξ, s)‖ ^ 2 := by
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      exact (integral_const_mul _ _).symm
    rw [h1, integral_integral_swap (f := fun ξ s => forcedFourierLam ξ * ‖Y (ξ, s)‖ ^ 2) hlam]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    unfold forcedFourierDissipation
    refine integral_congr_ae ?_
    filter_upwards [hrepV s hs] with ξ hξ
    rw [hξ]
  have hBle : ∫ ξ, ‖B ξ‖ ^ 2 = ‖b‖ ^ 2 := by
    have hBae : ∀ᵐ ξ ∂volume, ‖B ξ‖ = ‖(bh : L2Vec3 → ComplexVec3) ξ‖ := by
      filter_upwards [hbJ] with ξ hξ
      change ‖leraySymbol ξ ((bh : L2Vec3 → ComplexVec3) ξ)‖ =
        ‖(bh : L2Vec3 → ComplexVec3) ξ‖
      have hξ' : leraySymbol ξ ((bh : L2Vec3 → ComplexVec3) ξ) =
          (bh : L2Vec3 → ComplexVec3) ξ := by
        simpa [bh] using hξ
      rw [hξ']
    calc
      ∫ ξ, ‖B ξ‖ ^ 2 = ∫ ξ, ‖(bh : L2Vec3 → ComplexVec3) ξ‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hBae] with ξ hξ
        rw [hξ]
      _ = ‖bh‖ ^ 2 := integral_norm_sq_eq_norm_sq_Lp bh
      _ = ‖complexifyVectorL2 b‖ ^ 2 := by
        rw [hbh, LinearIsometryEquiv.norm_map]
      _ = ‖b‖ ^ 2 := by
        have hnorm : ‖complexifyVectorL2 b‖ = ‖b‖ := by
          apply le_antisymm (complexifyVectorL2_norm_le b)
          calc
            ‖b‖ = ‖realPartVectorL2 (complexifyVectorL2 b)‖ := by
              rw [realPartVectorL2_complexifyVectorL2]
            _ ≤ ‖complexifyVectorL2 b‖ := realPartVectorL2_norm_le _
        rw [hnorm]
  have hS : ∫ s in Ioc 0 t, ∫ ξ, (inner ℂ (Y (ξ, s))
      (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ (Fh (ξ, s))))).re =
      ∫ s in Ioc 0 t, forcedStokesPairing (forcedComplexCurve b F h s)
        (complexifyTensorL2 (F s)) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    unfold forcedStokesPairing
    refine integral_congr_ae ?_
    filter_upwards [hrepV s hs, hrepF s] with ξ hξ hξ'
    rw [hξ, hξ']
    rfl
  have hHt : ∫ s in Ioc 0 t, ∫ ξ, (inner ℂ (Y (ξ, s)) (Hh (ξ, s))).re =
      ∫ s in Ioc 0 t, inner ℝ (forcedMildCurve b h F s) (h s) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [forcedMildCurve_eq_realPart b hF hh hs.1.le
      (fun r hr => hFC r ⟨hr.1, hr.2.trans (hs.2.trans htT)⟩)
      (hH1.mono_set (Ioc_subset_Ioc_right (hs.2.trans htT))), inner_realPartVectorL2_eq_re,
      ← LinearIsometryEquiv.inner_map_map ℱV, L2.inner_def,
      ← RCLike.re_to_complex, ← integral_re (L2.integrable_inner _ _)]
    refine integral_congr_ae ?_
    filter_upwards [hrepV s hs, hrepH s] with ξ hξ hξ'
    rw [hξ, hξ']
    rfl
  rw [hA, hD, hS, hHt] at hid
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hlam.prod_left_ae, ae_restrict_mem measurableSet_Ioc] with s hsint hs
    refine hsint.congr ?_
    filter_upwards [hrepV s hs] with ξ hξ
    rw [← hYdef, hξ]
  · refine hlam.integral_prod_right.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    unfold forcedFourierDissipation
    refine integral_congr_ae ?_
    filter_upwards [hrepV s hs] with ξ hξ
    rw [← hYdef, hξ]
  · rw [hBle] at hid
    exact hid


end CKN.Leray

end
