/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedMildEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierPhysicalRange

/-!
# The forced mild solution is divergence free

The frequency representative of `eq:reg-mild-forced` lies in the range of the
Leray symbol at almost every frequency, so its transform is orthogonal to the
frequency and the real part of the solution is weakly divergence free at
every time, as asserted in `lem:regularised-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- At a frequency where the source is integrable, the representative lies in
the range of the Leray symbol. -/
theorem leraySymbol_forcedFourierRep {B : L2Vec3 → ComplexVec3}
    {Fh : L2Vec3 × ℝ → ComplexTensor3} {Hh : L2Vec3 × ℝ → ComplexVec3}
    (hFh : Measurable Fh) (hHh : Measurable Hh)
    (hBP : ∀ ξ, leraySymbol ξ (B ξ) = B ξ) (ξ : L2Vec3) {s : ℝ}
    (hgint : IntegrableOn (fun r => forcedFourierSource Fh Hh (ξ, r)) (Ioc 0 s)) :
    leraySymbol ξ (forcedFourierRep B Fh Hh (ξ, s)) = forcedFourierRep B Fh Hh (ξ, s) := by
  let P := leraySymbol ξ
  have hsrcmeas : Measurable fun r => forcedFourierSource Fh Hh (ξ, r) :=
    (measurable_forcedFourierSource hFh hHh).comp (measurable_const.prodMk measurable_id)
  have hk : IntegrableOn (fun r => heatSymbol (s - r) ξ •
      leraySymbol ξ (forcedFourierSource Fh Hh (ξ, r))) (Ioc 0 s) := by
    refine Integrable.mono' ((P.integrable_comp hgint).norm) ?_ ?_
    · refine (Measurable.aestronglyMeasurable ?_)
      have h1 : Measurable fun r : ℝ => heatSymbol (s - r) ξ := by fun_prop [heatSymbol]
      have h2 : Measurable fun r => leraySymbol ξ (forcedFourierSource Fh Hh (ξ, r)) :=
        P.continuous.measurable.comp hsrcmeas
      have h3 := continuous_smul.measurable.comp (h1.prodMk h2)
      exact h3
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (heatSymbol_norm_le_one (sub_nonneg.2 hr.2) ξ)
  simp only [forcedFourierRep]
  rw [map_add, map_smul, hBP ξ, ← P.integral_comp_comm hk]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only [map_smul]
  congr 1
  exact Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _)

/-- The transform of the complex solution is orthogonal to the frequency. -/
theorem forcedComplexCurve_fourierOrthogonal (b : RealVectorL2) (hb : RegularizedMildJData b)
    {F : ℝ → RealTensorL2} (hF : StronglyMeasurable F) {h : ℝ → RealVectorL2}
    (hh : StronglyMeasurable h) {T C : ℝ} (hFC : ∀ s ∈ Ioc 0 T, ‖F s‖ ≤ C)
    (hH2 : IntegrableOn (fun s => ‖h s‖ ^ 2) (Ioc 0 T)) {s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    ∀ᵐ ξ ∂volume, inner ℂ (complexifyFrequency ξ)
      ((Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (forcedComplexCurve b F h s) :
        L2Vec3 → ComplexVec3) ξ) = 0 := by
  set bh := Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (complexifyVectorL2 b) with hbh
  set Fc := forcedFourierTensorCurve F with hFc
  set Hc := forcedFourierForceCurve h with hHc
  obtain ⟨Fh, hFh, hrepF⟩ := exists_jointRep_of_stronglyMeasurable (μ := volume) Fc
    (stronglyMeasurable_forcedFourierTensorCurve hF)
  obtain ⟨Hh, hHh, hrepH⟩ := exists_jointRep_of_stronglyMeasurable (μ := volume) Hc
    (stronglyMeasurable_forcedFourierForceCurve hh)
  set B : L2Vec3 → ComplexVec3 := fun η => leraySymbol η ((bh : L2Vec3 → ComplexVec3) η)
  have hBP : ∀ ξ, leraySymbol ξ (B ξ) = B ξ := fun ξ =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _)
  have hH1 : IntegrableOn (fun s => ‖h s‖) (Ioc 0 T) := integrableOn_norm_of_sq hh hH2
  have hHc1 : IntegrableOn (fun s => ‖Hc s‖) (Ioc 0 T) :=
    Integrable.mono' hH1 (stronglyMeasurable_forcedFourierForceCurve hh).norm.aestronglyMeasurable
      (Eventually.of_forall fun s => by
        rw [norm_norm]; exact norm_forcedFourierForceCurve_le h s)
  have hFcC : ∀ r ∈ Ioc 0 T, ‖Fc r‖ ≤ C := fun r hr =>
    (norm_forcedFourierTensorCurve_le F r).trans (hFC r hr)
  have hrepW := forcedFourierMild_ae_eq_rep bh (ae_leraySymbol_fourier_of_mildJData b hb)
    hFh.measurable hrepF hHh.measurable hrepH hs
    (fun r hr => hFcC r ⟨hr.1, hr.2.trans hsT⟩) (hHc1.mono_set (Ioc_subset_Ioc_right hsT))
  have hFint : Integrable (fun p => ‖Fh p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 s))) :=
    integrable_sq_jointRep_prod Fh hFh Fc (fun r _ => hrepF r) (fun _ => C ^ 2)
      (integrableOn_const (by simp)) (fun r hr =>
        pow_le_pow_left₀ (norm_nonneg _) (hFcC r ⟨hr.1, hr.2.trans hsT⟩) 2)
  have hHint : Integrable (fun p => ‖Hh p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 s))) :=
    integrable_sq_jointRep_prod Hh hHh Hc (fun r _ => hrepH r) (fun r => ‖h r‖ ^ 2)
      (hH2.mono_set (Ioc_subset_Ioc_right hsT)) (fun r _ =>
        pow_le_pow_left₀ (norm_nonneg _) (norm_forcedFourierForceCurve_le h r) 2)
  have hμ : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) s)) := by
    refine ⟨?_⟩
    simp only [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hslice : ∀ {E : Type} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
      [SecondCountableTopology E] {f : L2Vec3 × ℝ → E}, Measurable f → ∀ ξ,
      Integrable (fun r => ‖f (ξ, r)‖ ^ 2) (volume.restrict (Ioc 0 s)) →
      Integrable (fun r => ‖f (ξ, r)‖) (volume.restrict (Ioc 0 s)) := by
    intro E _ _ _ _ f hf ξ hsq
    have hmeas : AEStronglyMeasurable (fun r => f (ξ, r)) (volume.restrict (Ioc 0 s)) :=
      (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact (((memLp_two_iff_integrable_sq_norm hmeas).2 hsq).integrable one_le_two).norm
  rw [forcedComplexCurve_fourier b F h hs]
  filter_upwards [hrepW, hFint.prod_right_ae, hHint.prod_right_ae] with ξ hξ hF2 hH2'
  have hF1 := hslice hFh.measurable ξ hF2
  have hH1' := hslice hHh.measurable ξ hH2'
  have hsrc : IntegrableOn (fun r => forcedFourierSource Fh Hh (ξ, r)) (Ioc 0 s) := by
    refine Integrable.mono' ((hF1.const_mul (2 * Real.pi * ‖ξ‖)).add hH1') ?_ ?_
    · exact ((measurable_forcedFourierSource hFh.measurable hHh.measurable).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · refine Eventually.of_forall fun r => ?_
      simp only [forcedFourierSource]
      exact (norm_add_le _ _).trans (add_le_add
        (norm_tensorDivergence_source_le ξ (Fh (ξ, r))) le_rfl)
  rw [hξ, ← leraySymbol_forcedFourierRep hFh.measurable hHh.measurable hBP ξ hsrc]
  exact leraySymbol_divergence_free ξ _

/-- The forced mild solution takes values in the divergence-free space `J`. -/
theorem forcedMildCurve_mildJData (b : RealVectorL2) (hb : RegularizedMildJData b)
    {F : ℝ → RealTensorL2} (hF : StronglyMeasurable F) {h : ℝ → RealVectorL2}
    (hh : StronglyMeasurable h) {T C : ℝ} (hFC : ∀ s ∈ Ioc 0 T, ‖F s‖ ≤ C)
    (hH2 : IntegrableOn (fun s => ‖h s‖ ^ 2) (Ioc 0 T)) {s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    RegularizedMildJData (forcedMildCurve b h F s) := by
  have horth := forcedComplexCurve_fourierOrthogonal b hb hF hh hFC hH2 hs hsT
  have hweak := realPart_isWeakDivFree_of_fourierOrthogonal _ horth
  rw [forcedMildCurve_eq_realPart b hF hh hs (fun r hr => hFC r ⟨hr.1, hr.2.trans hsT⟩)
    ((integrableOn_norm_of_sq hh hH2).mono_set (Ioc_subset_Ioc_right hsT))]
  exact CKN.isInJ_iff_weakDivFree.2
    (isWeakDivFree_congr_ae (realPartVectorL2Representative_eq_ae _).symm hweak)

end CKN.Leray

end
