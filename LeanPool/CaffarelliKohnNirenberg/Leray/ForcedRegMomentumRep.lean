/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedConstruction

/-!
# The frequency representative of the forced regularized solution

On a bounded time interval the forced regularized solution of
`lem:regularised-forced` has a jointly measurable frequency representative
given by the Duhamel formula of `eq:reg-mild-forced`: its slices are the
transforms of complex fields whose real parts are the solution, the tensor
and force representatives are the transforms of the regularized tensor and of
the force, and all three are square integrable in frequency and time.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- A jointly measurable frequency representative of the forced mild curve. -/
theorem forcedMild_fourier_representation (b : RealVectorL2) (hb : RegularizedMildJData b)
    {F : ℝ → RealTensorL2} (hF : StronglyMeasurable F) {h : ℝ → RealVectorL2}
    (hh : StronglyMeasurable h) {T C : ℝ} (hC : 0 ≤ C)
    (hFC : ∀ s ∈ Ioc 0 T, ‖F s‖ ≤ C) (hH2 : IntegrableOn (fun s => ‖h s‖ ^ 2) (Ioc 0 T)) :
    ∃ (B : L2Vec3 → ComplexVec3) (Fh : L2Vec3 × ℝ → ComplexTensor3)
      (Hh : L2Vec3 × ℝ → ComplexVec3), Measurable B ∧ Measurable Fh ∧ Measurable Hh ∧
      Integrable (fun p => ‖forcedFourierRep B Fh Hh p‖ ^ 2)
        (volume.prod (volume.restrict (Ioc 0 T))) ∧
      Integrable (fun p => ‖Fh p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 T))) ∧
      Integrable (fun p => ‖Hh p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 T))) ∧
      (∀ s ∈ Ioc 0 T, (fun ξ => forcedFourierRep B Fh Hh (ξ, s)) =ᵐ[volume]
        (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (forcedComplexCurve b F h s) :
          L2Vec3 → ComplexVec3)) ∧
      (∀ s, (fun ξ => Fh (ξ, s)) =ᵐ[volume] (forcedFourierTensorCurve F s :
        L2Vec3 → ComplexTensor3)) ∧
      ∀ s, (fun ξ => Hh (ξ, s)) =ᵐ[volume] (forcedFourierForceCurve h s :
        L2Vec3 → ComplexVec3) := by
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
  have hH1 : IntegrableOn (fun s => ‖h s‖) (Ioc 0 T) := integrableOn_norm_of_sq hh hH2
  have hHc1 : IntegrableOn (fun s => ‖Hc s‖) (Ioc 0 T) :=
    Integrable.mono' hH1 (stronglyMeasurable_forcedFourierForceCurve hh).norm.aestronglyMeasurable
      (Eventually.of_forall fun s => by
        rw [norm_norm]; exact norm_forcedFourierForceCurve_le h s)
  have hFcC : ∀ s ∈ Ioc 0 T, ‖Fc s‖ ≤ C := fun s hs =>
    (norm_forcedFourierTensorCurve_le F s).trans (hFC s hs)
  have hbJ := ae_leraySymbol_fourier_of_mildJData b hb
  set Y := forcedFourierRep B Fh Hh with hYdef
  have hrepV : ∀ s ∈ Ioc 0 T, (fun ξ => Y (ξ, s)) =ᵐ[volume]
      (ℱV (forcedComplexCurve b F h s) : L2Vec3 → ComplexVec3) := by
    intro s hs
    rw [forcedComplexCurve_fourier b F h hs.1.le]
    exact (forcedFourierMild_ae_eq_rep bh hbJ hFh.measurable hrepF hHh.measurable hrepH hs.1.le
      (fun r hr => hFcC r ⟨hr.1, hr.2.trans hs.2⟩)
      (hHc1.mono_set (Ioc_subset_Ioc_right hs.2))).symm
  set K := ‖bh‖ + 2 * (C / Real.sqrt (2 * Real.exp 1)) * Real.sqrt T +
    ∫ s in Ioc 0 T, ‖Hc s‖ with hK
  have hWK : ∀ s ∈ Ioc 0 T, ‖ℱV (forcedComplexCurve b F h s)‖ ^ 2 ≤ K ^ 2 := by
    intro s hs
    rw [forcedComplexCurve_fourier b F h hs.1.le]
    have hn := norm_forcedFourierMild_le bh hs.1.le hs.2 hFcC hHc1 hC
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hYsm : StronglyMeasurable Y := stronglyMeasurable_forcedFourierRep hBm
    hFh.measurable hHh.measurable
  refine ⟨B, Fh, Hh, hBm, hFh.measurable, hHh.measurable, ?_, ?_, ?_, hrepV,
    fun s => hrepF s, fun s => hrepH s⟩
  · exact integrable_sq_jointRep_prod Y hYsm (fun s => ℱV (forcedComplexCurve b F h s)) hrepV
      (fun _ => K ^ 2) (integrableOn_const (by simp)) hWK
  · exact integrable_sq_jointRep_prod Fh hFh Fc (fun s _ => hrepF s) (fun _ => C ^ 2)
      (integrableOn_const (by simp)) (fun s hs =>
        pow_le_pow_left₀ (norm_nonneg _) (hFcC s hs) 2)
  · exact integrable_sq_jointRep_prod Hh hHh Hc (fun s _ => hrepH s) (fun s => ‖h s‖ ^ 2)
      hH2 (fun s _ => pow_le_pow_left₀ (norm_nonneg _) (norm_forcedFourierForceCurve_le h s) 2)

/-- The frequency representative of the forced regularized solution on
`(0, T]`. -/
theorem forcedReg_fourier_representation (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    {a : Vec3 → Vec3} (ha : CKN.IsInJ a) {f : ParabolicPoint → Vec3}
    (hf : CKN.IsLocallySquareIntegrableForce f) {T : ℝ} (hT : 0 ≤ T) :
    ∃ (B : L2Vec3 → ComplexVec3) (Fh : L2Vec3 × ℝ → ComplexTensor3)
      (Hh : L2Vec3 × ℝ → ComplexVec3), Measurable B ∧ Measurable Fh ∧ Measurable Hh ∧
      Integrable (fun p => ‖forcedFourierRep B Fh Hh p‖ ^ 2)
        (volume.prod (volume.restrict (Ioc 0 T))) ∧
      Integrable (fun p => ‖Fh p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 T))) ∧
      Integrable (fun p => ‖Hh p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 T))) ∧
      (∀ s ∈ Ioc 0 T, ∃ Z : ComplexVectorL2,
        realPartVectorL2 Z = forcedRegCurve ρ ε hε ha hf s ∧
        (fun ξ => forcedFourierRep B Fh Hh (ξ, s)) =ᵐ[volume]
          (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 Z : L2Vec3 → ComplexVec3)) ∧
      (∀ s ∈ Ioc 0 T, (fun ξ => Fh (ξ, s)) =ᵐ[volume]
        (Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3 (complexifyTensorL2
          (regularizedMildTensor ρ ε hε (forcedRegCurve ρ ε hε ha hf s))) :
            L2Vec3 → ComplexTensor3)) ∧
      ∀ s, (fun ξ => Hh (ξ, s)) =ᵐ[volume]
        (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (complexifyVectorL2
          (forcedForceSlice (forcedForceMod f hf) s)) : L2Vec3 → ComplexVec3) := by
  set b := forcedRegDatum ρ ε hε ha with hbdef
  have hb := forcedRegDatum_mildJData ρ ε hε ha
  set h := forcedForceSlice (forcedForceMod f hf) with hhdef
  have hh : StronglyMeasurable h :=
    forcedForceSlice_stronglyMeasurable (forcedForceMod_stronglyMeasurable f hf)
  have hH2 := integrableOn_forcedForceSlice_sq f hf
  set u := forcedSolutionOn ρ ε hε b hb hh hH2 T hT with hudef
  set F := regularizedMildClampedTensorTrajectory ρ ε hε T hT u with hFdef
  have hFc : Continuous F := regularizedMildClampedTensorTrajectory_continuous ρ ε hε T hT u
  obtain ⟨C, hCb⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hFc.norm.continuousOn
  have hFC : ∀ s ∈ Ioc 0 T, ‖F s‖ ≤ C := fun s hs => by
    have := hCb s (Ioc_subset_Icc_self hs)
    rwa [norm_norm] at this
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hCb 0 ⟨le_rfl, hT⟩)
  obtain ⟨B, Fh, Hh, hBm, hFhm, hHhm, hY2, hF2, hHh2, hrepY, hrepF, hrepH⟩ :=
    forcedMild_fourier_representation b hb hFc.stronglyMeasurable hh hC0 hFC (hH2 T)
  have hU : ∀ s (hs : s ∈ Ioc 0 T), forcedRegCurve ρ ε hε ha hf s = u ⟨s, hs.1.le, hs.2⟩ :=
    fun s hs =>
    forcedSolutionCurve_eq ρ ε hε b hb hh hH2 hT ⟨hs.1.le, hs.2⟩
  have hFs : ∀ s ∈ Ioc 0 T, F s = regularizedMildTensor ρ ε hε (forcedRegCurve ρ ε hε ha hf s) :=
    fun s hs => by
      rw [hU s hs, hFdef]
      simp only [regularizedMildClampedTensorTrajectory,
        regularizedMildTimeClamp_eq_of_mem T hT ⟨hs.1.le, hs.2⟩]
  refine ⟨B, Fh, Hh, hBm, hFhm, hHhm, hY2, hF2, hHh2, fun s hs => ?_, fun s hs => ?_,
    fun s => hrepH s⟩
  · refine ⟨forcedComplexCurve b F h s, ?_, hrepY s hs⟩
    rw [← forcedMildCurve_eq_realPart b hFc.stronglyMeasurable hh hs.1.le
      (fun r hr => hFC r ⟨hr.1, hr.2.trans hs.2⟩)
      ((integrableOn_norm_of_sq hh (hH2 T)).mono_set (Ioc_subset_Ioc_right hs.2)), hU s hs]
    unfold forcedMildCurve
    rw [dite_eq_left hs.1.le]
    exact ((forcedSolutionOn_spec ρ ε hε b hb hh hH2 T hT).1 ⟨s, hs.1.le, hs.2⟩).symm
  · have h1 := hrepF s
    rw [forcedFourierTensorCurve, hFs s hs] at h1
    exact h1

end CKN.Leray

end
