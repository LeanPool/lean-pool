/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedFourierEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedMeasurableCurve
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierRealification

/-!
# The forced mild equation in frequency variables

The right-hand side of `eq:reg-mild-forced` is transformed to frequency
variables: the heat evolution of the datum, the Stokes Duhamel integral of
the tensor, and the heat Duhamel integral of the projected force. The Bochner
integral in frequency `L²` is identified almost everywhere with the pointwise
representative `forcedFourierRep` of `lem:regularised-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- The frequency-side Stokes Duhamel integrand, zero at and after the
evaluation time. -/
@[expose]
def forcedFourierStokesIntegrand (F : ℝ → ComplexTensorL2) (t s : ℝ) : ComplexVectorL2 :=
  if hs : s < t then stokesFourierMultiplier (sub_pos.2 hs) (F s) else 0

/-- The frequency-side force Duhamel integrand: the heat multiplier applied to
the Leray projection of the transformed force. -/
@[expose]
def forcedFourierForceIntegrand (H : ℝ → ComplexVectorL2) (t s : ℝ) : ComplexVectorL2 :=
  if hs : s ≤ t then heatMultiplier (t - s) (sub_nonneg.2 hs) • lerayFourierMultiplier (H s)
  else 0

/-- The frequency-side right-hand side of `eq:reg-mild-forced`. -/
@[expose]
def forcedFourierMild (b : ComplexVectorL2) (F : ℝ → ComplexTensorL2)
    (H : ℝ → ComplexVectorL2) (t : ℝ) (ht : 0 ≤ t) : ComplexVectorL2 :=
  heatMultiplier t ht • b +
    ∫ s in Ioc 0 t, (-forcedFourierStokesIntegrand F t s + forcedFourierForceIntegrand H t s)

/-- The Stokes formula is jointly measurable in time, frequency and tensor. -/
theorem measurable_stokesApplyFormula_uncurry :
    Measurable fun p : ℝ × L2Vec3 × ComplexTensor3 => stokesApplyFormula p.1 p.2.1 p.2.2 := by
  have hdiv : Measurable fun p : ℝ × L2Vec3 × ComplexTensor3 =>
      tensorDivergenceLinear p.2.1 p.2.2 := by
    change Measurable (fun p : ℝ × L2Vec3 × ComplexTensor3 =>
      ∑ i : Fin 3, (p.2.1 i : ℂ) • p.2.2 i)
    fun_prop
  have hpair : Measurable fun p : ℝ × L2Vec3 × ComplexTensor3 =>
      (p.2.1, tensorDivergenceLinear p.2.1 p.2.2) := by
    have h := (measurable_fst.comp measurable_snd).prodMk hdiv
    exact h
  have hproj : Measurable fun p : ℝ × L2Vec3 × ComplexTensor3 =>
      lerayApplyFormula p.2.1 (tensorDivergenceLinear p.2.1 p.2.2) := by
    have h := lerayApplyFormula_measurable.comp hpair
    exact h
  have hheat : Measurable fun p : ℝ × L2Vec3 × ComplexTensor3 =>
      heatSymbol p.1 p.2.1 * (2 * Real.pi * Complex.I : ℂ) := by
    fun_prop [heatSymbol]
  change Measurable (fun p : ℝ × L2Vec3 × ComplexTensor3 =>
    (heatSymbol p.1 p.2.1 * (2 * Real.pi * Complex.I : ℂ)) •
      lerayApplyFormula p.2.1 (tensorDivergenceLinear p.2.1 p.2.2))
  have h := continuous_smul.measurable.comp (hheat.prodMk hproj)
  exact h

/-- The joint representative of the Stokes Duhamel integrand. -/
@[expose]
def forcedFourierStokesRep (Fh : L2Vec3 × ℝ → ComplexTensor3) (t : ℝ)
    (p : L2Vec3 × ℝ) : ComplexVec3 :=
  if p.2 < t then stokesApplyFormula (t - p.2) p.1 (Fh p) else 0

/-- The joint representative of the force Duhamel integrand. -/
@[expose]
def forcedFourierForceRep (Hh : L2Vec3 × ℝ → ComplexVec3) (t : ℝ)
    (p : L2Vec3 × ℝ) : ComplexVec3 :=
  if p.2 ≤ t then heatSymbol (t - p.2) p.1 • lerayApplyFormula p.1 (Hh p) else 0

theorem measurable_forcedFourierStokesRep {Fh : L2Vec3 × ℝ → ComplexTensor3}
    (hFh : Measurable Fh) (t : ℝ) : Measurable (forcedFourierStokesRep Fh t) := by
  unfold forcedFourierStokesRep
  refine Measurable.ite (measurableSet_lt measurable_snd measurable_const) ?_ measurable_const
  have hq : Measurable fun p : L2Vec3 × ℝ => (t - p.2, p.1, Fh p) :=
    (measurable_const.sub measurable_snd).prodMk (measurable_fst.prodMk hFh)
  have h := measurable_stokesApplyFormula_uncurry.comp hq
  exact h

theorem measurable_forcedFourierForceRep {Hh : L2Vec3 × ℝ → ComplexVec3}
    (hHh : Measurable Hh) (t : ℝ) : Measurable (forcedFourierForceRep Hh t) := by
  unfold forcedFourierForceRep
  refine Measurable.ite (measurableSet_le measurable_snd measurable_const) ?_ measurable_const
  have hheat : Measurable fun p : L2Vec3 × ℝ => heatSymbol (t - p.2) p.1 := by
    fun_prop [heatSymbol]
  have hler : Measurable fun p : L2Vec3 × ℝ => lerayApplyFormula p.1 (Hh p) := by
    have h := lerayApplyFormula_measurable.comp (measurable_fst.prodMk hHh)
    exact h
  have h := continuous_smul.measurable.comp (hheat.prodMk hler)
  exact h

/-- Every slice of the Stokes representative represents the Stokes integrand. -/
theorem forcedFourierStokesRep_slice {F : ℝ → ComplexTensorL2}
    {Fh : L2Vec3 × ℝ → ComplexTensor3} (hrep : ∀ s, (fun ξ => Fh (ξ, s)) =ᵐ[volume] F s)
    (t s : ℝ) :
    (fun ξ => forcedFourierStokesRep Fh t (ξ, s)) =ᵐ[volume]
      forcedFourierStokesIntegrand F t s := by
  by_cases hs : s < t
  · simp only [forcedFourierStokesRep, forcedFourierStokesIntegrand, hs, ↓reduceIte,
      ↓reduceDIte]
    have hmult := measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula (t - s) p.1 p.2)
      (stokesApplyFormula_measurable (t - s))
      (1 / Real.sqrt (2 * Real.exp 1 * (t - s)))
      (by intro ξ T; exact stokesApplyFormula_norm_le (sub_pos.2 hs) ξ T) (F s)
    filter_upwards [hmult, hrep s] with ξ hξ hξ'
    change stokesApplyFormula (t - s) ξ (Fh (ξ, s)) =
      measurableFourierMultiplier
        (fun p : L2Vec3 × ComplexTensor3 => stokesApplyFormula (t - s) p.1 p.2)
        (stokesApplyFormula_measurable (t - s))
        (1 / Real.sqrt (2 * Real.exp 1 * (t - s)))
        (by intro η T; exact stokesApplyFormula_norm_le (sub_pos.2 hs) η T) (F s) ξ
    rw [hξ, hξ']
  · simp only [forcedFourierStokesRep, forcedFourierStokesIntegrand, hs, ↓reduceIte,
      ↓reduceDIte]
    exact (Lp.coeFn_zero _ _ _).symm

/-- Every slice of the force representative represents the force integrand. -/
theorem forcedFourierForceRep_slice {H : ℝ → ComplexVectorL2}
    {Hh : L2Vec3 × ℝ → ComplexVec3} (hrep : ∀ s, (fun ξ => Hh (ξ, s)) =ᵐ[volume] H s)
    (t s : ℝ) :
    (fun ξ => forcedFourierForceRep Hh t (ξ, s)) =ᵐ[volume]
      forcedFourierForceIntegrand H t s := by
  by_cases hs : s ≤ t
  · simp only [forcedFourierForceRep, forcedFourierForceIntegrand, hs, ↓reduceIte,
      ↓reduceDIte]
    have hsmul := Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (heatMultiplier (t - s) (sub_nonneg.2 hs)) (lerayFourierMultiplier (H s))
    have hheat : (heatMultiplier (t - s) (sub_nonneg.2 hs) : L2Vec3 → ℂ) =ᵐ[volume]
        heatSymbol (t - s) := by
      unfold heatMultiplier
      exact MemLp.coeFn_toLp _
    have hler := measurableFourierMultiplier_ae_eq
      (m := fun p : L2Vec3 × ComplexVec3 => lerayApplyFormula p.1 p.2)
      lerayApplyFormula_measurable 1
      (by
        intro ξ z
        rw [← leraySymbol_apply_eq_formula]
        simpa using leraySymbol_norm_le ξ z) (H s)
    filter_upwards [hsmul, hheat, hler, hrep s] with ξ h1 h2 h3 h4
    rw [h1, Pi.smul_apply', h2]
    change heatSymbol (t - s) ξ • lerayApplyFormula ξ (Hh (ξ, s)) =
      heatSymbol (t - s) ξ • lerayFourierMultiplier (H s) ξ
    unfold lerayFourierMultiplier
    rw [h3, h4]
  · simp only [forcedFourierForceRep, forcedFourierForceIntegrand, hs, ↓reduceIte,
      ↓reduceDIte]
    exact (Lp.coeFn_zero _ _ _).symm

/-- The Abel kernel `(t - s)^{-1/2}` is integrable on `(0, t]`. -/
theorem integrableOn_abelKernel (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => (t - s) ^ (-(1 / 2 : ℝ))) (Ioc 0 t) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := t) (b := 0)
    (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_left t
  simp only [sub_self, sub_zero] at h
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 h

theorem stokes_kernel_eq_rpow {τ : ℝ} (hτ : 0 < τ) :
    1 / Real.sqrt (2 * Real.exp 1 * τ) =
      1 / Real.sqrt (2 * Real.exp 1) * τ ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_mul (by positivity), Real.rpow_neg hτ.le, ← Real.sqrt_eq_rpow]
  field_simp

/-- The Stokes Duhamel integrand of a bounded tensor curve is integrable. -/
theorem integrableOn_forcedFourierStokesIntegrand {F : ℝ → ComplexTensorL2}
    {Fh : L2Vec3 × ℝ → ComplexTensor3} (hFh : Measurable Fh)
    (hrep : ∀ s, (fun ξ => Fh (ξ, s)) =ᵐ[volume] F s) {t C : ℝ} (ht : 0 ≤ t)
    (hFC : ∀ s ∈ Ioc 0 t, ‖F s‖ ≤ C) :
    IntegrableOn (forcedFourierStokesIntegrand F t) (Ioc 0 t) := by
  have hmeas : StronglyMeasurable (forcedFourierStokesIntegrand F t) :=
    stronglyMeasurable_of_jointRep (forcedFourierStokesRep Fh t)
      (measurable_forcedFourierStokesRep hFh t).stronglyMeasurable _
      (forcedFourierStokesRep_slice hrep t)
  refine Integrable.mono' ((integrableOn_abelKernel t ht).const_mul
      (C / Real.sqrt (2 * Real.exp 1))) hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  unfold forcedFourierStokesIntegrand
  by_cases hst : s < t
  · rw [dite_eq_left hst]
    refine (stokesFourierMultiplier_norm_le (sub_pos.2 hst) _).trans ?_
    rw [stokes_kernel_eq_rpow (sub_pos.2 hst)]
    have hk : 0 ≤ (t - s) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (sub_pos.2 hst).le _
    calc 1 / Real.sqrt (2 * Real.exp 1) * (t - s) ^ (-(1 / 2 : ℝ)) * ‖F s‖
        ≤ 1 / Real.sqrt (2 * Real.exp 1) * (t - s) ^ (-(1 / 2 : ℝ)) * C := by
          gcongr
          exact hFC s hs
      _ = C / Real.sqrt (2 * Real.exp 1) * (t - s) ^ (-(1 / 2 : ℝ)) := by ring
  · rw [dite_eq_right hst, norm_zero]
    have hst' : s = t := le_antisymm hs.2 (not_lt.1 hst)
    rw [hst', sub_self, Real.zero_rpow (by norm_num), mul_zero]

/-- The force Duhamel integrand of an integrable force curve is integrable. -/
theorem integrableOn_forcedFourierForceIntegrand {H : ℝ → ComplexVectorL2}
    {Hh : L2Vec3 × ℝ → ComplexVec3} (hHh : Measurable Hh)
    (hrep : ∀ s, (fun ξ => Hh (ξ, s)) =ᵐ[volume] H s) {t : ℝ}
    (hH : IntegrableOn (fun s => ‖H s‖) (Ioc 0 t)) :
    IntegrableOn (forcedFourierForceIntegrand H t) (Ioc 0 t) := by
  have hmeas : StronglyMeasurable (forcedFourierForceIntegrand H t) :=
    stronglyMeasurable_of_jointRep (forcedFourierForceRep Hh t)
      (measurable_forcedFourierForceRep hHh t).stronglyMeasurable _
      (forcedFourierForceRep_slice hrep t)
  refine Integrable.mono' hH hmeas.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
  unfold forcedFourierForceIntegrand
  by_cases hst : s ≤ t
  · rw [dite_eq_left hst]
    refine (Lp.norm_smul_le _ _).trans ?_
    calc ‖heatMultiplier (t - s) (sub_nonneg.2 hst)‖ * ‖lerayFourierMultiplier (H s)‖
        ≤ 1 * ‖H s‖ := mul_le_mul (heatMultiplier_norm_le_one _ _)
          (lerayFourierMultiplier_norm_le _) (norm_nonneg _) zero_le_one
      _ = ‖H s‖ := one_mul _
  · rw [dite_eq_right hst, norm_zero]
    exact norm_nonneg _

/-- The heat multiplier acts pointwise by the heat symbol. -/
theorem heatMultiplier_smul_ae_eq (t : ℝ) (ht : 0 ≤ t) (v : ComplexVectorL2) :
    ((heatMultiplier t ht • v : ComplexVectorL2) : L2Vec3 → ComplexVec3) =ᵐ[volume]
      fun ξ => heatSymbol t ξ • v ξ := by
  have hsmul := Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2) (heatMultiplier t ht) v
  have hheat : (heatMultiplier t ht : L2Vec3 → ℂ) =ᵐ[volume] heatSymbol t := by
    unfold heatMultiplier
    exact MemLp.coeFn_toLp _
  filter_upwards [hsmul, hheat] with ξ h1 h2
  rw [h1, Pi.smul_apply', h2]

/-- The frequency-side right-hand side of `eq:reg-mild-forced` agrees almost
everywhere with the pointwise representative. -/
theorem forcedFourierMild_ae_eq_rep (b : ComplexVectorL2)
    (hb : ∀ᵐ ξ ∂volume, leraySymbol ξ (b ξ) = b ξ)
    {F : ℝ → ComplexTensorL2} {Fh : L2Vec3 × ℝ → ComplexTensor3} (hFh : Measurable Fh)
    (hrepF : ∀ s, (fun ξ => Fh (ξ, s)) =ᵐ[volume] F s)
    {H : ℝ → ComplexVectorL2} {Hh : L2Vec3 × ℝ → ComplexVec3} (hHh : Measurable Hh)
    (hrepH : ∀ s, (fun ξ => Hh (ξ, s)) =ᵐ[volume] H s) {t C : ℝ} (ht : 0 ≤ t)
    (hFC : ∀ s ∈ Ioc 0 t, ‖F s‖ ≤ C) (hH : IntegrableOn (fun s => ‖H s‖) (Ioc 0 t)) :
    (forcedFourierMild b F H t ht : L2Vec3 → ComplexVec3) =ᵐ[volume]
      fun ξ => forcedFourierRep (fun η => leraySymbol η (b η)) Fh Hh (ξ, t) := by
  have hS := integrableOn_forcedFourierStokesIntegrand hFh hrepF ht hFC
  have hF := integrableOn_forcedFourierForceIntegrand hHh hrepH hH
  let γ : ℝ → ComplexVectorL2 := fun s =>
    -forcedFourierStokesIntegrand F t s + forcedFourierForceIntegrand H t s
  have hγ : Integrable γ (volume.restrict (Ioc 0 t)) := hS.neg.add hF
  let Γ : L2Vec3 × ℝ → ComplexVec3 := fun p =>
    -forcedFourierStokesRep Fh t p + forcedFourierForceRep Hh t p
  have hΓ : StronglyMeasurable Γ :=
    ((measurable_forcedFourierStokesRep hFh t).neg.add
      (measurable_forcedFourierForceRep hHh t)).stronglyMeasurable
  have hrepΓ : ∀ᵐ s ∂(volume.restrict (Ioc 0 t)),
      (fun ξ => Γ (ξ, s)) =ᵐ[volume] γ s := by
    refine Eventually.of_forall fun s => ?_
    filter_upwards [forcedFourierStokesRep_slice hrepF t s, forcedFourierForceRep_slice hrepH t s,
      Lp.coeFn_add (-forcedFourierStokesIntegrand F t s) (forcedFourierForceIntegrand H t s),
      Lp.coeFn_neg (forcedFourierStokesIntegrand F t s)] with ξ h1 h2 h3 h4
    simp only [Γ, γ]
    rw [h3, Pi.add_apply, h4, Pi.neg_apply, h1, h2]
  have hint := integral_ae_eq_integral_jointRep γ hγ Γ hΓ hrepΓ
  unfold forcedFourierMild
  filter_upwards [Lp.coeFn_add (heatMultiplier t ht • b) (∫ s in Ioc 0 t, γ s),
    heatMultiplier_smul_ae_eq t ht b, hint, hb] with ξ h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, h3]
  simp only [forcedFourierRep]
  rw [h4]
  congr 1
  have hnull : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) t)), s ≠ t := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [(measure_singleton t : volume {t} = 0) |> measure_eq_zero_iff_ae_notMem.1]
      with s hs _
    exact hs
  refine integral_congr_ae ?_
  filter_upwards [hnull, ae_restrict_mem measurableSet_Ioc] with s hs hsmem
  have hst : s < t := lt_of_le_of_ne hsmem.2 hs
  simp only [Γ, forcedFourierStokesRep, forcedFourierForceRep, hst, hst.le, ↓reduceIte,
    stokesApplyFormula, forcedFourierSource]
  rw [map_add, map_neg, map_smul, leraySymbol_apply_eq_formula, leraySymbol_apply_eq_formula,
    smul_add, smul_neg, smul_smul, mul_comm (heatSymbol (t - s) ξ)]

end CKN.Leray

end
