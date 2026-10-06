/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolevZeroExt
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Density extension for weighted Carleman inequalities

This module extends smooth compactly supported inequalities to compactly
supported fields with space-time weak derivatives (`lem:carleman-sobolev` of the
Escauriaza–Seregin–Šverák manuscript).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Pointwise
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

private theorem memLp_of_setLIntegral_enorm_sq_lt_top
    {X E : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [NormedAddCommGroup E] [SecondCountableTopology X]
    {μ : Measure X} {s : Set X} {f : X → E}
    (hf : LocallyIntegrableOn f s μ)
    (hfin : ∫⁻ x in s, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ⊤) :
    MemLp f (2 : ℝ≥0∞) (μ.restrict s) := by
  have hfmeas : AEStronglyMeasurable f (μ.restrict s) := hf.aestronglyMeasurable
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (p := (2 : ℝ≥0∞)) (μ := μ.restrict s) (by norm_num) (by norm_num) hfmeas).2
  simpa using hfin

/-- Finite space-time `L²` data give global `L²` zero extensions of the field and its weak
derivatives (`lem:carleman-sobolev`, ESS). -/
theorem zeroExtend_spaceTimeData_memLp
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet Ω I,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    MemLp (zeroExtendField (Ω ×ˢ I)
      (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q))) 2
        (volume : Measure (Vec3 × ℝ)) ∧
    MemLp (zeroExtendField (Ω ×ˢ I)
      (fun q : Vec3 × ℝ => Dw (parabolicHomeomorph.symm q))) 2
        (volume : Measure (Vec3 × ℝ)) ∧
    MemLp (zeroExtendField (Ω ×ˢ I)
      (fun q : Vec3 × ℝ => D2w (parabolicHomeomorph.symm q))) 2
        (volume : Measure (Vec3 × ℝ)) ∧
    MemLp (zeroExtendField (Ω ×ˢ I)
      (fun q : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm q))) 2
        (volume : Measure (Vec3 × ℝ)) := by
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  let W : Vec3 × ℝ → ℝ≥0∞ := fun q =>
    ‖w (parabolicHomeomorph.symm q)‖ₑ ^ (2 : ℝ)
  let G : Vec3 × ℝ → ℝ≥0∞ := fun q =>
    ‖Dw (parabolicHomeomorph.symm q)‖ₑ ^ (2 : ℝ)
  let H : Vec3 × ℝ → ℝ≥0∞ := fun q =>
    ‖D2w (parabolicHomeomorph.symm q)‖ₑ ^ (2 : ℝ)
  let T : Vec3 × ℝ → ℝ≥0∞ := fun q =>
    ‖Dtw (parabolicHomeomorph.symm q)‖ₑ ^ (2 : ℝ)
  let A : ParabolicPoint → ℝ≥0∞ := fun z =>
    ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
      ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)
  let B : Vec3 × ℝ → ℝ≥0∞ := fun q => W q + G q + H q + T q
  have hUmeas : MeasurableSet U := (hΩ.prod hI).measurableSet
  have hSmeas : MeasurableSet (spaceTimeSet Ω I) :=
    (isOpen_spaceTimeSet Ω I hΩ hI).measurableSet
  have hL2prod : (∫⁻ q in U, B q ∂(volume : Measure (Vec3 × ℝ))) < ⊤ := by
    rw [← setLIntegral_parabolic_to_product (F := A)]
    simpa [A, B, W, G, H, T, U] using hL2
  have htotalFull :
      (∫⁻ q, U.indicator B q ∂(volume : Measure (Vec3 × ℝ))) < ⊤ := by
    rw [lintegral_indicator hUmeas]
    exact hL2prod
  have hWle : ∀ q, W q ≤ B q := by
    intro q
    dsimp [B]
    calc
      W q ≤ W q + G q := le_add_of_nonneg_right (by positivity)
      _ ≤ W q + G q + H q := le_add_of_nonneg_right (by positivity)
      _ ≤ W q + G q + H q + T q := le_add_of_nonneg_right (by positivity)
  have hGle : ∀ q, G q ≤ B q := by
    intro q
    dsimp [B]
    calc
      G q ≤ W q + G q := le_add_of_nonneg_left (by positivity)
      _ ≤ W q + G q + H q := le_add_of_nonneg_right (by positivity)
      _ ≤ W q + G q + H q + T q := le_add_of_nonneg_right (by positivity)
  have hHle : ∀ q, H q ≤ B q := by
    intro q
    dsimp [B]
    calc
      H q ≤ W q + G q + H q := le_add_of_nonneg_left (by positivity)
      _ ≤ W q + G q + H q + T q := le_add_of_nonneg_right (by positivity)
  have hTle : ∀ q, T q ≤ B q := by
    intro q
    dsimp [B]
    exact le_add_of_nonneg_left (by positivity)
  have hWfull :
      (∫⁻ q, U.indicator W q ∂(volume : Measure (Vec3 × ℝ))) < ⊤ := by
    apply lt_of_le_of_lt ?_ htotalFull
    apply lintegral_mono
    intro q
    by_cases hq : q ∈ U
    · simpa [hq] using hWle q
    · simp [hq]
  have hGfull :
      (∫⁻ q, U.indicator G q ∂(volume : Measure (Vec3 × ℝ))) < ⊤ := by
    apply lt_of_le_of_lt ?_ htotalFull
    apply lintegral_mono
    intro q
    by_cases hq : q ∈ U
    · simpa [hq] using hGle q
    · simp [hq]
  have hHfull :
      (∫⁻ q, U.indicator H q ∂(volume : Measure (Vec3 × ℝ))) < ⊤ := by
    apply lt_of_le_of_lt ?_ htotalFull
    apply lintegral_mono
    intro q
    by_cases hq : q ∈ U
    · simpa [hq] using hHle q
    · simp [hq]
  have hTfull :
      (∫⁻ q, U.indicator T q ∂(volume : Measure (Vec3 × ℝ))) < ⊤ := by
    apply lt_of_le_of_lt ?_ htotalFull
    apply lintegral_mono
    intro q
    by_cases hq : q ∈ U
    · simpa [hq] using hTle q
    · simp [hq]
  have hWfin : (∫⁻ q in U, W q ∂(volume : Measure (Vec3 × ℝ))) < ⊤ := by
    simpa [lintegral_indicator hUmeas] using hWfull
  have hGfin : (∫⁻ q in U, G q ∂(volume : Measure (Vec3 × ℝ))) < ⊤ := by
    simpa [lintegral_indicator hUmeas] using hGfull
  have hHfin : (∫⁻ q in U, H q ∂(volume : Measure (Vec3 × ℝ))) < ⊤ := by
    simpa [lintegral_indicator hUmeas] using hHfull
  have hTfin : (∫⁻ q in U, T q ∂(volume : Measure (Vec3 × ℝ))) < ⊤ := by
    simpa [lintegral_indicator hUmeas] using hTfull
  have hWloc := locallyIntegrableOn_parabolic_to_product hΩ hI hderiv.1
  have hGloc := locallyIntegrableOn_parabolic_to_product hΩ hI hderiv.2.1
  have hHloc := locallyIntegrableOn_parabolic_to_product hΩ hI hderiv.2.2.1
  have hTloc := locallyIntegrableOn_parabolic_to_product hΩ hI hderiv.2.2.2.1
  have hWmem : MemLp (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q)) 2
      ((volume : Measure (Vec3 × ℝ)).restrict U) := by
    apply memLp_of_setLIntegral_enorm_sq_lt_top hWloc
    simpa [W] using hWfin
  have hGmem : MemLp (fun q : Vec3 × ℝ => Dw (parabolicHomeomorph.symm q)) 2
      ((volume : Measure (Vec3 × ℝ)).restrict U) := by
    apply memLp_of_setLIntegral_enorm_sq_lt_top hGloc
    simpa [G] using hGfin
  have hHmem : MemLp (fun q : Vec3 × ℝ => D2w (parabolicHomeomorph.symm q)) 2
      ((volume : Measure (Vec3 × ℝ)).restrict U) := by
    apply memLp_of_setLIntegral_enorm_sq_lt_top hHloc
    simpa [H] using hHfin
  have hTmem : MemLp (fun q : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm q)) 2
      ((volume : Measure (Vec3 × ℝ)).restrict U) := by
    apply memLp_of_setLIntegral_enorm_sq_lt_top hTloc
    simpa [T] using hTfin
  refine ⟨?_, ?_, ?_, ?_⟩
  · change MemLp (U.indicator (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q))) 2 _
    exact (memLp_indicator_iff_restrict hUmeas).2 hWmem
  · change MemLp (U.indicator (fun q : Vec3 × ℝ => Dw (parabolicHomeomorph.symm q))) 2 _
    exact (memLp_indicator_iff_restrict hUmeas).2 hGmem
  · change MemLp (U.indicator (fun q : Vec3 × ℝ => D2w (parabolicHomeomorph.symm q))) 2 _
    exact (memLp_indicator_iff_restrict hUmeas).2 hHmem
  · change MemLp (U.indicator (fun q : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm q))) 2 _
    exact (memLp_indicator_iff_restrict hUmeas).2 hTmem

/-- A finite-coordinate projection preserves MemLp (`lem:carleman-sobolev`, ESS). -/
theorem memLp_pi_component
    {X ι E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [Fintype ι]
    {μ : Measure X} {f : X → ι → E} {p : ℝ≥0∞}
    (hf : MemLp f p μ) (i : ι) : MemLp (fun x => f x i) p μ := by
  apply hf.of_le
  · exact (continuous_apply i).comp_aestronglyMeasurable hf.aestronglyMeasurable
  · filter_upwards [] with x
    exact norm_le_pi_norm (f x) i

/-- A bounded measurable weight preserves quadratic integral convergence under `L²`
convergence (`lem:carleman-sobolev`, ESS). -/
theorem weightedSq_tendsto
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {ρ : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hρ : AEStronglyMeasurable ρ μ)
    (hρbound : ∀ᵐ x ∂μ, ‖ρ x‖ ≤ C)
    {f : X → ℝ} {fseq : ℕ → X → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) μ)
    (hfseq : ∀ n, MemLp (fseq n) (2 : ℝ≥0∞) μ)
    (hconv : Tendsto (fun n => eLpNorm (fseq n - f) (2 : ℝ≥0∞) μ)
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, ρ x * (fseq n x) ^ 2 ∂μ)
      atTop (nhds (∫ x, ρ x * f x ^ 2 ∂μ)) := by
  have hweight (g : X → ℝ) (hg : MemLp g (2 : ℝ≥0∞) μ) :
      Integrable (fun x => ρ x * g x ^ 2) μ := by
    have hsq : Integrable (fun x => g x * g x) μ := hg.integrable_mul hg
    have hmul := hsq.mul_bdd hρ hρbound
    convert hmul using 1
    ext x
    ring
  have hLpDiff : Tendsto (fun n => lpNorm (fseq n - f) 2 μ) atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
    change Tendsto (fun n => (eLpNorm (fseq n - f) 2 μ).toReal) atTop (nhds 0)
    rw [show (fun n => (eLpNorm (fseq n - f) 2 μ).toReal) =
      ENNReal.toReal ∘ (fun n => eLpNorm (fseq n - f) 2 μ) by rfl]
    exact h
  have hsumBound : ∀ᶠ n in atTop,
      lpNorm (fun x => fseq n x + f x) 2 μ ≤ 1 + 2 * lpNorm f 2 μ := by
    have hsmall : ∀ᶠ n in atTop, lpNorm (fseq n - f) 2 μ < 1 :=
      hLpDiff.eventually (gt_mem_nhds (by norm_num))
    filter_upwards [hsmall] with n hn
    have hfn : lpNorm (fseq n) 2 μ ≤ lpNorm f 2 μ + lpNorm (fseq n - f) 2 μ :=
      MeasureTheory.lpNorm_le_lpNorm_add_lpNorm_sub' hf
        (by norm_num : 1 ≤ (2 : ℝ≥0∞))
    have hsum := MeasureTheory.lpNorm_add_le (hfseq n) (g := f)
      (by norm_num : 1 ≤ (2 : ℝ≥0∞))
    calc
      lpNorm (fun x => fseq n x + f x) 2 μ
        ≤ lpNorm (fseq n) 2 μ + lpNorm f 2 μ := by
          change lpNorm (fseq n + f) 2 μ ≤ _
          exact hsum
      _ ≤ 2 * lpNorm f 2 μ + lpNorm (fseq n - f) 2 μ := by
          linarith only [hfn]
      _ ≤ 1 + 2 * lpNorm f 2 μ := by linarith only [hn]
  have hboundTendsto : Tendsto
      (fun n => C * lpNorm (fseq n - f) 2 μ * (1 + 2 * lpNorm f 2 μ))
      atTop (nhds 0) := by
    have hfirst : Tendsto (fun n => C * lpNorm (fseq n - f) 2 μ)
        atTop (nhds 0) := by
      simpa [mul_comm] using hLpDiff.const_mul C
    simpa using hfirst.mul_const (1 + 2 * lpNorm f 2 μ)
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => dist_nonneg) ?_ hboundTendsto
  filter_upwards [hsumBound] with n hsn
  let d : X → ℝ := fun x => fseq n x - f x
  let s : X → ℝ := fun x => fseq n x + f x
  have hd : MemLp d 2 μ := by dsimp [d]; exact (hfseq n).sub hf
  have hs : MemLp s 2 μ := by dsimp [s]; exact (hfseq n).add hf
  have hprod : Integrable (fun x => d x * s x) μ := hd.integrable_mul hs
  have hρprod : Integrable (fun x => ρ x * (d x * s x)) μ := by
    have hmul := hprod.mul_bdd hρ hρbound
    convert hmul using 1
    ext x
    ring
  have hfnweight : Integrable (fun x => ρ x * (fseq n x) ^ 2) μ :=
    hweight _ (hfseq n)
  have hdiffIntegral :
      (∫ x, ρ x * (fseq n x) ^ 2 ∂μ) - ∫ x, ρ x * f x ^ 2 ∂μ =
        ∫ x, ρ x * (d x * s x) ∂μ := by
    rw [← integral_sub hfnweight (hweight f hf)]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [d, s]
    ring
  have hnormBound : ‖∫ x, ρ x * (d x * s x) ∂μ‖ ≤
      C * (lpNorm d 2 μ * lpNorm s 2 μ) := by
    have hboundInt : Integrable (fun x => C * (‖d x‖ * ‖s x‖)) μ := by
      have h := hprod.norm.const_mul C
      convert h using 1
      ext x
      simp [norm_mul]
    have hpoint : ∀ᵐ x ∂μ,
        ‖ρ x * (d x * s x)‖ ≤ C * (‖d x‖ * ‖s x‖) := by
      filter_upwards [hρbound] with x hx
      calc
        ‖ρ x * (d x * s x)‖ = ‖ρ x‖ * (‖d x‖ * ‖s x‖) := by simp [norm_mul]
        _ ≤ C * (‖d x‖ * ‖s x‖) := mul_le_mul_of_nonneg_right hx (by positivity)
    have hmono := integral_mono_ae hρprod.norm hboundInt hpoint
    have hdR : MemLp d (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hd
    have hsR : MemLp s (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hs
    have hholder := integral_mul_norm_le_Lp_mul_Lq
      (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ))
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hdR hsR
    have hholder' : ∫ x, ‖d x‖ * ‖s x‖ ∂μ ≤ lpNorm d 2 μ * lpNorm s 2 μ := by
      rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by simp) hd.aestronglyMeasurable,
        lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by simp) hs.aestronglyMeasurable]
      simpa using hholder
    calc
      _ ≤ ∫ x, ‖ρ x * (d x * s x)‖ ∂μ :=
        norm_integral_le_integral_norm (fun x => ρ x * (d x * s x))
      _ ≤ ∫ x, C * (‖d x‖ * ‖s x‖) ∂μ := hmono
      _ = C * ∫ x, ‖d x‖ * ‖s x‖ ∂μ := integral_const_mul _ _
      _ ≤ C * (lpNorm d 2 μ * lpNorm s 2 μ) := by gcongr
  have herror : dist
      (∫ x, ρ x * (fseq n x) ^ 2 ∂μ) (∫ x, ρ x * f x ^ 2 ∂μ) ≤
      C * lpNorm (fseq n - f) 2 μ * (1 + 2 * lpNorm f 2 μ) := by
    have hfac' : C * (lpNorm d 2 μ * lpNorm s 2 μ) =
        C * lpNorm d 2 μ * lpNorm s 2 μ := by ring
    have hsn' : lpNorm s 2 μ ≤ 1 + 2 * lpNorm f 2 μ := by simpa [s] using hsn
    have hdEq : d = fseq n - f := rfl
    calc
      _ = ‖∫ x, ρ x * (d x * s x) ∂μ‖ := by rw [dist_eq_norm, hdiffIntegral]
      _ ≤ C * (lpNorm d 2 μ * lpNorm s 2 μ) := hnormBound
      _ ≤ C * lpNorm d 2 μ * (1 + 2 * lpNorm f 2 μ) := by
        rw [hfac']
        have hdnonneg : 0 ≤ lpNorm d 2 μ := lpNorm_nonneg
        exact mul_le_mul_of_nonneg_left hsn' (mul_nonneg hC hdnonneg)
      _ = C * lpNorm (fseq n - f) 2 μ * (1 + 2 * lpNorm f 2 μ) := by
        rw [← hdEq]
  simpa using herror

/-- A componentwise space-time mollification is a smooth compactly supported test field when
its closed support neighborhood remains inside the product domain (`lem:carleman-sobolev`, ESS). -/
theorem spaceTimeMollifyPi_mem_spaceTimeTestFunction
    {Ω : Set Vec3} {I : Set ℝ} {f : Vec3 × ℝ → Fin 3 → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hf : HasCompactSupport f)
    (hthick : Metric.closedBall (0 : Vec3 × ℝ) δ + tsupport f ⊆ Ω ×ˢ I)
    (hloc : ∀ i : Fin 3, LocallyIntegrable
      (fun x : Vec3 × ℝ => f x i) (volume : Measure (Vec3 × ℝ))) :
    spaceTimeMollifyPi f δ hδ ∈ spaceTimeTestFunction (V := Vec3) Ω I := by
  have hcont : ContDiff ℝ (⊤ : ℕ∞) (spaceTimeMollifyPi f δ hδ) :=
    spaceTimeMollifyPi_contDiff hδ hloc
  have hcompact : HasCompactSupport (spaceTimeMollifyPi f δ hδ) :=
    spaceTimeMollifyPi_hasCompactSupport hδ hf
  let K : Set (Vec3 × ℝ) := Metric.closedBall 0 δ + tsupport f
  have hKcompact : IsCompact K :=
    (isCompact_closedBall (0 : Vec3 × ℝ) δ).add hf.isCompact
  have hsupport : Function.support (spaceTimeMollifyPi f δ hδ) ⊆ K := by
    calc
      Function.support (spaceTimeMollifyPi f δ hδ) ⊆
          Metric.ball (0 : Vec3 × ℝ) δ + Function.support f :=
        spaceTimeMollifyPi_support_subset hδ
      _ ⊆ Metric.closedBall 0 δ + tsupport f :=
        add_subset_add Metric.ball_subset_closedBall (subset_tsupport f)
  have htsupport : tsupport (spaceTimeMollifyPi f δ hδ) ⊆ K :=
    closure_minimal hsupport hKcompact.isClosed
  exact ⟨hcont, hcompact, htsupport.trans (by simpa [K, spaceTimeSet] using hthick)⟩

/-- A compactly supported field in an open product domain admits a sequence of smooth compactly
supported mollifications in that same domain, with radii tending to zero
(`lem:carleman-sobolev`, ESS). -/
theorem exists_spaceTimeMollifyPi_testSequence
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    {f : Vec3 × ℝ → Fin 3 → ℝ} (hf : HasCompactSupport f)
    (hfsupport : tsupport f ⊆ Ω ×ˢ I)
    (hloc : ∀ i : Fin 3, LocallyIntegrable
      (fun x : Vec3 × ℝ => f x i) (volume : Measure (Vec3 × ℝ))) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ n, 0 < δ n ∧ ∀ hδ : 0 < δ n,
        spaceTimeMollifyPi f (δ n) hδ ∈ spaceTimeTestFunction (V := Vec3) Ω I := by
  let K : Set (Vec3 × ℝ) := tsupport f
  have hKcompact : IsCompact K := hf.isCompact
  have hKU : K ⊆ Ω ×ˢ I := by simpa [K] using hfsupport
  have hUopen : IsOpen (Ω ×ˢ I) := hΩ.prod hI
  obtain ⟨r, hrpos, hrK⟩ := hKcompact.exists_cthickening_subset_open hUopen hKU
  let δ : ℕ → ℝ := fun n => (r / 2) * ((n : ℝ) + 1)⁻¹
  have hδtendsto : Tendsto δ atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (r / 2)
    simpa [δ, mul_comm] using h
  refine ⟨δ, hδtendsto, ?_⟩
  intro n
  have hδpos : 0 < δ n := by
    dsimp [δ]
    positivity
  refine ⟨hδpos, fun hδ => ?_⟩
  have hnNat : 1 ≤ n + 1 := by omega
  have hn : 1 ≤ (n : ℝ) + 1 := by exact_mod_cast hnNat
  have hinv : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  have hδle : δ n ≤ r := by
    dsimp [δ]
    calc
      (r / 2) * ((n : ℝ) + 1)⁻¹ ≤ (r / 2) * 1 :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = r / 2 := by ring
      _ ≤ r := by linarith only [hrpos]
  have hMinkowski : Metric.closedBall (0 : Vec3 × ℝ) (δ n) + K ⊆
      Metric.cthickening r K := by
    rintro z ⟨u, hu, v, hv, rfl⟩
    apply Metric.mem_cthickening_of_dist_le (u + v) v r K hv
    calc
      dist (u + v) v = dist u 0 := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      _ ≤ δ n := by simpa using hu
      _ ≤ r := hδle
  have hthick : Metric.closedBall (0 : Vec3 × ℝ) (δ n) + tsupport f ⊆ Ω ×ˢ I := by
    simpa [K] using hMinkowski.trans hrK
  exact spaceTimeMollifyPi_mem_spaceTimeTestFunction hδ hf hthick hloc

end CKN
