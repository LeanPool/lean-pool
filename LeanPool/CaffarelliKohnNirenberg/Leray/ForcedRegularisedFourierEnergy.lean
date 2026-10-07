/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedScalarEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierLeray
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierHeat
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The frequency-wise energy identity of the forced mild equation

In frequency variables the forced mild equation `eq:reg-mild-forced` is, at
each frequency `ξ`, the damped Duhamel formula
`Y(ξ,t) = e^{-λt} B(ξ) + ∫₀ᵗ e^{-λ(t-s)} ℙ(ξ) g(ξ,s) ds` with `λ = 4π²|ξ|²`,
source `g = -2πi ξ·F̂ + Fourier(H)`, and the Leray symbol `ℙ(ξ)`. This file defines
the jointly measurable frequency representative `Y` and proves, frequency by
frequency, the energy identity of the damped formula; the Leray symbol drops
out of the source pairing because `Y(ξ,s)` lies in its range.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- The heat decay rate `4π²|ξ|²` at a frequency. -/
@[expose]
def forcedFourierLam (ξ : L2Vec3) : ℝ := 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2

theorem forcedFourierLam_nonneg (ξ : L2Vec3) : 0 ≤ forcedFourierLam ξ := by
  unfold forcedFourierLam; positivity

/-- The heat symbol is the exponential of minus the decay rate times the time. -/
theorem heatSymbol_eq_exp_lam (τ : ℝ) (ξ : L2Vec3) :
    heatSymbol τ ξ = (Real.exp (-forcedFourierLam ξ * τ) : ℂ) := by
  unfold heatSymbol forcedFourierLam
  congr 2
  ring

theorem tensorDivergenceLinear_apply (ξ : L2Vec3) (F : ComplexTensor3) :
    tensorDivergenceLinear ξ F = ∑ i : Fin 3, (ξ i : ℂ) • F i := rfl

/-- The frequency source of the forced mild equation: minus `2πi` times the
tensor divergence symbol applied to the tensor, plus the force. -/
@[expose]
def forcedFourierSource (Fh : L2Vec3 × ℝ → ComplexTensor3)
    (Hh : L2Vec3 × ℝ → ComplexVec3) (p : L2Vec3 × ℝ) : ComplexVec3 :=
  -((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear p.1 (Fh p)) + Hh p

/-- The frequency representative of the forced mild equation. -/
@[expose]
def forcedFourierRep (B : L2Vec3 → ComplexVec3) (Fh : L2Vec3 × ℝ → ComplexTensor3)
    (Hh : L2Vec3 × ℝ → ComplexVec3) (p : L2Vec3 × ℝ) : ComplexVec3 :=
  heatSymbol p.2 p.1 • B p.1 +
    ∫ s in Ioc 0 p.2, heatSymbol (p.2 - s) p.1 •
      leraySymbol p.1 (forcedFourierSource Fh Hh (p.1, s))

theorem continuous_heatSymbol_uncurry :
    Continuous fun p : ℝ × L2Vec3 => heatSymbol p.1 p.2 := by
  unfold heatSymbol
  fun_prop

theorem measurable_leraySymbol_uncurry :
    Measurable fun p : L2Vec3 × ComplexVec3 => leraySymbol p.1 p.2 := by
  simp_rw [leraySymbol_apply_eq_formula]
  exact lerayApplyFormula_measurable

/-- The divergence part of the frequency source is jointly measurable. -/
theorem measurable_forcedFourierDivergence {Fh : L2Vec3 × ℝ → ComplexTensor3}
    (hFh : Measurable Fh) :
    Measurable fun p : L2Vec3 × ℝ =>
      -((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear p.1 (Fh p)) := by
  change Measurable (fun p : L2Vec3 × ℝ =>
    -((2 * Real.pi * Complex.I : ℂ) • ∑ i : Fin 3, (p.1 i : ℂ) • (Fh p) i))
  fun_prop

theorem measurable_forcedFourierSource {Fh : L2Vec3 × ℝ → ComplexTensor3}
    {Hh : L2Vec3 × ℝ → ComplexVec3} (hFh : Measurable Fh) (hHh : Measurable Hh) :
    Measurable (forcedFourierSource Fh Hh) :=
  (measurable_forcedFourierDivergence hFh).add hHh

/-- The frequency integrand of the representative is jointly measurable. -/
theorem measurable_forcedFourierIntegrand {Fh : L2Vec3 × ℝ → ComplexTensor3}
    {Hh : L2Vec3 × ℝ → ComplexVec3} (hFh : Measurable Fh) (hHh : Measurable Hh) :
    Measurable fun q : (L2Vec3 × ℝ) × ℝ => heatSymbol (q.1.2 - q.2) q.1.1 •
      leraySymbol q.1.1 (forcedFourierSource Fh Hh (q.1.1, q.2)) := by
  have hheat : Measurable fun q : (L2Vec3 × ℝ) × ℝ => heatSymbol (q.1.2 - q.2) q.1.1 := by
    fun_prop [heatSymbol]
  have hpair : Measurable fun q : (L2Vec3 × ℝ) × ℝ => (q.1.1, q.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hsrc : Measurable fun q : (L2Vec3 × ℝ) × ℝ =>
      forcedFourierSource Fh Hh (q.1.1, q.2) := by
    have h := (measurable_forcedFourierSource hFh hHh).comp hpair
    exact h
  have hpair2 : Measurable fun q : (L2Vec3 × ℝ) × ℝ =>
      (q.1.1, forcedFourierSource Fh Hh (q.1.1, q.2)) :=
    (measurable_fst.comp measurable_fst).prodMk hsrc
  have hler : Measurable fun q : (L2Vec3 × ℝ) × ℝ =>
      leraySymbol q.1.1 (forcedFourierSource Fh Hh (q.1.1, q.2)) := by
    have h := measurable_leraySymbol_uncurry.comp hpair2
    exact h
  have h := continuous_smul.measurable.comp (hheat.prodMk hler)
  exact h

/-- The frequency representative is jointly strongly measurable. -/
theorem stronglyMeasurable_forcedFourierRep {B : L2Vec3 → ComplexVec3}
    {Fh : L2Vec3 × ℝ → ComplexTensor3} {Hh : L2Vec3 × ℝ → ComplexVec3}
    (hB : Measurable B) (hFh : Measurable Fh) (hHh : Measurable Hh) :
    StronglyMeasurable (forcedFourierRep B Fh Hh) := by
  have hheat0 : Measurable fun p : L2Vec3 × ℝ => heatSymbol p.2 p.1 := by
    fun_prop [heatSymbol]
  have hfirst : Measurable fun p : L2Vec3 × ℝ => heatSymbol p.2 p.1 • B p.1 := by
    have h := continuous_smul.measurable.comp (hheat0.prodMk (hB.comp measurable_fst))
    exact h
  let S : Set ((L2Vec3 × ℝ) × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ q.1.2}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))
  have hint : StronglyMeasurable fun p : L2Vec3 × ℝ =>
      ∫ s, S.indicator (fun q : (L2Vec3 × ℝ) × ℝ => heatSymbol (q.1.2 - q.2) q.1.1 •
        leraySymbol q.1.1 (forcedFourierSource Fh Hh (q.1.1, q.2))) (p, s) := by
    refine StronglyMeasurable.integral_prod_right
      (f := fun p s => S.indicator (fun q : (L2Vec3 × ℝ) × ℝ =>
        heatSymbol (q.1.2 - q.2) q.1.1 •
        leraySymbol q.1.1 (forcedFourierSource Fh Hh (q.1.1, q.2))) (p, s)) ?_
    exact ((measurable_forcedFourierIntegrand hFh hHh).indicator hS).stronglyMeasurable
  have heq : forcedFourierRep B Fh Hh = fun p : L2Vec3 × ℝ =>
      heatSymbol p.2 p.1 • B p.1 +
      ∫ s, S.indicator (fun q : (L2Vec3 × ℝ) × ℝ => heatSymbol (q.1.2 - q.2) q.1.1 •
        leraySymbol q.1.1 (forcedFourierSource Fh Hh (q.1.1, q.2))) (p, s) := by
    funext p
    unfold forcedFourierRep
    congr 1
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  rw [heq]
  exact hfirst.stronglyMeasurable.add hint

theorem norm_tensorDivergence_source_le (ξ : L2Vec3) (F : ComplexTensor3) :
    ‖-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ F)‖ ≤
      2 * Real.pi * ‖ξ‖ * ‖F‖ := by
  rw [norm_neg, norm_smul]
  have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real, Complex.norm_ofNat,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  calc ‖(2 * Real.pi * Complex.I : ℂ)‖ * ‖tensorDivergenceLinear ξ F‖
      = 2 * Real.pi * ‖tensorDivergenceLinear ξ F‖ := by rw [hc]
    _ ≤ 2 * Real.pi * (‖ξ‖ * ‖F‖) :=
        mul_le_mul_of_nonneg_left (tensorDivergence_norm_le ξ F) hpi
    _ = 2 * Real.pi * ‖ξ‖ * ‖F‖ := by ring

/-- The pairing of a vector with the divergence part of the source is bounded
by half of the weighted squared norms. -/
theorem abs_re_inner_divergence_le (ξ : L2Vec3) (y : ComplexVec3) (F : ComplexTensor3) :
    |(inner ℂ y (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ F))).re| ≤
      (forcedFourierLam ξ * ‖y‖ ^ 2 + ‖F‖ ^ 2) / 2 := by
  have h1 := (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) y
    (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ F)))
  have h2 := mul_le_mul_of_nonneg_left (norm_tensorDivergence_source_le ξ F) (norm_nonneg y)
  have hlam : forcedFourierLam ξ = (2 * Real.pi * ‖ξ‖) ^ 2 := by
    unfold forcedFourierLam; ring
  rw [hlam]
  nlinarith only [h1, h2, sq_nonneg (2 * Real.pi * ‖ξ‖ * ‖y‖ - ‖F‖)]

theorem abs_re_inner_le_half (y z : ComplexVec3) :
    |(inner ℂ y z).re| ≤ (‖y‖ ^ 2 + ‖z‖ ^ 2) / 2 := by
  have h1 := (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) y z)
  nlinarith only [h1, sq_nonneg (‖y‖ - ‖z‖)]

/-- At a frequency where the source is integrable in time, the representative
satisfies the damped energy identity with the unprojected source. -/
theorem forcedFourierRep_frequency_identity {B : L2Vec3 → ComplexVec3}
    {Fh : L2Vec3 × ℝ → ComplexTensor3} {Hh : L2Vec3 × ℝ → ComplexVec3}
    (hFh : Measurable Fh) (hHh : Measurable Hh)
    (hBP : ∀ ξ, leraySymbol ξ (B ξ) = B ξ) (ξ : L2Vec3) {t : ℝ} (ht : 0 ≤ t)
    (hgint : IntegrableOn (fun s => forcedFourierSource Fh Hh (ξ, s)) (Ioc 0 t)) :
    ‖forcedFourierRep B Fh Hh (ξ, t)‖ ^ 2 +
        2 * forcedFourierLam ξ * ∫ s in Ioc 0 t, ‖forcedFourierRep B Fh Hh (ξ, s)‖ ^ 2 =
      ‖B ξ‖ ^ 2 + 2 * ∫ s in Ioc 0 t,
        (inner ℂ (forcedFourierRep B Fh Hh (ξ, s)) (forcedFourierSource Fh Hh (ξ, s))).re := by
  set Y : ℝ → ComplexVec3 := fun τ => forcedFourierRep B Fh Hh (ξ, τ) with hYdef
  let P := leraySymbol ξ
  let g : ℝ → ComplexVec3 := fun s => P (forcedFourierSource Fh Hh (ξ, s))
  have hsrcmeas : Measurable fun s => forcedFourierSource Fh Hh (ξ, s) :=
    (measurable_forcedFourierSource hFh hHh).comp (measurable_const.prodMk measurable_id)
  have hgOn : IntegrableOn g (Ioc 0 t) := P.integrable_comp hgint
  have hg : IntervalIntegrable g volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 hgOn
  have hkint : ∀ τ ∈ Icc 0 t, IntegrableOn
      (fun s => heatSymbol (τ - s) ξ • g s) (Ioc 0 τ) := by
    intro τ hτ
    have hsub : Ioc 0 τ ⊆ Ioc 0 t := Ioc_subset_Ioc_right hτ.2
    refine Integrable.mono' ((hgOn.mono_set hsub).norm) ?_ ?_
    · refine (Measurable.aestronglyMeasurable ?_)
      exact ((continuous_heatSymbol_uncurry.comp
        ((continuous_const.sub continuous_id).prodMk continuous_const)).measurable).smul
        (P.continuous.measurable.comp hsrcmeas)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (heatSymbol_norm_le_one (sub_nonneg.2 hs.2) ξ)
  have hy : ∀ τ ∈ uIcc 0 t, Y τ = (Real.exp (-forcedFourierLam ξ * τ) : ℂ) • B ξ +
      ∫ s in (0 : ℝ)..τ, (Real.exp (-forcedFourierLam ξ * (τ - s)) : ℂ) • g s := by
    intro τ hτ
    rw [uIcc_of_le ht] at hτ
    simp only [hYdef, forcedFourierRep, heatSymbol_eq_exp_lam]
    rw [intervalIntegral.integral_of_le hτ.1]
  have hid := damped_duhamel_complexVec3_identity (forcedFourierLam ξ) (B ξ) g Y hg hy
  rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht] at hid
  have hPY : ∀ s ∈ Ioc 0 t, P (Y s) = Y s := by
    intro s hs
    have hτ : s ∈ Icc 0 t := ⟨hs.1.le, hs.2⟩
    simp only [hYdef, forcedFourierRep]
    rw [map_add, map_smul, hBP ξ, ← P.integral_comp_comm (hkint s hτ)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [g, map_smul]
    congr 1
    exact Submodule.starProjection_eq_self_iff.2
      (Submodule.starProjection_apply_mem _ _)
  rw [hid]
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  have hPYs := hPY s hs
  simp only [g, P] at hPYs ⊢
  simp only [hYdef] at hPYs ⊢
  simp only [leraySymbol] at hPYs ⊢
  rw [← Submodule.inner_starProjection_left_eq_right, hPYs]

/-- The energy identity of the forced mild equation in frequency variables:
integrating the frequency-wise identity gives
`∫|Y(t)|² + 2∫λ∫₀ᵗ|Y|² = ∫|B|² + 2∫₀ᵗ∫Re⟨Y, -2πi ξ·F̂⟩ + 2∫₀ᵗ∫Re⟨Y, Fourier(H)⟩`,
and the weighted dissipation is integrable in frequency and time. -/
theorem forcedFourierRep_energy_identity {B : L2Vec3 → ComplexVec3}
    {Fh : L2Vec3 × ℝ → ComplexTensor3} {Hh : L2Vec3 × ℝ → ComplexVec3}
    (hBm : Measurable B) (hB : Integrable (fun ξ => ‖B ξ‖ ^ 2))
    (hFh : Measurable Fh) (hHh : Measurable Hh)
    (hBP : ∀ ξ, leraySymbol ξ (B ξ) = B ξ) {t : ℝ} (ht : 0 ≤ t)
    (hFint : Integrable (fun p => ‖Fh p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 t))))
    (hHint : Integrable (fun p => ‖Hh p‖ ^ 2) (volume.prod (volume.restrict (Ioc 0 t))))
    (hYint : Integrable (fun p => ‖forcedFourierRep B Fh Hh p‖ ^ 2)
      (volume.prod (volume.restrict (Ioc 0 t))))
    (hYt : Integrable (fun ξ => ‖forcedFourierRep B Fh Hh (ξ, t)‖ ^ 2)) :
    Integrable (fun p : L2Vec3 × ℝ => forcedFourierLam p.1 * ‖forcedFourierRep B Fh Hh p‖ ^ 2)
        (volume.prod (volume.restrict (Ioc 0 t))) ∧
    (∫ ξ, ‖forcedFourierRep B Fh Hh (ξ, t)‖ ^ 2) +
        2 * (∫ ξ, forcedFourierLam ξ *
          ∫ s in Ioc 0 t, ‖forcedFourierRep B Fh Hh (ξ, s)‖ ^ 2) =
      (∫ ξ, ‖B ξ‖ ^ 2) +
        2 * (∫ s in Ioc 0 t, ∫ ξ, (inner ℂ (forcedFourierRep B Fh Hh (ξ, s))
          (-((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear ξ (Fh (ξ, s))))).re) +
        2 * ∫ s in Ioc 0 t, ∫ ξ, (inner ℂ (forcedFourierRep B Fh Hh (ξ, s)) (Hh (ξ, s))).re := by
  set Y := forcedFourierRep B Fh Hh with hYdef
  have hμt : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) := by
    refine ⟨?_⟩
    simp only [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hYm : Measurable Y := (stronglyMeasurable_forcedFourierRep hBm hFh hHh).measurable
  let D : L2Vec3 × ℝ → ComplexVec3 := fun p =>
    -((2 * Real.pi * Complex.I : ℂ) • tensorDivergenceLinear p.1 (Fh p))
  have hDm : Measurable D := measurable_forcedFourierDivergence hFh
  let kS : L2Vec3 × ℝ → ℝ := fun p => (inner ℂ (Y p) (D p)).re
  let kH : L2Vec3 × ℝ → ℝ := fun p => (inner ℂ (Y p) (Hh p)).re
  have hkSm : Measurable kS := by
    have h := Complex.measurable_re.comp (continuous_inner.measurable.comp (hYm.prodMk hDm))
    exact h
  have hkHm : Measurable kH := by
    have h := Complex.measurable_re.comp (continuous_inner.measurable.comp (hYm.prodMk hHh))
    exact h
  -- time integrability at almost every frequency
  have hgood : ∀ᵐ ξ ∂(volume : Measure L2Vec3),
      Integrable (fun s => ‖Fh (ξ, s)‖ ^ 2) (volume.restrict (Ioc (0 : ℝ) t)) ∧
        Integrable (fun s => ‖Hh (ξ, s)‖ ^ 2) (volume.restrict (Ioc (0 : ℝ) t)) ∧
        Integrable (fun s => ‖Y (ξ, s)‖ ^ 2) (volume.restrict (Ioc (0 : ℝ) t)) := by
    filter_upwards [hFint.prod_right_ae, hHint.prod_right_ae, hYint.prod_right_ae]
      with ξ h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hslice : ∀ {E : Type} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
      [SecondCountableTopology E] {f : L2Vec3 × ℝ → E}, Measurable f → ∀ ξ,
      Integrable (fun s => ‖f (ξ, s)‖ ^ 2) (volume.restrict (Ioc (0 : ℝ) t)) →
        Integrable (fun s => ‖f (ξ, s)‖) (volume.restrict (Ioc (0 : ℝ) t)) := by
    intro E _ _ _ _ f hf ξ hsq
    have hmeas : AEStronglyMeasurable (fun s => f (ξ, s)) (volume.restrict (Ioc (0 : ℝ) t)) :=
      (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact (((memLp_two_iff_integrable_sq_norm hmeas).2 hsq).integrable one_le_two).norm
  -- the frequency identity, split into the two source pairings
  have hsplit : ∀ᵐ ξ ∂(volume : Measure L2Vec3),
      ‖Y (ξ, t)‖ ^ 2 + 2 * (forcedFourierLam ξ * ∫ s in Ioc 0 t, ‖Y (ξ, s)‖ ^ 2) =
        ‖B ξ‖ ^ 2 + 2 * (∫ s in Ioc 0 t, kS (ξ, s)) + 2 * ∫ s in Ioc 0 t, kH (ξ, s) := by
    filter_upwards [hgood] with ξ hξ
    obtain ⟨hF2, hH2, hY2⟩ := hξ
    have hF1 := hslice hFh ξ hF2
    have hH1 := hslice hHh ξ hH2
    have hsrc : IntegrableOn (fun s => forcedFourierSource Fh Hh (ξ, s)) (Ioc 0 t) := by
      refine Integrable.mono' ((hF1.const_mul (2 * Real.pi * ‖ξ‖)).add hH1) ?_ ?_
      · exact ((measurable_forcedFourierSource hFh hHh).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      · refine Eventually.of_forall fun s => ?_
        simp only [forcedFourierSource]
        exact (norm_add_le _ _).trans (add_le_add
          (norm_tensorDivergence_source_le ξ (Fh (ξ, s))) le_rfl)
    have hid := forcedFourierRep_frequency_identity hFh hHh hBP ξ ht hsrc
    have hkSint : Integrable (fun s => kS (ξ, s)) (volume.restrict (Ioc (0 : ℝ) t)) := by
      refine Integrable.mono' (((hY2.const_mul (forcedFourierLam ξ)).add hF2).div_const 2) ?_ ?_
      · exact (hkSm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      · exact Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs]
          exact abs_re_inner_divergence_le ξ (Y (ξ, s)) (Fh (ξ, s))
    have hkHint : Integrable (fun s => kH (ξ, s)) (volume.restrict (Ioc (0 : ℝ) t)) := by
      refine Integrable.mono' ((hY2.add hH2).div_const 2) ?_ ?_
      · exact (hkHm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      · exact Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs]
          exact abs_re_inner_le_half (Y (ξ, s)) (Hh (ξ, s))
    have hsum : ∫ s in Ioc 0 t, (inner ℂ (Y (ξ, s)) (forcedFourierSource Fh Hh (ξ, s))).re =
        (∫ s in Ioc 0 t, kS (ξ, s)) + ∫ s in Ioc 0 t, kH (ξ, s) := by
      rw [← integral_add hkSint hkHint]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only [kS, kH, D, forcedFourierSource, inner_add_right, Complex.add_re]
    rw [hsum] at hid
    linear_combination hid
  -- integrability in frequency
  have hkHprod : Integrable kH (volume.prod (volume.restrict (Ioc (0 : ℝ) t))) := by
    refine Integrable.mono' ((hYint.add hHint).div_const 2) hkHm.aestronglyMeasurable ?_
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact abs_re_inner_le_half (Y p) (Hh p)
  have hdmeas : StronglyMeasurable fun ξ : L2Vec3 =>
      forcedFourierLam ξ * ∫ s in Ioc 0 t, ‖Y (ξ, s)‖ ^ 2 := by
    refine StronglyMeasurable.mul ?_ ?_
    · exact (continuous_const.mul ((continuous_norm).pow 2)).stronglyMeasurable
    · exact StronglyMeasurable.integral_prod_right
        (f := fun ξ s => ‖Y (ξ, s)‖ ^ 2) (hYm.norm.pow_const 2).stronglyMeasurable
  have hdint : Integrable (fun ξ => forcedFourierLam ξ * ∫ s in Ioc 0 t, ‖Y (ξ, s)‖ ^ 2) := by
    have hbound : Integrable (fun ξ => ‖B ξ‖ ^ 2 + (∫ s in Ioc 0 t, ‖Fh (ξ, s)‖ ^ 2) +
        2 * |∫ s in Ioc 0 t, kH (ξ, s)|) :=
      (hB.add hFint.integral_prod_left).add (hkHprod.integral_prod_left.abs.const_mul 2)
    refine Integrable.mono' hbound hdmeas.aestronglyMeasurable ?_
    filter_upwards [hsplit, hgood] with ξ hξ hgξ
    obtain ⟨hF2, _, hY2⟩ := hgξ
    have hd0 : 0 ≤ forcedFourierLam ξ * ∫ s in Ioc 0 t, ‖Y (ξ, s)‖ ^ 2 :=
      mul_nonneg (forcedFourierLam_nonneg ξ) (integral_nonneg fun _ => by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hd0]
    have hS0 : |∫ s, kS (ξ, s) ∂(volume.restrict (Ioc (0 : ℝ) t))| ≤
        ∫ s, (forcedFourierLam ξ * ‖Y (ξ, s)‖ ^ 2 + ‖Fh (ξ, s)‖ ^ 2) / 2
          ∂(volume.restrict (Ioc (0 : ℝ) t)) :=
      (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
        (Eventually.of_forall fun _ => abs_nonneg _)
        (((hY2.const_mul _).add hF2).div_const 2) (Eventually.of_forall fun s =>
          abs_re_inner_divergence_le ξ (Y (ξ, s)) (Fh (ξ, s))))
    have hS1 : ∫ s, (forcedFourierLam ξ * ‖Y (ξ, s)‖ ^ 2 + ‖Fh (ξ, s)‖ ^ 2) / 2
          ∂(volume.restrict (Ioc (0 : ℝ) t)) =
        (forcedFourierLam ξ * ∫ s, ‖Y (ξ, s)‖ ^ 2 ∂(volume.restrict (Ioc (0 : ℝ) t)) +
          ∫ s, ‖Fh (ξ, s)‖ ^ 2 ∂(volume.restrict (Ioc (0 : ℝ) t))) / 2 := by
      rw [integral_div, integral_add (hY2.const_mul _) hF2, integral_const_mul]
    have hS := hS0.trans_eq hS1
    have hY0 : 0 ≤ ‖Y (ξ, t)‖ ^ 2 := by positivity
    have hHa := le_abs_self (∫ s in Ioc 0 t, kH (ξ, s))
    have hSa := le_abs_self (∫ s in Ioc 0 t, kS (ξ, s))
    linarith only [hξ, hS, hY0, hHa, hSa]
  -- product integrability of the divergence pairing
  have hlamprod : Integrable (fun p : L2Vec3 × ℝ => forcedFourierLam p.1 * ‖Y p‖ ^ 2)
      (volume.prod (volume.restrict (Ioc (0 : ℝ) t))) := by
    have hm : AEStronglyMeasurable (fun p : L2Vec3 × ℝ => forcedFourierLam p.1 * ‖Y p‖ ^ 2)
        (volume.prod (volume.restrict (Ioc (0 : ℝ) t))) :=
      ((continuous_const.mul ((continuous_norm).pow 2)).measurable.comp measurable_fst |>.mul
        (hYm.norm.pow_const 2)).aestronglyMeasurable
    rw [integrable_prod_iff hm]
    constructor
    · filter_upwards [hgood] with ξ hξ
      exact hξ.2.2.const_mul _
    · refine hdint.congr (Eventually.of_forall fun ξ => ?_)
      simp only
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (forcedFourierLam_nonneg ξ)
        (by positivity))]
  refine ⟨hlamprod, ?_⟩
  have hkSprod : Integrable kS (volume.prod (volume.restrict (Ioc (0 : ℝ) t))) := by
    refine Integrable.mono' ((hlamprod.add hFint).div_const 2) hkSm.aestronglyMeasurable ?_
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact abs_re_inner_divergence_le p.1 (Y p) (Fh p)
  -- integrate the frequency identity
  have hint := integral_congr_ae hsplit
  have hd2 : Integrable (fun ξ => 2 * (forcedFourierLam ξ *
      ∫ s in Ioc 0 t, ‖Y (ξ, s)‖ ^ 2)) := hdint.const_mul 2
  have hS2 : Integrable (fun ξ => 2 * ∫ s in Ioc 0 t, kS (ξ, s)) :=
    hkSprod.integral_prod_left.const_mul 2
  have hH2 : Integrable (fun ξ => 2 * ∫ s in Ioc 0 t, kH (ξ, s)) :=
    hkHprod.integral_prod_left.const_mul 2
  have hBS : Integrable (fun ξ => ‖B ξ‖ ^ 2 + 2 * ∫ s in Ioc 0 t, kS (ξ, s)) := hB.add hS2
  rw [integral_add hYt hd2, integral_add hBS hH2, integral_add hB hS2, integral_const_mul,
    integral_const_mul, integral_const_mul] at hint
  have hswapS := integral_integral_swap (μ := (volume : Measure L2Vec3))
    (ν := (volume.restrict (Ioc (0 : ℝ) t)))
    (f := fun ξ s => kS (ξ, s)) hkSprod
  have hswapH := integral_integral_swap (μ := (volume : Measure L2Vec3))
    (ν := (volume.restrict (Ioc (0 : ℝ) t)))
    (f := fun ξ s => kH (ξ, s)) hkHprod
  rw [hswapS, hswapH] at hint
  exact hint

end CKN.Leray

end
