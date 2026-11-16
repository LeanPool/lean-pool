/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoAlgebra

/-!
# The Itô integral of an indicator is a Brownian increment

The integrand `1_{(a, b]}` is simple, so its `L²` Itô integral up to a time `t` is the elementary
integral `W_{b ∧ t} − W_{a ∧ t}`.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Indicator

/-- The indicator integrand of a time window, as a process constant in the sample point. -/
noncomputable def indIoc (Ω) [MeasurableSpace Ω] (a b : ℝ) : Ω → ℝ → ℝ :=
  fun _ s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s

theorem indIoc_le_one (a b : ℝ) (ω : Ω) (s : ℝ) : |indIoc Ω a b ω s| ≤ 1 := by
  unfold indIoc
  by_cases h : s ∈ Set.Ioc a b
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num

theorem measurable_uncurry_indIoc (a b : ℝ) :
    Measurable (Function.uncurry (indIoc Ω a b)) :=
  ((measurable_const.indicator measurableSet_Ioc).comp measurable_snd)

theorem progressivelyMeasurable_indIoc (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b) := by
  have hfun : indIoc Ω a b = fun ω s => (stepIoc Ω ha hab).eval s ω := by
    funext ω s; rw [stepIoc_eval]; rfl
  rw [hfun]
  exact (stepIoc Ω ha hab).progressivelyMeasurable_eval ℱ (stepIoc_adapt ℱ ha hab)

theorem progressivelyMeasurable_indIoc₀ (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ}
    (hb : 0 < b) : Probability.ProgressivelyMeasurable ℱ (indIoc Ω 0 b) := by
  have hfun : indIoc Ω 0 b = fun ω s => (stepIoc₀ Ω hb).eval s ω := by
    funext ω s; rw [stepIoc₀_eval]; rfl
  rw [hfun]
  exact (stepIoc₀ Ω hb).progressivelyMeasurable_eval ℱ (stepIoc₀_adapt ℱ hb)

theorem lintegral_sq_indIoc_lt_top (P : Measure Ω) [IsProbabilityMeasure P] (a b : ℝ)
    (T : ℝ) (_hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hpt : ∀ (ω : Ω) (s : ℝ), (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ≤ 1 := by
    intro ω s
    have hx : ‖indIoc Ω a b ω s‖ ≤ 1 := (Real.norm_eq_abs _).le.trans (indIoc_le_one a b ω s)
    have : (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ≤ 1 := by
      rw [← ENNReal.coe_one, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
      simpa using hx
    simpa using pow_le_pow_left' this 2
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ : Ω, ∫⁻ _ in Set.Icc (0 : ℝ) T, (1 : ℝ≥0∞) ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ < ⊤ := by
        simp only [lintegral_one, Measure.restrict_apply_univ, Real.volume_Icc,
          lintegral_const, measure_univ, mul_one]
        exact ENNReal.ofReal_lt_top

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **The Itô integral of an indicator is a Brownian increment.** -/
theorem stochasticIntegralBrownian_indIoc {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hm : Measurable (Function.uncurry (indIoc Ω a b)))
    (hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b))
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (indIoc Ω a b) hm hp hq t
      =ᵐ[P] fun ω => W.W (min b t) ω - W.W (min a t) ω := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hfun : indIoc Ω 0 b = fun ω s => (stepIoc₀ Ω hab).eval s ω := by
      funext ω s; rw [stepIoc₀_eval]; rfl
    have hm' : Measurable (Function.uncurry fun ω s => (stepIoc₀ Ω hab).eval s ω) := by
      rw [← hfun]; exact hm
    have hp' : Probability.ProgressivelyMeasurable ℱ fun ω s => (stepIoc₀ Ω hab).eval s ω := by
      rw [← hfun]; exact hp
    have hq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(stepIoc₀ Ω hab).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT
      have := hq T hT
      rwa [hfun] at this
    have hkey := stochasticIntegralBrownian_eval_simple W ℱ hℱ (stepIoc₀ Ω hab)
      (stepIoc₀_adapt ℱ hab) hm' hp' hq' ht
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun.symm hm' hp' hq' hm hp hq t] at hkey
    exact hkey.trans (Filter.Eventually.of_forall fun ω => stepIoc₀_integralAgainst hab W.W t ω)
  · have hfun : indIoc Ω a b = fun ω s => (stepIoc Ω ha' hab).eval s ω := by
      funext ω s; rw [stepIoc_eval]; rfl
    have hm' : Measurable (Function.uncurry fun ω s => (stepIoc Ω ha' hab).eval s ω) := by
      rw [← hfun]; exact hm
    have hp' : Probability.ProgressivelyMeasurable ℱ fun ω s => (stepIoc Ω ha' hab).eval s ω := by
      rw [← hfun]; exact hp
    have hq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(stepIoc Ω ha' hab).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT
      have := hq T hT
      rwa [hfun] at this
    have hkey := stochasticIntegralBrownian_eval_simple W ℱ hℱ (stepIoc Ω ha' hab)
      (stepIoc_adapt ℱ ha' hab) hm' hp' hq' ht
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun.symm hm' hp' hq' hm hp hq t] at hkey
    exact hkey.trans
      (Filter.Eventually.of_forall fun ω => stepIoc_integralAgainst ha' hab W.W t ω)

include hℱ in
/-- The Itô integral of the constant integrand `1` at a time `t ≥ 0` is the Brownian value at
`t`. -/
theorem stochasticIntegralBrownian_one
    (hm : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (1 : ℝ)))
    (hp : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (1 : ℝ))
    (hq : ∀ T, 0 < T → ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
      (‖(1 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (fun _ _ => (1 : ℝ)) hm hp hq t =ᵐ[P] W.W t := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · filter_upwards [stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ
      (fun _ _ => (1 : ℝ)) hm hp hq (le_refl (0 : ℝ)), W.initial_zero] with ω h1 h2
    simp [h1, h2]
  · have hmul : (fun (_ : Ω) (s : ℝ) =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * (1 : ℝ)) = indIoc Ω 0 t := by
      funext _ _
      simp [indIoc]
    have hm' : Measurable (Function.uncurry (indIoc Ω 0 t)) := measurable_uncurry_indIoc 0 t
    have hp' : Probability.ProgressivelyMeasurable ℱ (indIoc Ω 0 t) :=
      progressivelyMeasurable_indIoc₀ ℱ ht'
    have hq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖indIoc Ω 0 t ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
      fun T hT => lintegral_sq_indIoc_lt_top P 0 t T hT
    have him : Measurable (Function.uncurry fun (_ : Ω) (s : ℝ) =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * (1 : ℝ)) := by
      rw [hmul]; exact hm'
    have hip : Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (s : ℝ) =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * (1 : ℝ)) := by
      rw [hmul]; exact hp'
    have hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * (1 : ℝ)‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ := by
      intro T hT
      simpa [indIoc] using hq' T hT
    have hkey := stochasticIntegralBrownian_indicator_Ioc W ℱ hℱ (fun _ _ => (1 : ℝ)) hm hp hq
      (a := 0) (b := t) le_rfl ht' him hip hiq ht'
    rw [min_self, min_eq_left ht'.le] at hkey
    have hI : stochasticIntegralBrownian W ℱ hℱ (fun (_ : Ω) (s : ℝ) =>
        (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * (1 : ℝ)) him hip hiq t
        =ᵐ[P] fun ω => W.W t ω - W.W 0 ω := by
      rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hmul him hip hiq hm' hp' hq' t]
      have h := stochasticIntegralBrownian_indIoc W ℱ hℱ (a := 0) (b := t) le_rfl ht'
        hm' hp' hq' ht'.le
      rwa [min_self, min_eq_left ht'.le] at h
    filter_upwards [hkey, hI, stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ
      (fun _ _ => (1 : ℝ)) hm hp hq (le_refl (0 : ℝ)), W.initial_zero] with ω h1 h2 h3 h4
    simp only [Pi.zero_apply] at h3
    linarith [h1, h2, h3, h4]

end Indicator

end LevyStochCalc.Brownian.Ito
