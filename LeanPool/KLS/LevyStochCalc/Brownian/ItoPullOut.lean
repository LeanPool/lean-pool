/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoIncrement

/-!
# Pulling a past weight inside an Itô integral over a window

A bounded `ℱ_a`-measurable weight times the Itô integral of an integrand supported in `(a, b]` is
the Itô integral of the weighted integrand: the weight times the indicator is itself a simple
integrand, so this is associativity against a simple integrand.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The simple integrand `V · 1_{(a, b]}`, for `0 < a < b` and a bounded measurable `V`. -/
noncomputable def stepIocMul (Ω) [MeasurableSpace Ω] {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (V : Ω → ℝ) (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) :
    SimplePredictable Ω b where
  N := 2
  partition := ![0, a, b]
  partition_zero := by simp
  partition_le_T := by simp
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    · simpa using ha
    · simpa using hab
  ξ := ![fun _ => 0, V]
  ξ_bounded := by
    intro i
    fin_cases i
    · exact ⟨0, fun ω => by norm_num⟩
    · exact hVb
  ξ_measurable := by
    intro i
    fin_cases i
    · exact measurable_const
    · exact hVm

/-- The simple integrand `V · 1_{(0, b]}`, for `0 < b` and a bounded measurable `V`. -/
noncomputable def stepIocMul₀ (Ω) [MeasurableSpace Ω] {b : ℝ} (hb : 0 < b)
    (V : Ω → ℝ) (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) :
    SimplePredictable Ω b where
  N := 1
  partition := ![0, b]
  partition_zero := by simp
  partition_le_T := by simp
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    simpa using hb
  ξ := ![V]
  ξ_bounded := by intro i; fin_cases i; exact hVb
  ξ_measurable := by intro i; fin_cases i; exact hVm

theorem stepIocMul_eval {a b : ℝ} (ha : 0 < a) (hab : a < b) {V : Ω → ℝ}
    (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) (s : ℝ) (ω : Ω) :
    (stepIocMul Ω ha hab V hVb hVm).eval s ω = V ω * indIoc Ω a b ω s := by
  have hrw : (stepIocMul Ω ha hab V hVb hVm).eval s ω
      = ∑ i : Fin 2, if (![0, a, b] : Fin 3 → ℝ) i.castSucc < s
            ∧ s ≤ (![0, a, b] : Fin 3 → ℝ) i.succ
          then (![fun _ => (0 : ℝ), V] : Fin 2 → Ω → ℝ) i ω else 0 := rfl
  rw [hrw, Fin.sum_univ_two]
  change _ = V ω * (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s
  by_cases h : a < s ∧ s ≤ b
  · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr h)]
    simp [h]
  · rw [Set.indicator_of_notMem fun hmem => h (Set.mem_Ioc.mp hmem)]
    show (if (0 : ℝ) < s ∧ s ≤ a then (0 : ℝ) else 0)
      + (if a < s ∧ s ≤ b then V ω else 0) = V ω * 0
    simp only [ite_self, zero_add]
    rw [ite_eq_right h]
    ring

theorem stepIocMul₀_eval {b : ℝ} (hb : 0 < b) {V : Ω → ℝ}
    (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) (s : ℝ) (ω : Ω) :
    (stepIocMul₀ Ω hb V hVb hVm).eval s ω = V ω * indIoc Ω 0 b ω s := by
  have hrw : (stepIocMul₀ Ω hb V hVb hVm).eval s ω
      = ∑ i : Fin 1, if (![0, b] : Fin 2 → ℝ) i.castSucc < s
            ∧ s ≤ (![0, b] : Fin 2 → ℝ) i.succ
          then (![V] : Fin 1 → Ω → ℝ) i ω else 0 := rfl
  rw [hrw, Fin.sum_univ_one]
  change _ = V ω * (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s
  by_cases h : (0 : ℝ) < s ∧ s ≤ b
  · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr h)]
    simp [h]
  · rw [Set.indicator_of_notMem fun hmem => h (Set.mem_Ioc.mp hmem)]
    show (if (0 : ℝ) < s ∧ s ≤ b then V ω else 0) = V ω * 0
    rw [ite_eq_right h]
    ring

theorem stepIocMul_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V) :
    ∀ i : Fin (stepIocMul Ω ha hab V hVb hVm).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIocMul Ω ha hab V hVb hVm).partition i.castSucc))
      ((stepIocMul Ω ha hab V hVb hVm).ξ i) := by
  intro i
  fin_cases i
  · exact MeasureTheory.stronglyMeasurable_const
  · exact hVa

theorem stepIocMul₀_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ} (hb : 0 < b)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ 0) V) :
    ∀ i : Fin (stepIocMul₀ Ω hb V hVb hVm).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIocMul₀ Ω hb V hVb hVm).partition i.castSucc))
      ((stepIocMul₀ Ω hb V hVb hVm).ξ i) := by
  intro i
  fin_cases i
  exact hVa

theorem stepIocMul_integralAgainst {a b : ℝ} (ha : 0 < a) (hab : a < b) {V : Ω → ℝ}
    (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (stepIocMul Ω ha hab V hVb hVm).integralAgainst M t ω
      = V ω * (M (min b t) ω - M (min a t) ω) := by
  have hrw : (stepIocMul Ω ha hab V hVb hVm).integralAgainst M t ω
      = ∑ i : Fin 2, (![fun _ => (0 : ℝ), V] : Fin 2 → Ω → ℝ) i ω
        * (M (min ((![0, a, b] : Fin 3 → ℝ) i.succ) t) ω
          - M (min ((![0, a, b] : Fin 3 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_two]
  simp

theorem stepIocMul₀_integralAgainst {b : ℝ} (hb : 0 < b) {V : Ω → ℝ}
    (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V) (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (stepIocMul₀ Ω hb V hVb hVm).integralAgainst M t ω
      = V ω * (M (min b t) ω - M (min 0 t) ω) := by
  have hrw : (stepIocMul₀ Ω hb V hVb hVm).integralAgainst M t ω
      = ∑ i : Fin 1, (![V] : Fin 1 → Ω → ℝ) i ω
        * (M (min ((![0, b] : Fin 2 → ℝ) i.succ) t) ω
          - M (min ((![0, b] : Fin 2 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_one]
  simp

/-- A bounded weight measurable before a window, times the window's indicator, is progressively
measurable. -/
theorem progressivelyMeasurable_mul_indIoc (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M)
    (hVm : Measurable V) (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * indIoc Ω a b ω s := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hfun : (fun ω s => V ω * indIoc Ω 0 b ω s)
        = fun ω s => (stepIocMul₀ Ω hab V hVb hVm).eval s ω := by
      funext ω s; rw [stepIocMul₀_eval]
    rw [hfun]
    exact (stepIocMul₀ Ω hab V hVb hVm).progressivelyMeasurable_eval ℱ
      (stepIocMul₀_adapt ℱ hab hVb hVm hVa)
  · have hfun : (fun ω s => V ω * indIoc Ω a b ω s)
        = fun ω s => (stepIocMul Ω ha' hab V hVb hVm).eval s ω := by
      funext ω s; rw [stepIocMul_eval]
    rw [hfun]
    exact (stepIocMul Ω ha' hab V hVb hVm).progressivelyMeasurable_eval ℱ
      (stepIocMul_adapt ℱ ha' hab hVb hVm hVa)

section PullOut

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **A past weight passes inside an Itô integral over a window.** For `V` bounded and
`ℱ_a`-measurable and an integrand restricted to `(a, b]`, multiplying by `V` outside the integral
is the same as multiplying the integrand by `V`. -/
theorem mul_stochasticIntegralBrownian_indIoc {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V)
    (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
    (hp : Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (him : Measurable (Function.uncurry fun ω s => indIoc Ω a b ω s * K ω s))
    (hip : Probability.ProgressivelyMeasurable ℱ fun ω s => indIoc Ω a b ω s * K ω s)
    (hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hvm : Measurable (Function.uncurry fun ω s => V ω * indIoc Ω a b ω s * K ω s))
    (hvp : Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * indIoc Ω a b ω s * K ω s)
    (hvq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖V ω * indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    (fun ω => V ω * stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => indIoc Ω a b ω s * K ω s) him hip hiq t ω)
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => V ω * indIoc Ω a b ω s * K ω s) hvm hvp hvq t := by
  have hloc := stochasticIntegralBrownian_indicator_Ioc W ℱ hℱ K hm hp hq ha hab him hip hiq ht
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hpt : ∀ (ω : Ω) (s : ℝ),
        (stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s
          = V ω * indIoc Ω 0 b ω s * K ω s := by
      intro ω s; rw [stepIocMul₀_eval]
    have hGeval : (fun ω s => (stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s)
        = fun ω s => V ω * indIoc Ω 0 b ω s * K ω s := by
      funext ω s; exact hpt ω s
    have hmm : Measurable (Function.uncurry fun ω s =>
        (stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s) := by rw [hGeval]; exact hvm
    have hmp : Probability.ProgressivelyMeasurable ℱ fun ω s =>
        (stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s := by rw [hGeval]; exact hvp
    have hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hvq T hT
    have hass := stochasticIntegralBrownian_integralAgainst W ℱ hℱ
      (stepIocMul₀ Ω hab V hVb hVm) (stepIocMul₀_adapt ℱ hab hVb hVm hVa) K hm hp hq
      hmm hmp hmq ht
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hGeval hmm hmp hmq hvm hvp hvq t] at hass
    refine Filter.EventuallyEq.trans ?_ hass
    filter_upwards [hloc] with ω hω
    rw [stepIocMul₀_integralAgainst]
    exact congrArg (fun x => V ω * x) hω
  · have hpt : ∀ (ω : Ω) (s : ℝ),
        (stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s
          = V ω * indIoc Ω a b ω s * K ω s := by
      intro ω s; rw [stepIocMul_eval]
    have hGeval : (fun ω s => (stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s)
        = fun ω s => V ω * indIoc Ω a b ω s * K ω s := by
      funext ω s; exact hpt ω s
    have hmm : Measurable (Function.uncurry fun ω s =>
        (stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s) := by rw [hGeval]; exact hvm
    have hmp : Probability.ProgressivelyMeasurable ℱ fun ω s =>
        (stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s := by rw [hGeval]; exact hvp
    have hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hvq T hT
    have hass := stochasticIntegralBrownian_integralAgainst W ℱ hℱ
      (stepIocMul Ω ha' hab V hVb hVm) (stepIocMul_adapt ℱ ha' hab hVb hVm hVa) K hm hp hq
      hmm hmp hmq ht
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hGeval hmm hmp hmq hvm hvp hvq t] at hass
    refine Filter.EventuallyEq.trans ?_ hass
    filter_upwards [hloc] with ω hω
    rw [stepIocMul_integralAgainst]
    exact congrArg (fun x => V ω * x) hω

end PullOut

end LevyStochCalc.Brownian.Ito
