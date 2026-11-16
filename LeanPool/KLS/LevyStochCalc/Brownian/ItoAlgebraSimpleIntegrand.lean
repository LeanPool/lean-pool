/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
-- Modified 2026-10-31 by the KLS formalization project: pass the existing
-- `AEStronglyMeasurable` witnesses now taken by `eLpNorm_two_rpow_eq_lintegral_sq`
-- (Mathlib v4.35.0 `eLpNorm` change); proof-only change.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoL2Completion

/-!
# Simple integrands as integrands of the `L²` Brownian Itô integral

A simple integrand is uniformly bounded in both variables, jointly measurable, square-integrable
on every time window and, when its coefficients are adapted to a filtration, progressively
measurable, so it is an admissible integrand for the `L²` Itô integral in its own right; the two
elementary integrals of adapted simple integrands obey the Itô isometry for their difference at
an intermediate time, and the `L²` Itô integral of a simple integrand agrees almost everywhere
with its elementary integral.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- A simple integrand is uniformly bounded in both variables. -/
theorem SimplePredictable.exists_eval_bound {T : ℝ} (G : SimplePredictable Ω T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ω, |G.eval s ω| ≤ B := by
  classical
  choose M hM using G.ξ_bounded
  refine ⟨∑ i : Fin G.N, max (M i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _,
    fun s ω => ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  by_cases h : G.partition i.castSucc < s ∧ s ≤ G.partition i.succ
  · rw [ite_eq_left h]; exact (hM i ω).trans (le_max_left _ _)
  · rw [ite_eq_right h, abs_zero]; exact le_max_right _ _

/-- The `L²`-mass of a simple integrand over any time window is finite. -/
theorem SimplePredictable.lintegral_eval_sq_lt_top {T : ℝ} (G : SimplePredictable Ω T)
    (P : Measure Ω) [IsProbabilityMeasure P] (T' : ℝ) (_hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  obtain ⟨B, hB0, hB⟩ := G.exists_eval_bound
  have hpt : ∀ s ω, ((‖G.eval s ω‖₊ : ℝ≥0∞)) ^ 2 ≤ (ENNReal.ofReal B) ^ 2 := by
    intro s ω
    refine pow_le_pow_left' ?_ 2
    have hx : ‖G.eval s ω‖ ≤ B := (Real.norm_eq_abs _).le.trans (hB s ω)
    calc (‖G.eval s ω‖₊ : ℝ≥0∞)
        = ENNReal.ofReal ‖G.eval s ω‖ := by
          rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; rfl
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hx
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T',
        (ENNReal.ofReal B) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt s ω
    _ < ⊤ := by
        rw [lintegral_const, setLIntegral_const, Real.volume_Icc, measure_univ, mul_one]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          ENNReal.ofReal_lt_top


/-- A finite sum of step processes `1_{(aᵢ, bᵢ]}(s) · ξᵢ ω`, with `ξᵢ` measurable for
`ℱ (aᵢ)`, is progressively measurable. -/
theorem progressivelyMeasurable_sum_indicator_Ioc
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {n : ℕ} (a b : Fin n → ℝ)
    (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ (a i)) (ξ i)) :
    Probability.ProgressivelyMeasurable ℱ
      (fun ω s => ∑ i : Fin n, (Set.Ioc (a i) (b i)).indicator (fun _ => ξ i ω) s) := by
  classical
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator
        (fun s => ∑ i : Fin n, (Set.Ioc (a i) (b i)).indicator (fun _ => ξ i p.1) s) p.2)
      = fun p : Ω × ℝ => ∑ i : Fin n,
        (Set.univ ×ˢ (Set.Ioc (a i) (b i) ∩ Set.Iic t)).indicator
          (fun q : Ω × ℝ => ξ i q.1) p := by
    funext p
    by_cases hp : p.2 ≤ t
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hp)]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : p.2 ∈ Set.Ioc (a i) (b i)
      · have hmem : p ∈ Set.univ ×ˢ (Set.Ioc (a i) (b i) ∩ Set.Iic t) :=
          ⟨Set.mem_univ _, hi, Set.mem_Iic.mpr hp⟩
        rw [Set.indicator_of_mem hi, Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem]
        rintro ⟨-, hmem, -⟩
        exact hi hmem
    · rw [Set.indicator_of_notMem (by simpa using hp)]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [Set.indicator_of_notMem]
      rintro ⟨-, -, hmem⟩
      exact hp (Set.mem_Iic.mp hmem)
  let : MeasurableSpace Ω := ℱ t
  rw [key]
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ => ?_
  by_cases hi : a i < t
  · refine MeasureTheory.StronglyMeasurable.indicator ?_
      (MeasurableSet.univ.prod (measurableSet_Ioc.inter measurableSet_Iic))
    exact ((hξ i).mono (ℱ.mono hi.le)).comp_measurable measurable_fst
  · have hempty : Set.Ioc (a i) (b i) ∩ Set.Iic t = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun s hs =>
        absurd (lt_of_lt_of_le hs.1.1 hs.2) (not_lt.mpr (not_lt.mp hi))
    rw [hempty, Set.prod_empty, Set.indicator_empty]
    exact MeasureTheory.stronglyMeasurable_const

/-- A simple integrand with `ℱ`-adapted coefficients is progressively measurable. -/
theorem SimplePredictable.progressivelyMeasurable_eval {T : ℝ} (G : SimplePredictable Ω T)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i)) :
    Probability.ProgressivelyMeasurable ℱ (fun ω s => G.eval s ω) := by
  have hfun : (fun ω s => G.eval s ω)
      = fun ω s => ∑ i : Fin G.N,
        (Set.Ioc (G.partition i.castSucc) (G.partition i.succ)).indicator
          (fun _ => G.ξ i ω) s := by
    funext ω s; exact eval_eq_sum_indicator G s ω
  rw [hfun]
  exact progressivelyMeasurable_sum_indicator_Ioc ℱ _ _ _ h_adapt


/-- Difference isometry at an intermediate time for two adapted simple integrands whose
horizons need not agree. -/
theorem simpleIntegral_diff_isometry_of_adapted
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T₁ T₂ : ℝ} (G₁ : SimplePredictable Ω T₁) (G₂ : SimplePredictable Ω T₂)
    (h₁ : ∀ i : Fin G₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G₁.partition i.castSucc)) (G₁.ξ i))
    (h₂ : ∀ i : Fin G₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G₂.partition i.castSucc)) (G₂.ξ i))
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω,
        (‖simpleIntegral W G₁ t ω - simpleIntegral W G₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖G₁.eval s ω - G₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set K : ℝ :=
    max (G₁.partition (Fin.last G₁.N)) (G₂.partition (Fin.last G₂.N)) + 1 with hK
  have hK₁ : G₁.partition (Fin.last G₁.N) < K := by
    have := le_max_left (G₁.partition (Fin.last G₁.N)) (G₂.partition (Fin.last G₂.N))
    rw [hK]; linarith
  have hK₂ : G₂.partition (Fin.last G₂.N) < K := by
    have := le_max_right (G₁.partition (Fin.last G₁.N)) (G₂.partition (Fin.last G₂.N))
    rw [hK]; linarith
  have h_eq : (G₁.appendInterval hK₁).partition (Fin.last (G₁.appendInterval hK₁).N)
      = (G₂.appendInterval hK₂).partition (Fin.last (G₂.appendInterval hK₂).N) :=
    (G₁.appendInterval_partition_last hK₁).trans (G₂.appendInterval_partition_last hK₂).symm
  have hiso := simpleIntegral_intermediate_diff_isometry W ℱ hℱ (G₁.appendInterval hK₁)
    (G₂.appendInterval hK₂) h_eq (G₁.appendInterval_adapt ℱ hK₁ h₁)
    (G₂.appendInterval_adapt ℱ hK₂ h₂) ht
  have hL : ∫⁻ ω,
        (‖simpleIntegral W G₁ t ω - simpleIntegral W G₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖simpleIntegral W (G₁.appendInterval hK₁) t ω
          - simpleIntegral W (G₂.appendInterval hK₂) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    lintegral_congr fun ω => by
      rw [G₁.appendInterval_simpleIntegral W hK₁ t ω,
        G₂.appendInterval_simpleIntegral W hK₂ t ω]
  have hR : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖G₁.eval s ω - G₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖(G₁.appendInterval hK₁).eval s ω
          - (G₂.appendInterval hK₂).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    lintegral_congr fun ω => MeasureTheory.setLIntegral_congr_fun measurableSet_Icc fun s _ => by
      rw [G₁.appendInterval_eval hK₁ s ω, G₂.appendInterval_eval hK₂ s ω]
  rw [hL, hR]; exact hiso


/-- A simple integrand is jointly measurable in the form the integral consumes. -/
theorem SimplePredictable.measurable_uncurry_eval {T : ℝ} (G : SimplePredictable Ω T) :
    Measurable (Function.uncurry fun ω s => G.eval s ω) := G.eval_jointly_measurable

/-- A simple integrand times a jointly measurable process is jointly measurable. -/
theorem SimplePredictable.measurable_uncurry_eval_mul {T : ℝ} (G : SimplePredictable Ω T)
    {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry fun ω s => G.eval s ω * H ω s) :=
  G.eval_jointly_measurable.mul hm

/-- A simple integrand with adapted coefficients times a progressively measurable process is
progressively measurable. -/
theorem SimplePredictable.progressivelyMeasurable_eval_mul {T : ℝ} (G : SimplePredictable Ω T)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {H : Ω → ℝ → ℝ} (hp : Probability.ProgressivelyMeasurable ℱ H) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω * H ω s :=
  (G.progressivelyMeasurable_eval ℱ h_adapt).mul hp

/-- A simple integrand times a square-integrable process is square-integrable on every
window. -/
theorem SimplePredictable.lintegral_eval_mul_sq_lt_top {T : ℝ} (G : SimplePredictable Ω T)
    {P : Measure Ω} {H : Ω → ℝ → ℝ}
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T' : ℝ) (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  obtain ⟨B, hB0, hB⟩ := G.exists_eval_bound
  have hbd : ∀ s ω, (‖G.eval s ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal B := by
    intro s ω
    calc (‖G.eval s ω‖₊ : ℝ≥0∞)
        = ENNReal.ofReal ‖G.eval s ω‖ := by
          rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; rfl
      _ ≤ ENNReal.ofReal B :=
          ENNReal.ofReal_le_ofReal ((Real.norm_eq_abs _).le.trans (hB s ω))
  have hpt : ∀ s ω, (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal B ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro s ω
    rw [nnnorm_mul, ENNReal.coe_mul, mul_pow]
    gcongr
    exact hbd s ω
  have hne : ENNReal.ofReal B ^ 2 ≠ ⊤ := (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          ENNReal.ofReal B ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt s ω
    _ = ENNReal.ofReal B ^ 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [← MeasureTheory.lintegral_const_mul' _ _ hne]
        exact lintegral_congr fun ω => MeasureTheory.lintegral_const_mul' _ _ hne
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hne) (hq T' hT')

section EvalSimple

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (hm : Measurable (Function.uncurry fun ω s => G.eval s ω))
  (hp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ h_adapt in
/-- **The `L²` Itô integral of a simple integrand is its elementary integral.** -/
theorem stochasticIntegralBrownian_eval_simple {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t
      =ᵐ[P] simpleIntegral W G t := by
  classical
  have hIn : ∀ n : ℕ, Measurable
      (simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t) := by
    intro n
    unfold simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n).ξ_measurable i).mul
        ((W.measurable_eval _).sub (W.measurable_eval _))
  have hIG : Measurable (simpleIntegral W G t) := by
    unfold simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      (G.ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hSI : Measurable
      (stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t) :=
    ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ (fun ω s => G.eval s ω) hm
      hp hq t).mono (ℱ.le t)).measurable
  -- the master integrals converge to the elementary integral of `G`
  have hA : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t ω
        - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (nhds 0) := by
    refine (masterApprox_eval_tendsto (t := t) ℱ (fun ω s => G.eval s ω) hm hp hq).congr
      fun n => ?_
    rw [simpleIntegral_diff_isometry_of_adapted W ℱ hℱ _ G
      (masterApprox_adapt ℱ (fun ω s => G.eval s ω) hm hp hq n) h_adapt ht]
    refine lintegral_congr fun ω =>
      MeasureTheory.setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    rw [← nnnorm_neg, neg_sub]
  -- and to the `L²` Itô integral
  have hconv : ∀ g : Ω → ℝ, MeasureTheory.AEStronglyMeasurable g P →
      MeasureTheory.eLpNorm g 2 P * MeasureTheory.eLpNorm g 2 P
        = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro g hg
    rw [← eLpNorm_two_rpow_eq_lintegral_sq g hg,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
  have hB : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t ω
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (nhds 0) := by
    have h := masterApprox_tendsto_L2 W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq ht
    have h2 := ENNReal.Tendsto.mul h (Or.inr (by simp)) h (Or.inr (by simp))
    simpa using h2.congr fun n => hconv _ ((hIn n).sub hSI).aestronglyMeasurable
  -- squeeze
  have hle : ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
      hq t ω - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ 0 := by
    have hlim : Filter.Tendsto (fun n => 2 * ((∫⁻ ω,
        (‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t ω
          - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
            hq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        + ∫⁻ ω, (‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp
            hq n) t ω - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P))
        Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul (a := 2) (hB.add hA) (Or.inr (by simp))
      simpa using this
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
    calc ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
          hq t ω - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, 2 * ((‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm
              hp hq n) t ω - stochasticIntegralBrownian W ℱ hℱ
              (fun ω s => G.eval s ω) hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2
            + (‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp
              hq n) t ω - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          have hrw : stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
                hq t ω - simpleIntegral W G t ω
              = -(simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp
                  hq n) t ω - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω)
                  hm hp hq t ω)
                + (simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp
                  hq n) t ω - simpleIntegral W G t ω) := by ring
          rw [hrw]
          refine le_trans (sq_nnnorm_add_le_two_mul_brownian _ _) ?_
          rw [nnnorm_neg]
      _ = 2 * ((∫⁻ ω, (‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm
              hp hq n) t ω - stochasticIntegralBrownian W ℱ hℱ
              (fun ω s => G.eval s ω) hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
            + ∫⁻ ω, (‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp
              hq n) t ω - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) := by
          have hm2 : AEMeasurable (fun ω => (‖simpleIntegral W (masterApprox ℱ
              (fun ω s => G.eval s ω) hm hp hq n) t ω
                - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
                  hq t ω‖₊ : ℝ≥0∞) ^ 2) P :=
            ((((hIn n).sub hSI).nnnorm).coe_nnreal_ennreal).pow_const 2 |>.aemeasurable
          rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
            MeasureTheory.lintegral_add_left' hm2]
  have hzero : ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm
      hp hq t ω - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 :=
    le_antisymm hle bot_le
  have hmeas : Measurable fun ω => (‖stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => G.eval s ω) hm hp hq t ω
        - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 :=
    (((hSI.sub hIG).nnnorm).coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hzero] with ω hω
  have h0 : (‖stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t ω
      - simpleIntegral W G t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa using hω
  simpa [sub_eq_zero] using h0

end EvalSimple

end LevyStochCalc.Brownian.Ito
