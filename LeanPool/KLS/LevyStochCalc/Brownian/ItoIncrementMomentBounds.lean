/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system (module
-- header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with source adaptations
-- (deprecated names, proof-context visibility, the v4.35.0 `eLpNorm`/`MemLp` API,
-- `continuous_abs.measurable.comp` for the no longer reachable `Measurable.abs`) listed in
-- vendor/port.patch.
-- Modified 2026-10-31 by the KLS formalization project: pass the existing
-- `AEStronglyMeasurable` witnesses now taken by `eLpNorm_two_rpow_eq_lintegral_sq`
-- (Mathlib v4.35.0 `eLpNorm` change); proof-only change.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoIncrementMomentRestrict

/-!
# Moments of an increment of the Itô integral

The fourth moment of `∫_a^b H dW` for an integrand bounded by `C` is at most
`(6 + c)·C⁴·(b − a)²`, with `c` the fourth moment of the standard Gaussian, the second moment is
at most `C²·(b − a)`, and interpolating between the two by `2λ|y|³ ≤ λ²y² + y⁴` at `λ = √(b − a)`
bounds the third absolute moment. The fourth-moment bound is the per-tile variance budget of
`LevyStochCalc.Brownian.Ito.SimplePredictable.varClock` applied to simple approximants of
`1_{(a, b]}·H` that themselves vanish off `(a, b]`.

## Main statements

* `lintegral_stochasticIntegralBrownian_pow_four_le_Ioc` — the fourth-moment bound for an
  integrand supported in `(a, b]`.
* `lintegral_stochasticIntegralBrownian_sub_pow_four_le` —
  `𝔼|∫_a^b H dW|⁴ ≤ (6 + c)·C⁴·(b − a)²` for an integrand bounded by `C`.
* `lintegral_stochasticIntegralBrownian_sub_sq_le` — `𝔼|∫_a^b H dW|² ≤ C²·(b − a)`.
* `integral_abs_sub_pow_three_le` —
  `𝔼|∫_a^b H dW|³ ≤ ((C² + (6 + c)C⁴)/2)·(b − a)·√(b − a)`.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section IncrementBound

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

/-- A process depending only on time is progressively measurable as soon as it is Borel. -/
theorem progressivelyMeasurable_of_time {g : ℝ → ℝ} (hg : Measurable g) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) s => g s) := by
  intro t
  have h : Measurable[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance]
      (fun p : Ω × ℝ => (Set.Iic t).indicator g p.2) :=
    (hg.indicator measurableSet_Iic).comp measurable_snd
  exact h.stronglyMeasurable

include hℱ in
/-- **Fourth-moment bound for the `L²` Itô integral of an integrand supported in `(a, b]`.**
The bound sees only the length of the support. -/
theorem lintegral_stochasticIntegralBrownian_pow_four_le_Ioc
    (F : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry F))
    (hp : Probability.ProgressivelyMeasurable ℱ F)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCF : ∀ ω s, |F ω s| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hsupp : ∀ ω s, s ∉ Set.Ioc a b → F ω s = 0) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) := by
  classical
  have hb : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  choose G0 hG0adapt hG0within using fun n : ℕ =>
    exists_adaptedSimple_within ℱ F hm hp hb (hq b hb)
      (show (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ from ENNReal.inv_pos.mpr
        (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩))
  have hGadapt : ∀ n, ∀ i : Fin ((G0 n).truncate C).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (((G0 n).truncate C).partition i.castSucc)) (((G0 n).truncate C).ξ i) :=
    fun n => SimplePredictable.truncate_adapt ℱ (G0 n) C (hG0adapt n)
  have hGbdd : ∀ n, ∀ (i : Fin ((G0 n).truncate C).N) (ω : Ω),
      |((G0 n).truncate C).ξ i ω| ≤ C := fun n i ω => (G0 n).abs_truncate_xi_le hC0 i ω
  choose T3 Q hQadapt hQeval hQxi using fun n : ℕ =>
    SimplePredictable.exists_restrict_Ioc W ℱ ((G0 n).truncate C) (hGadapt n) hC0
      (hGbdd n) ha hab
  -- the restricted approximants are bounded by `C` and vanish off `(a, b]`
  have hQC : ∀ (n : ℕ) (j : Fin (Q n).N) (ω : Ω), |(Q n).ξ j ω| ≤ C := by
    intro n j ω
    refine (hQxi n j ω).trans ?_
    by_cases h : a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]; exact hC0
  have hQz : ∀ (n : ℕ) (j : Fin (Q n).N) (ω : Ω),
      ¬(a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b) → (Q n).ξ j ω = 0 := by
    intro n j ω h
    have := (hQxi n j ω).trans (le_of_eq (ite_eq_right h))
    exact abs_nonpos_iff.mp this
  -- their elementary integrals at `b` are the ones the variance budget bounds
  have hQsimp : ∀ (n : ℕ) (ω : Ω),
      simpleIntegral W (Q n) b ω = simpleIntegral W (Q n) (T3 n) ω :=
    fun n ω => (Q n).simpleIntegral_eq_of_support W (hQz n) le_rfl ω
  have hQbound : ∀ n : ℕ, ∫⁻ ω, (‖simpleIntegral W (Q n) b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) := by
    intro n
    simp_rw [hQsimp n]
    refine le_trans ((Q n).lintegral_simpleIntegral_pow_four_le_varClock W ℱ hℱ (hQadapt n)
      hC0 (hQC n) (c := fun j => if a ≤ (Q n).partition j.castSucc
        ∧ (Q n).partition j.succ ≤ b then C else 0) (hQxi n)) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hV := (Q n).varClock_le_Ioc (a := a) (b := b) (C := C) hab.le
    have hV0 := (Q n).varClock_nonneg
      (fun j => if a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b then C else 0)
      (Q n).N
    have hcg : (0 : ℝ) ≤ 6 + gaussianFourthMoment := by
      linarith [gaussianFourthMoment_nonneg]
    have hsq : (Q n).varClock
        (fun j => if a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b then C else 0)
        (Q n).N ^ 2 ≤ (C ^ 2 * (b - a)) ^ 2 := by
      nlinarith [hV, hV0]
    calc (6 + gaussianFourthMoment) * (Q n).varClock
            (fun j => if a ≤ (Q n).partition j.castSucc
              ∧ (Q n).partition j.succ ≤ b then C else 0) (Q n).N ^ 2
        ≤ (6 + gaussianFourthMoment) * (C ^ 2 * (b - a)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hcg
      _ = (6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by ring
  -- the restricted approximants still approximate `F`
  have hQwithin : ∀ n : ℕ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖(Q n).eval s ω - F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    refine le_trans ?_ (hG0within n).le
    refine lintegral_mono fun ω => lintegral_mono fun s => ?_
    have hle : ‖(Q n).eval s ω - F ω s‖₊ ≤ ‖F ω s - (G0 n).eval s ω‖₊ := by
      rw [← NNReal.coe_le_coe]
      simp only [coe_nnnorm, Real.norm_eq_abs]
      have hstep : |(Q n).eval s ω - F ω s|
          ≤ |((G0 n).truncate C).eval s ω - F ω s| := by
        rw [hQeval n s ω]
        by_cases hs : s ∈ Set.Ioc a b
        · rw [Set.indicator_of_mem hs]
          simp
        · rw [Set.indicator_of_notMem hs, zero_mul, hsupp ω s hs]
          simp
      refine hstep.trans ?_
      rw [(G0 n).truncate_eval hC0 s ω, abs_sub_comm (F ω s)]
      exact abs_clamp_sub_le hC0 (hCF ω s)
    exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr hle) 2
  have htol : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
    have h := ENNReal.tendsto_inv_nat_nhds_zero.comp hg
    refine h.congr fun n => ?_
    simp [Nat.cast_add_one]
  have hsq : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖simpleIntegral W (Q n) b ω
        - stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htol
      (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall fun n => ?_)
    rw [isometry_simple_sub_stochasticIntegralBrownian W ℱ hℱ (Q n) (hQadapt n) F hm hp hq hb]
    exact hQwithin n
  have heL : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
      (fun ω => simpleIntegral W (Q n) b ω
        - stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω) 2 P) Filter.atTop (nhds 0) := by
    have hrw : ∀ n, MeasureTheory.eLpNorm
        (fun ω => simpleIntegral W (Q n) b ω
          - stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω) 2 P
        = (∫⁻ ω, (‖simpleIntegral W (Q n) b ω
            - stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
              ^ ((2 : ℝ))⁻¹ := by
      intro n
      rw [← eLpNorm_two_rpow_eq_lintegral_sq]
      · exact (ENNReal.rpow_rpow_inv (by norm_num) _).symm
      · have hQm : Measurable (simpleIntegral W (Q n) b) := by
          unfold simpleIntegral
          exact Finset.measurable_sum _ fun i _ =>
            ((Q n).ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
        exact (hQm.sub ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ F hm hp hq b).mono
          (ℱ.le b)).measurable).aestronglyMeasurable
    simp_rw [hrw]
    have h := (ENNReal.continuous_rpow_const (y := ((2 : ℝ))⁻¹)).tendsto 0 |>.comp hsq
    simpa [Function.comp_def,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < ((2 : ℝ))⁻¹)] using h
  have hmeasG : ∀ n, Measurable (fun ω => simpleIntegral W (Q n) b ω) := by
    intro n
    unfold simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((Q n).ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hTIM : MeasureTheory.TendstoInMeasure P
      (fun n ω => simpleIntegral W (Q n) b ω) Filter.atTop
      (stochasticIntegralBrownian W ℱ hℱ F hm hp hq b) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) heL
  obtain ⟨ns, -, hns_ae⟩ := hTIM.exists_seq_tendsto_ae
  have hcont : Continuous fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 4 := by
    have hfun : (fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 4)
        = fun x : ℝ => ((‖x‖₊ ^ 4 : ℝ≥0) : ℝ≥0∞) := by
      funext x; rw [ENNReal.coe_pow]
    rw [hfun]
    exact ENNReal.continuous_coe.comp (continuous_nnnorm.pow 4)
  have hfatou : ∫⁻ ω,
      (‖stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ Filter.liminf (fun k => ∫⁻ ω,
        (‖simpleIntegral W (Q (ns k)) b ω‖₊ : ℝ≥0∞) ^ 4 ∂P) Filter.atTop := by
    have h1 : ∀ᵐ ω ∂P,
        (‖stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4
        = Filter.liminf (fun k =>
            (‖simpleIntegral W (Q (ns k)) b ω‖₊ : ℝ≥0∞) ^ 4) Filter.atTop := by
      filter_upwards [hns_ae] with ω hω
      exact ((hcont.tendsto _).comp hω).liminf_eq.symm
    rw [lintegral_congr_ae h1]
    exact lintegral_liminf_le fun k => (hcont.measurable.comp (hmeasG (ns k)))
  exact hfatou.trans (Filter.liminf_le_of_frequently_le
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun k => hQbound (ns k))))


/-- Restricting an integrand to `(a, b]` preserves joint measurability. -/
theorem measurable_uncurry_indicator_Ioc_mul (H : Ω → ℝ → ℝ)
    (hm : Measurable (Function.uncurry H)) (a b : ℝ) :
    Measurable (Function.uncurry fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s) :=
  (((measurable_const.indicator measurableSet_Ioc).comp measurable_snd)).mul hm

/-- Restricting an integrand to `(a, b]` preserves progressive measurability. -/
theorem progressivelyMeasurable_indicator_Ioc_mul
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (H : Ω → ℝ → ℝ)
    (hp : Probability.ProgressivelyMeasurable ℱ H) (a b : ℝ) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s :=
  (progressivelyMeasurable_of_time ℱ (measurable_const.indicator measurableSet_Ioc)).mul hp

omit [MeasurableSpace Ω] in
/-- Restricting an integrand to `(a, b]` cannot increase its absolute value. -/
theorem abs_indicator_Ioc_mul_le (H : Ω → ℝ → ℝ)
    (a b : ℝ) (ω : Ω) (s : ℝ) :
    |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s| ≤ |H ω s| := by
  by_cases hs : s ∈ Set.Ioc a b
  · rw [Set.indicator_of_mem hs, one_mul]
  · rw [Set.indicator_of_notMem hs, zero_mul, abs_zero]
    exact abs_nonneg _

/-- Restricting an integrand to `(a, b]` preserves square integrability. -/
theorem lintegral_sq_indicator_Ioc_mul_lt_top {P : Measure Ω}
    (H : Ω → ℝ → ℝ)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (a b : ℝ) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T hT
  refine lt_of_le_of_lt ?_ (hq T hT)
  refine lintegral_mono fun ω => lintegral_mono fun s => ?_
  refine pow_le_pow_left' (ENNReal.coe_le_coe.mpr ?_) 2
  rw [← NNReal.coe_le_coe]
  simpa [Real.norm_eq_abs] using abs_indicator_Ioc_mul_le H a b ω s

include hℱ in
/-- **Fourth moment of an increment of the `L²` Itô integral.** For an integrand bounded by `C`,

  `𝔼|∫_a^b H dW|⁴ ≤ (6 + c)·C⁴·(b − a)²`,

with `c` the fourth moment of the standard Gaussian. -/
theorem lintegral_stochasticIntegralBrownian_sub_pow_four_le
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) := by
  classical
  have hb : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  have hFle : ∀ (ω : Ω) (s : ℝ),
      |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s| ≤ |H ω s| :=
    fun ω s => abs_indicator_Ioc_mul_le H a b ω s
  have hmF := measurable_uncurry_indicator_Ioc_mul H hm a b
  have hpF := progressivelyMeasurable_indicator_Ioc_mul ℱ H hp a b
  have hqF := lintegral_sq_indicator_Ioc_mul_lt_top (P := P) H hq a b
  have hCF : ∀ (ω : Ω) (s : ℝ),
      |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s| ≤ C :=
    fun ω s => (hFle ω s).trans (hCH ω s)
  have hsupp : ∀ (ω : Ω) (s : ℝ), s ∉ Set.Ioc a b →
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s = 0 := by
    intro ω s hs
    rw [Set.indicator_of_notMem hs, zero_mul]
  have hloc := stochasticIntegralBrownian_indicator_Ioc W ℱ hℱ H hm hp hq ha hab hmF hpF hqF hb
  rw [min_self, min_eq_left hab.le] at hloc
  have hcongr : ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      = ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s)
          hmF hpF hqF b ω‖₊ : ℝ≥0∞) ^ 4 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hloc] with ω hω
    rw [hω]
  rw [hcongr]
  exact lintegral_stochasticIntegralBrownian_pow_four_le_Ioc W ℱ hℱ _ hmF hpF hqF hC0 hCF
    ha hab hsupp

include hℱ in
/-- **Second moment of an increment of the `L²` Itô integral.** For an integrand bounded by `C`,
`𝔼|∫_a^b H dW|² ≤ C²·(b − a)`. -/
theorem lintegral_stochasticIntegralBrownian_sub_sq_le
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (C ^ 2 * (b - a)) := by
  classical
  have hb : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  have hFle : ∀ (ω : Ω) (s : ℝ),
      |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s| ≤ |H ω s| :=
    fun ω s => abs_indicator_Ioc_mul_le H a b ω s
  have hmF := measurable_uncurry_indicator_Ioc_mul H hm a b
  have hpF := progressivelyMeasurable_indicator_Ioc_mul ℱ H hp a b
  have hqF := lintegral_sq_indicator_Ioc_mul_lt_top (P := P) H hq a b
  have hloc := stochasticIntegralBrownian_indicator_Ioc W ℱ hℱ H hm hp hq ha hab hmF hpF hqF hb
  rw [min_self, min_eq_left hab.le] at hloc
  have hcongr : ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s)
          hmF hpF hqF b ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hloc] with ω hω
    rw [hω]
  rw [hcongr, isometry_stochasticIntegralBrownian W ℱ hℱ _ hmF hpF hqF hb]
  -- the restricted integrand has `L²` mass at most `C²(b − a)` on every path
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
      ≤ ENNReal.ofReal (C ^ 2 * (b - a)) := by
    intro ω
    have hptw : ∀ s : ℝ,
        (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2
          ≤ (Set.Ioc a b).indicator (fun _ => ENNReal.ofReal (C ^ 2)) s := by
      intro s
      by_cases hs : s ∈ Set.Ioc a b
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, one_mul]
        have h1 : (‖H ω s‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal C := by
          rw [ENNReal.ofReal_eq_coe_nnreal hC0]
          refine ENNReal.coe_le_coe.mpr ?_
          rw [← NNReal.coe_le_coe]
          simpa [Real.norm_eq_abs] using hCH ω s
        calc (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal C ^ 2 := pow_le_pow_left' h1 2
          _ = ENNReal.ofReal (C ^ 2) := (ENNReal.ofReal_pow hC0 2).symm
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, zero_mul]
        simp
    calc ∫⁻ s in Set.Icc (0 : ℝ) b,
          (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
        ≤ ∫⁻ s in Set.Icc (0 : ℝ) b,
            (Set.Ioc a b).indicator (fun _ => ENNReal.ofReal (C ^ 2)) s ∂volume :=
          lintegral_mono hptw
      _ ≤ ∫⁻ s, (Set.Ioc a b).indicator (fun _ => ENNReal.ofReal (C ^ 2)) s ∂volume :=
          MeasureTheory.setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (C ^ 2) * volume (Set.Ioc a b) := by
          rw [lintegral_indicator measurableSet_Ioc, MeasureTheory.setLIntegral_const]
      _ = ENNReal.ofReal (C ^ 2 * (b - a)) := by
          rw [Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity)]
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ω : Ω, ENNReal.ofReal (C ^ 2 * (b - a)) ∂P := lintegral_mono hinner
    _ = ENNReal.ofReal (C ^ 2 * (b - a)) := by simp

end IncrementBound


/-- A measurable function with finite `lintegral` of its norm is integrable. -/
theorem integrable_of_lintegral_nnnorm_lt_top {P : Measure Ω} {f : Ω → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f P)
    (h : ∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ∂P < ⊤) : MeasureTheory.Integrable f P := by
  refine ⟨hf, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  simpa only [enorm_eq_nnnorm] using h

/-- A pointwise-nonnegative integrand is bounded through its `lintegral`. -/
theorem integral_le_of_lintegral_ofReal_le {P : Measure Ω} {f : Ω → ℝ}
    (hint : MeasureTheory.Integrable f P) (hnn : ∀ ω, 0 ≤ f ω) {K : ℝ} (hK : 0 ≤ K)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal K) : ∫ ω, f ω ∂P ≤ K := by
  rw [← ENNReal.ofReal_le_ofReal_iff hK,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
  exact h

section ThirdMoment

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ in
/-- The increment of the `L²` Itô integral is measurable. -/
theorem measurable_sub_stochasticIntegralBrownian (a b : ℝ) :
    Measurable fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω :=
  (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq b).mono
      (ℱ.le b)).measurable).sub
    (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq a).mono
      (ℱ.le a)).measurable)

include hℱ hC0 hCH in
/-- The fourth power of an increment is integrable, with the fourth-moment bound. -/
theorem integral_sub_pow_four_le {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MeasureTheory.Integrable (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4) P
      ∧ ∫ ω, (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4 ∂P
        ≤ (6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by
  have hmeas := measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq a b
  have hbound := lintegral_stochasticIntegralBrownian_sub_pow_four_le W ℱ hℱ H hm hp hq
    hC0 hCH ha hab
  have hpt : ∀ ω : Ω, ENNReal.ofReal ((stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4)
      = (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 := by
    have key : ∀ x : ℝ, ENNReal.ofReal (x ^ 4) = (‖x‖₊ : ℝ≥0∞) ^ 4 := by
      intro x
      have h1 : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal |x| := by
        rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
        exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
      rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
    exact fun ω => key _
  have hnn : ∀ ω : Ω, (0 : ℝ) ≤ (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4 := fun ω => by positivity
  have hint : MeasureTheory.Integrable
      (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4) P := by
    refine integrable_of_lintegral_nnnorm_lt_top
      (hmeas.pow_const 4).aestronglyMeasurable ?_
    have hrw : ∀ ω : Ω, ((‖(stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4‖₊ : ℝ≥0∞))
        = (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 := by
      intro ω
      rw [nnnorm_pow, ENNReal.coe_pow]
    simp_rw [hrw]
    exact lt_of_le_of_lt hbound (by simp)
  have hKnn : (0 : ℝ) ≤ (6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith [gaussianFourthMoment_nonneg]) (by positivity))
      (by positivity)
  refine ⟨hint, integral_le_of_lintegral_ofReal_le hint hnn hKnn ?_⟩
  simp_rw [hpt]
  exact hbound

include hℱ hC0 hCH in
/-- The square of an increment is integrable, with the second-moment bound. -/
theorem integral_sub_sq_le {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MeasureTheory.Integrable (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) P
      ∧ ∫ ω, (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2 ∂P
        ≤ C ^ 2 * (b - a) := by
  have hmeas := measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq a b
  have hbound := lintegral_stochasticIntegralBrownian_sub_sq_le W ℱ hℱ H hm hp hq
    hC0 hCH ha hab
  have hpt : ∀ ω : Ω, ENNReal.ofReal ((stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2)
      = (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 := by
    have key : ∀ x : ℝ, ENNReal.ofReal (x ^ 2) = (‖x‖₊ : ℝ≥0∞) ^ 2 := by
      intro x
      have h1 : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal |x| := by
        rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
        exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
      rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2)]
    exact fun ω => key _
  have hnn : ∀ ω : Ω, (0 : ℝ) ≤ (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2 := fun ω => by positivity
  have hint : MeasureTheory.Integrable
      (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) P := by
    refine integrable_of_lintegral_nnnorm_lt_top
      (hmeas.pow_const 2).aestronglyMeasurable ?_
    have hrw : ∀ ω : Ω, ((‖(stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2‖₊ : ℝ≥0∞))
        = (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro ω
      rw [nnnorm_pow, ENNReal.coe_pow]
    simp_rw [hrw]
    exact lt_of_le_of_lt hbound (by simp)
  refine ⟨hint, integral_le_of_lintegral_ofReal_le hint hnn (by positivity) ?_⟩
  simp_rw [hpt]
  exact hbound

include hℱ hC0 hCH in
/-- **Third absolute moment of an increment of the `L²` Itô integral.** For an integrand
bounded by `C`, `𝔼|∫_a^b H dW|³ ≤ ((C² + (6 + c)C⁴)/2)·(b − a)·√(b − a)`. -/
theorem integral_abs_sub_pow_three_le {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MeasureTheory.Integrable (fun ω => |stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3) P
      ∧ ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3 ∂P
        ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * ((b - a) * Real.sqrt (b - a)) := by
  have hmeas := measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq a b
  obtain ⟨h2int, h2le⟩ := integral_sub_sq_le W ℱ hℱ H hm hp hq hC0 hCH ha hab
  obtain ⟨h4int, h4le⟩ := integral_sub_pow_four_le W ℱ hℱ H hm hp hq hC0 hCH ha hab
  have hba : (0 : ℝ) < b - a := by linarith
  set lam : ℝ := Real.sqrt (b - a) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr hba
  have hlamsq : lam ^ 2 = b - a := Real.sq_sqrt hba.le
  -- pointwise Young inequality `2λ|y|³ ≤ λ²y² + y⁴`
  have hyoung : ∀ y : ℝ, |y| ^ 3 ≤ (lam ^ 2 * y ^ 2 + y ^ 4) / (2 * lam) := by
    intro y
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * lam)]
    have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
    have hy3 : |y| * y ^ 2 = |y| ^ 3 := by rw [← hy2]; ring
    have hid : (lam * |y| - y ^ 2) ^ 2
        = lam ^ 2 * |y| ^ 2 - 2 * lam * (|y| * y ^ 2) + y ^ 4 := by ring
    rw [hy2, hy3] at hid
    linarith [sq_nonneg (lam * |y| - y ^ 2), hid]
  have hdomint : MeasureTheory.Integrable
      (fun ω => (lam ^ 2 * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
        + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4) / (2 * lam)) P :=
    ((h2int.const_mul (lam ^ 2)).add h4int).div_const _
  have hint3 : MeasureTheory.Integrable
      (fun ω => |stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3) P := by
    refine hdomint.mono (((continuous_abs.measurable.comp hmeas).pow_const 3).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ |stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3)]
    refine (hyoung _).trans (le_abs_self _)
  refine ⟨hint3, ?_⟩
  calc ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3 ∂P
      ≤ ∫ ω, (lam ^ 2 * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
          + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4) / (2 * lam) ∂P :=
        MeasureTheory.integral_mono hint3 hdomint (fun ω => hyoung _)
    _ = (lam ^ 2 * (∫ ω, (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2 ∂P)
          + ∫ ω, (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4 ∂P) / (2 * lam) := by
        rw [MeasureTheory.integral_div,
          MeasureTheory.integral_add (h2int.const_mul _) h4int,
          MeasureTheory.integral_const_mul]
    _ ≤ (lam ^ 2 * (C ^ 2 * (b - a))
          + (6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) / (2 * lam) := by
        gcongr
    _ = (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 * ((b - a) * lam) := by
        rw [hlamsq]
        field_simp
        rw [hlamsq]
        ring

end ThirdMoment

end LevyStochCalc.Brownian.Ito
