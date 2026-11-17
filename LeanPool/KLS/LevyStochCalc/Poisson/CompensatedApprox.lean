/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.MarkStep
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoL2Completion

/-!
# Approximation of a square-integrable integrand by mark-step integrands

For a jointly measurable, progressively measurable integrand `φ : Ω → ℝ → E → ℝ` that is
square integrable over `Ω × [0, T] × E`, and any dyadic level `L₀` and tolerance `ε`, there is
an adapted mark-step integrand on a dyadic grid of level at least `L₀` within `ε` of `φ` in
`L²(P ⊗ ds ⊗ ν)` on `[0, T]` (`exists_markStep_close`). The integrand is first clipped and
restricted to a mark set of finite measure (`truncate`), which reduces to the bounded,
finitely supported case treated by `exists_markEval_L2_tendsto`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Truncate

/-- The integrand clipped at level `M` and restricted to marks in `S`. -/
noncomputable def truncate (φ : Ω → ℝ → E → ℝ) (M : ℝ) (S : Set E) : Ω → ℝ → E → ℝ :=
  fun ω s e => S.indicator (fun _ => max (-M) (min M (φ ω s e))) e

lemma continuous_clip (M : ℝ) : Continuous (fun x : ℝ => max (-M) (min M x)) := by
  fun_prop

lemma abs_clip_le {M x : ℝ} (hM : 0 ≤ M) : |max (-M) (min M x)| ≤ M := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma abs_clip_le_abs {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |max (-M) (min M x)| ≤ |x| := by
  rcases le_total x 0 with hx | hx
  · rw [min_eq_right (hx.trans hM)]
    rcases le_total (-M) x with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, abs_neg, abs_of_nonneg hM, abs_of_nonpos hx]
      linarith
  · have h0 : 0 ≤ min M x := le_min hM hx
    rw [max_eq_right (by linarith), abs_of_nonneg h0, abs_of_nonneg hx]
    exact min_le_right _ _

lemma nnnorm_clip_le {M : ℝ} (hM : 0 ≤ M) (x : ℝ) :
    (‖max (-M) (min M x)‖₊ : ℝ≥0∞) ≤ ‖x‖₊ := by
  have h : ‖max (-M) (min M x)‖₊ ≤ ‖x‖₊ := by
    rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs]
    exact abs_clip_le_abs hM x
  exact_mod_cast h

variable (φ : Ω → ℝ → E → ℝ) (M : ℝ) (S : Set E)

omit [MeasurableSpace Ω] [MeasurableSpace E] in
lemma truncate_abs_le (hM : 0 ≤ M) (ω : Ω) (s : ℝ) (e : E) : |truncate φ M S ω s e| ≤ M := by
  unfold truncate
  by_cases he : e ∈ S
  · rw [Set.indicator_of_mem he]
    exact abs_clip_le hM
  · rw [Set.indicator_of_notMem he, abs_zero]
    exact hM

omit [MeasurableSpace Ω] [MeasurableSpace E] in
lemma truncate_eq_zero (ω : Ω) {e : E} (he : e ∉ S) (s : ℝ) : truncate φ M S ω s e = 0 :=
  Set.indicator_of_notMem he _

omit [MeasurableSpace Ω] [MeasurableSpace E] in
lemma truncate_eq_indicator :
    (fun p : Ω × ℝ × E => truncate φ M S p.1 p.2.1 p.2.2)
      = {p : Ω × ℝ × E | p.2.2 ∈ S}.indicator
          (fun p => max (-M) (min M (φ p.1 p.2.1 p.2.2))) := by
  funext p
  by_cases h : p.2.2 ∈ S
  · rw [truncate, Set.indicator_of_mem h,
    Set.indicator_of_mem (show p ∈ {q : Ω × ℝ × E | q.2.2 ∈ S} from h)]
  · rw [truncate, Set.indicator_of_notMem h,
      Set.indicator_of_notMem (show p ∉ {q : Ω × ℝ × E | q.2.2 ∈ S} from h)]

lemma truncate_measurable (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (hS : MeasurableSet S) :
    Measurable (fun p : Ω × ℝ × E => truncate φ M S p.1 p.2.1 p.2.2) := by
  rw [truncate_eq_indicator]
  exact ((continuous_clip M).measurable.comp h_meas).indicator
    ((measurable_snd.comp measurable_snd) hS)

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

lemma truncate_progMeas (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ) (hM : 0 ≤ M)
    (hS : MeasurableSet S) :
    Probability.MarkedProgressivelyMeasurable ℱ (truncate φ M S) :=
  ((continuous_clip M).comp_markedProgressivelyMeasurable
    (by rw [min_eq_right hM, max_eq_right (neg_nonpos.mpr hM)]) h_progMeas).indicator_mark hS

omit [IsProbabilityMeasure P] in
/-- The `2(a² + b²)` bound for nested triple integrals: if `a` is within `ε / 4` of `b`
and `b` within `ε / 4` of `c`, then `a` is within `ε` of `c`. -/
lemma triple_sq_lt_of_lt {T : ℝ} {a b c : Ω → ℝ → E → ℝ}
    (ha : Measurable (fun p : Ω × ℝ × E => a p.1 p.2.1 p.2.2))
    (hb : Measurable (fun p : Ω × ℝ × E => b p.1 p.2.1 p.2.2)) {ε : ℝ≥0∞}
    (h1 : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖a ω s e - b ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ε / 4)
    (h2 : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖b ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ε / 4) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖a ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ε := by
  have hpt : ∀ ω s e, (‖a ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖a ω s e - b ω s e‖₊ : ℝ≥0∞) ^ 2 + (‖b ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω s e
    rw [show a ω s e - c ω s e = (a ω s e - b ω s e) + (b ω s e - c ω s e) by ring]
    exact sq_nnnorm_add_le_two_mul _ _
  have hu : Measurable (fun p : Ω × ℝ × E =>
      (‖a p.1 p.2.1 p.2.2 - b p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp (ha.sub hb).nnnorm).pow_const 2
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖a ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          2 * ((‖a ω s e - b ω s e‖₊ : ℝ≥0∞) ^ 2 + (‖b ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2)
          ∂ν ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => hpt ω s e
    _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖a ω s e - b ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖b ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) := by
        rw [lintegral_triple_const_mul 2 (by norm_num), lintegral_triple_add hu]
    _ = ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖a ω s e - b ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖b ω s e - c ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) * 2 := mul_comm _ _
    _ < (ε / 4 + ε / 4) * 2 :=
        ENNReal.mul_lt_mul_left (by norm_num) (by norm_num) (ENNReal.add_lt_add h1 h2)
    _ = ε := by
        rw [show (ε / 4 + ε / 4) * 2 = 4 * (ε / 4) by ring,
          ENNReal.mul_div_cancel (by norm_num) (by norm_num)]

/-- Clipping and restricting to a finite-measure mark set approximates `φ` in `L²`. -/
lemma exists_truncate_close (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {T : ℝ} (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (M : ℕ) (S : Set E), MeasurableSet S ∧ ν S ≠ ⊤ ∧
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - truncate φ M S ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ε := by
  have hε4 : 0 < ε / 4 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨M, hM⟩ :=
    ((truncation_L2_converges φ h_meas h_sq_int).eventually (Iio_mem_nhds hε4)).exists
  set ψ : Ω → ℝ → E → ℝ := fun ω s e => max (-(M : ℝ)) (min (M : ℝ) (φ ω s e)) with hψ
  have hψ_meas : Measurable (fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2) :=
    (continuous_clip (M : ℝ)).measurable.comp h_meas
  have hψ_sq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
    refine lt_of_le_of_lt ?_ h_sq_int
    refine lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => ?_
    exact pow_le_pow_left' (nnnorm_clip_le (Nat.cast_nonneg M) _) 2
  obtain ⟨j, hj⟩ := ((mark_truncation_L2_converges ψ hψ_meas hψ_sq
    (measurableSet_spanningSets ν) (iUnion_spanningSets ν)).eventually (Iio_mem_nhds hε4)).exists
  set S : Set E := ⋃ m ∈ Finset.range j, spanningSets ν m with hS
  have hSm : MeasurableSet S :=
    Finset.measurableSet_biUnion _ fun m _ => measurableSet_spanningSets ν m
  have hSfin : ν S ≠ ⊤ :=
    ((measure_biUnion_finset_le _ _).trans_lt
      (ENNReal.sum_lt_top.2 fun m _ => measure_spanningSets_lt_top ν m)).ne
  refine ⟨M, S, hSm, hSfin, ?_⟩
  have htr : ∀ ω s e, truncate φ M S ω s e = S.indicator (fun _ => ψ ω s e) e := fun _ _ _ => rfl
  have hc_meas : Measurable (fun p : Ω × ℝ × E => truncate φ M S p.1 p.2.1 p.2.2) :=
    truncate_measurable φ M S h_meas hSm
  simp_rw [htr] at hc_meas ⊢
  exact triple_sq_lt_of_lt h_meas hψ_meas hM hj

end Truncate

section Close

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)

include N h_meas h_progMeas in
/-- A square-integrable progressively measurable integrand is approximated in `L²` on
`[0, T]` by adapted mark-step integrands on dyadic grids of arbitrarily high level. -/
theorem exists_markStep_close {T : ℝ} (hT : 0 < T)
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (L₀ : ℕ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ ℓ : ℕ, L₀ ≤ ℓ ∧ ∃ G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ), G.Adapted ℱ ∧
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ε := by
  classical
  have hε4 : 0 < ε / 4 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨M, S, hS, hSfin, hMS⟩ := exists_truncate_close φ h_meas h_sq_int hε4
  have hψm := truncate_measurable φ M S h_meas hS
  have hψp := truncate_progMeas φ M S ℱ h_progMeas (Nat.cast_nonneg M) hS
  obtain ⟨Ki, Bi, ci, hBim, hBiS, hcia, hcib, htend⟩ :=
    exists_markEval_L2_tendsto N ℱ hT (truncate φ M S) hψm hψp
      (truncate_abs_le φ M S (Nat.cast_nonneg M)) hS hSfin
      (fun ω e he u => truncate_eq_zero φ M S ω he u)
  obtain ⟨ℓ, hℓerr, hℓ⟩ :=
    ((htend.eventually (Iio_mem_nhds hε4)).and (Filter.eventually_ge_atTop L₀)).exists
  have hcim : ∀ i k, Measurable (ci ℓ i k) := fun i k =>
    (hcia ℓ i k).measurable.mono (ℱ.le _) le_rfl
  obtain ⟨K, B, ξ, hBm, hBf, hξb, hξm, hξa, hF⟩ :=
    exists_sharedMark_blockDiag N ℱ (dyadicPartition T ℓ) (Bi ℓ) (ci ℓ) (hBim ℓ)
      (fun i k => ne_top_of_le_ne_top hSfin (measure_mono (hBiS ℓ i k))) (hcib ℓ) hcim (hcia ℓ)
  let G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ) :=
    { K := K
      B := B
      B_measurable := hBm
      B_finite := hBf
      ξ := fun i k => if h : i < 2 ^ ℓ then ξ ⟨i, h⟩ k else 0
      ξ_bounded := fun i k => by
        by_cases h : i < 2 ^ ℓ
        · rw [dite_eq_left h]
          exact hξb ⟨i, h⟩ k
        · rw [dite_eq_right h]
          exact ⟨0, fun ω => by simp⟩
      ξ_measurable := fun i k => by
        by_cases h : i < 2 ^ ℓ
        · rw [dite_eq_left h]
          exact hξm ⟨i, h⟩ k
        · rw [dite_eq_right h]
          exact measurable_const }
  have hG : G.Adapted ℱ := by
    intro i hi k
    change @StronglyMeasurable Ω ℝ _ (ℱ ((TimeGrid.dyadic T hT ℓ).p i))
      (if h : i < 2 ^ ℓ then ξ ⟨i, h⟩ k else 0)
    rw [dite_eq_left (show i < 2 ^ ℓ from hi)]
    exact hξa ⟨i, hi⟩ k
  have heval : ∀ s e ω, G.eval s e ω = ∑ i : Fin (2 ^ ℓ),
      (Set.Ioc (dyadicPartition T ℓ i.castSucc) (dyadicPartition T ℓ i.succ)).indicator
        (fun _ => (1 : ℝ)) s
      * ∑ k, ci ℓ i k ω * (Bi ℓ i k).indicator (fun _ => (1 : ℝ)) e := by
    intro s e ω
    rw [MarkStep.eval_eq_fin]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (Set.Ioc (dyadicPartition T ℓ i.castSucc) (dyadicPartition T ℓ i.succ)).indicator
        (fun _ => (1 : ℝ)) s
      * ∑ k, (if h : (i : ℕ) < 2 ^ ℓ then ξ ⟨i, h⟩ k else 0) ω
          * (B k).indicator (fun _ => (1 : ℝ)) e = _
    congr 1
    rw [show (∑ k, (if h : (i : ℕ) < 2 ^ ℓ then ξ ⟨i, h⟩ k else 0) ω
          * (B k).indicator (fun _ => (1 : ℝ)) e)
        = ∑ k, ξ ⟨i, i.isLt⟩ k ω * (B k).indicator (fun _ => (1 : ℝ)) e from
      Finset.sum_congr rfl fun k _ => by rw [dite_eq_left (show (i : ℕ) < 2 ^ ℓ from i.isLt)]]
    exact hF ⟨i, i.isLt⟩ ω (fun B' => B'.indicator (fun _ => (1 : ℝ)) e)
  have hmk : Measurable (fun p : Ω × ℝ × E => ∑ i : Fin (2 ^ ℓ),
      (Set.Ioc (dyadicPartition T ℓ i.castSucc) (dyadicPartition T ℓ i.succ)).indicator
        (fun _ => (1 : ℝ)) p.2.1
      * ∑ k, ci ℓ i k p.1 * (Bi ℓ i k).indicator (fun _ => (1 : ℝ)) p.2.2) := by
    have := G.eval_measurable
    simp_rw [heval] at this
    exact this
  refine ⟨ℓ, hℓ, G, hG, ?_⟩
  simp_rw [heval]
  exact triple_sq_lt_of_lt h_meas hψm hMS hℓerr

end Close

section Master

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

/-- The horizon `2 ^ n` of stage `n` of the master sequence. -/
def stageHorizon (n : ℕ) : ℝ := (2 : ℝ) ^ n

lemma stageHorizon_pos (n : ℕ) : 0 < stageHorizon n := pow_pos two_pos n

lemma stageHorizon_mono {n n' : ℕ} (h : n ≤ n') : stageHorizon n ≤ stageHorizon n' :=
  pow_le_pow_right₀ one_le_two h

lemma stageHorizon_eq_mul {n n' : ℕ} (h : n ≤ n') :
    stageHorizon n' = stageHorizon n * 2 ^ (n' - n) := by
  unfold stageHorizon
  rw [← pow_add, Nat.add_sub_cancel' h]

/-- The `L²` error of a mark-step integrand against `φ` on the horizon of stage `n`. -/
noncomputable def stageErr (P : Measure Ω) (n : ℕ) {ℓ : ℕ}
    (G : MarkStep Ω E ν (TimeGrid.dyadic (stageHorizon n) (stageHorizon_pos n) ℓ)) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) (stageHorizon n), ∫⁻ e,
    (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P

include N h_meas h_progMeas h_sq_int_global in
lemma exists_stage (n L₀ : ℕ) :
    ∃ ℓ : ℕ, L₀ ≤ ℓ ∧
      ∃ G : MarkStep Ω E ν (TimeGrid.dyadic (stageHorizon n) (stageHorizon_pos n) ℓ),
        G.Adapted ℱ ∧ stageErr φ P n G < ((n : ℝ≥0∞) + 1)⁻¹ :=
  exists_markStep_close N ℱ φ h_meas h_progMeas (stageHorizon_pos n)
    (h_sq_int_global _ (stageHorizon_pos n)) L₀
    (ENNReal.inv_pos.2 (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩))

/-- The master sequence of approximants: stage `n` is an adapted mark-step integrand on a
dyadic grid of `[0, 2 ^ n]` within `(n + 1)⁻¹` of `φ` in `L²`, the levels increasing by at
least one per stage. -/
noncomputable def master :
    ∀ n : ℕ, Σ ℓ : ℕ, MarkStep Ω E ν (TimeGrid.dyadic (stageHorizon n) (stageHorizon_pos n) ℓ)
  | 0 => ⟨Classical.choose (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global 0 0),
      Classical.choose
        (Classical.choose_spec (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global 0 0)).2⟩
  | n + 1 => ⟨Classical.choose (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global (n + 1)
        ((master n).1 + 1)),
      Classical.choose (Classical.choose_spec (exists_stage N ℱ φ h_meas h_progMeas
        h_sq_int_global (n + 1) ((master n).1 + 1))).2⟩

lemma master_level_succ (n : ℕ) :
    (master N ℱ φ h_meas h_progMeas h_sq_int_global n).1 + 1
      ≤ (master N ℱ φ h_meas h_progMeas h_sq_int_global (n + 1)).1 :=
  (Classical.choose_spec (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global (n + 1)
    ((master N ℱ φ h_meas h_progMeas h_sq_int_global n).1 + 1))).1

lemma master_level_add {n n' : ℕ} (h : n ≤ n') :
    (master N ℱ φ h_meas h_progMeas h_sq_int_global n).1 + (n' - n)
      ≤ (master N ℱ φ h_meas h_progMeas h_sq_int_global n').1 := by
  induction h with
  | refl => simp
  | @step m h ih =>
    have h1 := master_level_succ N ℱ φ h_meas h_progMeas h_sq_int_global m
    change _ + (m + 1 - n) ≤ (master N ℱ φ h_meas h_progMeas h_sq_int_global (m + 1)).1
    omega

lemma master_adapted (n : ℕ) :
    (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.Adapted ℱ := by
  cases n with
  | zero =>
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global 0 0)).2).1
  | succ n =>
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global (n + 1) _)).2).1

lemma master_err (n : ℕ) :
    stageErr φ P n (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 < ((n : ℝ≥0∞) + 1)⁻¹ :=
      by
  cases n with
  | zero =>
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global 0 0)).2).2
  | succ n =>
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_stage N ℱ φ h_meas h_progMeas h_sq_int_global (n + 1) _)).2).2

end Master

section Cauchy

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

/-- The compensated integral of the stage-`n` approximant up to time `t`. -/
noncomputable def stageIntegral (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.integral N t ω

include hℱ in
lemma martingale_stageIntegral (n : ℕ) :
    Martingale (fun t => stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t)
      ℱ P :=
  MarkStep.martingale_integral N hℱ _ (master_adapted N ℱ φ h_meas h_progMeas h_sq_int_global n)

lemma memLp_stageIntegral (n : ℕ) (t : ℝ) :
    MemLp (fun ω => stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω) 2 P :=
  MarkStep.memLp_integral N _ t

lemma stageIntegral_eq_zero_of_nonpos (n : ℕ) {t : ℝ} (ht : t ≤ 0) (ω : Ω) :
    stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω = 0 :=
  MarkStep.integral_eq_zero_of_nonpos N _ ht ω

omit [IsProbabilityMeasure P] in
/-- Tonelli for the inner two integrals of the nested triple integral. -/
lemma lintegral_swap_es {T : ℝ} (f : Ω → ℝ → E → ℝ≥0∞)
    (hf : Measurable (fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2)) (ω : Ω) :
    ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T, f ω s e ∂volume ∂ν
      = ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, f ω s e ∂ν ∂volume := by
  refine lintegral_lintegral_swap ?_
  exact (hf.comp (by fun_prop :
    Measurable fun q : E × ℝ => ((ω, q.2, q.1) : Ω × ℝ × E))).aemeasurable

include hℱ in
/-- The `L²` distance between two stages, at the horizon of the earlier stage. -/
lemma stageIntegral_sub_sq_horizon_le {n n' : ℕ} (h : n ≤ n') :
    ∫⁻ ω, (‖stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n (stageHorizon n) ω
        - stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n' (stageHorizon n) ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * ((n : ℝ≥0∞) + 1)⁻¹ + 2 * ((n' : ℝ≥0∞) + 1)⁻¹ := by
  set G := (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 with hGdef
  set G' := (master N ℱ φ h_meas h_progMeas h_sq_int_global n').2 with hG'def
  have hG := master_adapted N ℱ φ h_meas h_progMeas h_sq_int_global n
  have hG' := master_adapted N ℱ φ h_meas h_progMeas h_sq_int_global n'
  have hlev := master_level_add N ℱ φ h_meas h_progMeas h_sq_int_global h
  have hd : n' - n ≤ (master N ℱ φ h_meas h_progMeas h_sq_int_global n').1 := by omega
  have hℓ : (master N ℱ φ h_meas h_progMeas h_sq_int_global n).1
      ≤ (master N ℱ φ h_meas h_progMeas h_sq_int_global n').1 - (n' - n) := by omega
  have hT := stageHorizon_eq_mul h
  set R := G'.dyadicRestrict (stageHorizon_pos n) hd hT with hRdef
  set Rf := G.dyadicRefine hℓ with hRfdef
  have hR : R.Adapted ℱ := hG'.dyadicRestrict (stageHorizon_pos n) hd hT
  have hRf : Rf.Adapted ℱ := hG.dyadicRefine N hℓ
  have hhor : (TimeGrid.dyadic (stageHorizon n) (stageHorizon_pos n)
      ((master N ℱ φ h_meas h_progMeas h_sq_int_global n').1 - (n' - n))).horizon
      = stageHorizon n := TimeGrid.dyadic_horizon _ _ _
  have e1 : ∀ ω, stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n (stageHorizon n) ω
      = G.full N ω := fun ω =>
    G.integral_eq_full_of_horizon_le N (by rw [TimeGrid.dyadic_horizon]) ω
  have e2 : ∀ ω, stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n' (stageHorizon n) ω
      = R.full N ω := fun ω => (G'.full_dyadicRestrict N (stageHorizon_pos n) hd hT ω).symm
  have e3 : ∀ ω, R.full N ω = R.integral N (stageHorizon n) ω := fun ω =>
    (R.integral_eq_full_of_horizon_le N hhor.le ω).symm
  have e4 : ∀ ω, Rf.full N ω = Rf.integral N (stageHorizon n) ω := fun ω =>
    (Rf.integral_eq_full_of_horizon_le N hhor.le ω).symm
  have hae : (fun ω => (‖G.full N ω - R.full N ω‖₊ : ℝ≥0∞) ^ 2)
      =ᵐ[P] fun ω => (‖Rf.integral N (stageHorizon n) ω
        - R.integral N (stageHorizon n) ω‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [G.full_dyadicRefine N hℓ] with ω hω
    rw [← hω, e3, e4]
  simp_rw [e1, e2]
  rw [lintegral_congr_ae hae,
    Rf.lintegral_integral_sub_sq_at N hℱ R hRf hR (stageHorizon_pos n).le]
  have hev : ∀ ω e s, s ∈ Set.Icc (0 : ℝ) (stageHorizon n) →
      Rf.eval s e ω - R.eval s e ω = G.eval s e ω - G'.eval s e ω := by
    intro ω e s hs
    rw [G.eval_dyadicRefine hℓ, G'.eval_dyadicRestrict (stageHorizon_pos n) hd hT hs.2]
  have hu : Measurable (fun p : Ω × ℝ × E =>
      (‖φ p.1 p.2.1 p.2.2 - G.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp (h_meas.sub G.eval_measurable).nnnorm).pow_const 2
  have hw : Measurable (fun p : Ω × ℝ × E =>
      (‖G.eval p.2.1 p.2.2 p.1 - G'.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp
      (G.eval_measurable.sub G'.eval_measurable).nnnorm).pow_const 2
  have hpt : ∀ ω s e, (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2
        + (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω s e
    rw [show G.eval s e ω - G'.eval s e ω
      = -(φ ω s e - G.eval s e ω) + (φ ω s e - G'.eval s e ω) by ring]
    have h2 := sq_nnnorm_add_le_two_mul (-(φ ω s e - G.eval s e ω)) (φ ω s e - G'.eval s e ω)
    rwa [nnnorm_neg] at h2
  have herr' : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) (stageHorizon n), ∫⁻ e,
      (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      ≤ stageErr φ P n' G' :=
    lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right (stageHorizon_mono h))
  calc ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) (stageHorizon n),
        (‖Rf.eval s e ω - R.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) (stageHorizon n), ∫⁻ e,
        (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [← lintegral_swap_es (fun ω s e => (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hw ω]
        refine lintegral_congr fun e => ?_
        refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
        rw [hev ω e s hs]
    _ ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) (stageHorizon n), ∫⁻ e,
        2 * ((‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2
          + (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2) ∂ν ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => hpt ω s e
    _ = 2 * (stageErr φ P n G + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) (stageHorizon n), ∫⁻ e,
        (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) := by
        rw [lintegral_triple_const_mul 2 (by norm_num), lintegral_triple_add hu]
        rfl
    _ ≤ 2 * (((n : ℝ≥0∞) + 1)⁻¹ + ((n' : ℝ≥0∞) + 1)⁻¹) := by
        gcongr
        · exact (master_err N ℱ φ h_meas h_progMeas h_sq_int_global n).le
        · exact herr'.trans (master_err N ℱ φ h_meas h_progMeas h_sq_int_global n').le
    _ = 2 * ((n : ℝ≥0∞) + 1)⁻¹ + 2 * ((n' : ℝ≥0∞) + 1)⁻¹ := mul_add _ _ _

include hℱ in
/-- The `L²` distance between two stages at any time up to the horizon of the earlier
stage. -/
lemma stageIntegral_sub_sq_le {n n' : ℕ} (h : n ≤ n') {t : ℝ} (ht : t ≤ stageHorizon n) :
    ∫⁻ ω, (‖stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω
        - stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n' t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * ((n : ℝ≥0∞) + 1)⁻¹ + 2 * ((n' : ℝ≥0∞) + 1)⁻¹ := by
  refine le_trans ?_ (stageIntegral_sub_sq_horizon_le N ℱ hℱ φ h_meas h_progMeas h_sq_int_global h)
  set M : ℝ → Ω → ℝ := fun u ω => stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n u ω
    - stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n' u ω with hMdef
  have hmart : Martingale M ℱ P :=
    (martingale_stageIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global n).sub
      (martingale_stageIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global n')
  have hL2 : ∀ u, MemLp (M u) 2 P := fun u =>
    (memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n u).sub
      (memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n' u)
  have key := LevyStochCalc.Brownian.Ito.integral_sq_increment_eq_of_martingale hmart (hL2 t)
    (hL2 (stageHorizon n)) ht
  have h0 : 0 ≤ ∫ ω, (M (stageHorizon n) ω - M t ω) ^ 2 ∂P :=
    integral_nonneg fun ω => sq_nonneg _
  have hle : ∫ ω, (M t ω) ^ 2 ∂P ≤ ∫ ω, (M (stageHorizon n) ω) ^ 2 ∂P := by linarith
  change ∫⁻ ω, (‖M t ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ ∫⁻ ω, (‖M (stageHorizon n) ω‖₊ : ℝ≥0∞) ^ 2 ∂P
  rw [lintegral_sq_eq_ofReal_integral (hL2 t),
    lintegral_sq_eq_ofReal_integral (hL2 (stageHorizon n))]
  exact ENNReal.ofReal_le_ofReal hle

end Cauchy

end LevyStochCalc.Poisson.Compensated
