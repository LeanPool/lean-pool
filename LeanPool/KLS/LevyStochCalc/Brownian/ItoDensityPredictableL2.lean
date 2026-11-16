/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoDensityPointwise

/-!
# `L²` convergence of the predictable dyadic approximations

For a bounded jointly measurable integrand the left-shifted dyadic simple processes
converge to it in `L²(Ω × [0,T])`, giving density of the simple predictable processes and
of the adapted simple processes in the bounded case, joint measurability of the evaluation
map and the `L²` Cauchy property of the approximating sequence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Joint measurability of the predictable convergence set.** -/
private lemma predictable_convergence_set_measurable
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    MeasurableSet
      {p : Ω × ℝ | Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2))} := by
  have h_eq : {p : Ω × ℝ | Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2))}
      = {p : Ω × ℝ | Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1
          - g p.1 p.2)
        Filter.atTop (nhds 0)} := by
    ext p
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using hp.sub h_const
    · intro hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using hp.add h_const
  rw [h_eq]
  have h_seq_meas : ∀ n, Measurable (fun (p : Ω × ℝ) =>
      (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1
        - g p.1 p.2) := by
    intro n
    have h_eval_meas : Measurable (fun p : Ω × ℝ =>
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
      unfold SimplePredictable.eval
      refine Finset.measurable_sum _ ?_
      intro i _
      refine Measurable.ite ?_ ?_ measurable_const
      · refine MeasurableSet.inter ?_ ?_
        · exact measurable_snd (measurableSet_Ioi
            (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.castSucc))
        · exact measurable_snd (measurableSet_Iic
            (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.succ))
      · exact (dyadicAvg_shifted_brownian_measurable T g h_meas n i).comp measurable_fst
    exact h_eval_meas.sub
      (h_meas.comp (by fun_prop : Measurable (fun (p : Ω × ℝ) => (p.1, p.2))))
  exact measurableSet_tendsto (nhds (0 : ℝ)) h_seq_meas

/-- **a.e. convergence on the product (predictable case).** -/
private lemma predictableDyadicSimple_brownian_ae_tendsto
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2)) := by
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
    (predictable_convergence_set_measurable hT g h_meas M h_bound)]
  refine Filter.Eventually.of_forall (fun ω => ?_)
  exact predictable_pointwise_tendsto_per_omega hT g h_meas M h_bound ω

/-- **L² convergence of predictable shifted dyadic to g.** Mirror of
`dyadicSimplePredictable_brownian_L2_converges`, but with `M` replaced by
`max M 0` for the eval bound, and using `predictable_pointwise_tendsto_per_omega`. -/
lemma predictableDyadicSimple_brownian_L2_converges
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s - (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  have h_finite_vol : MeasureTheory.IsFiniteMeasure
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have h_finite_prod : MeasureTheory.IsFiniteMeasure
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := inferInstance
  -- Bound: 2(|M|+1) ≥ |g - eval|.
  set CC : ℝ := 2 * (|M| + 1) with hCC
  have hCC_pos : (0 : ℝ) < CC := by
    have : (0 : ℝ) ≤ |M| := abs_nonneg _
    rw [hCC]; linarith
  have hCC_nn : (0 : ℝ) ≤ CC := le_of_lt hCC_pos
  set F : ℕ → Ω × ℝ → ℝ≥0∞ := fun n p =>
    (‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2 with hF_def
  have h_F_bound : ∀ n p, F n p ≤ ENNReal.ofReal (CC ^ 2) := by
    intro n p
    have h_norm_le : ‖g p.1 p.2 -
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖
        ≤ CC := by
      rw [Real.norm_eq_abs]
      have h1 : |g p.1 p.2| ≤ M := h_bound p.1 p.2
      have h2 : |(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1|
          ≤ max M 0 :=
        predictableDyadicSimple_brownian_eval_bounded hT g h_meas M h_bound n p.2 p.1
      have h_abs_M : M ≤ |M| := le_abs_self _
      have h_max_le : max M 0 ≤ |M| + 1 := by
        by_cases hM : M ≤ 0
        · rw [max_eq_right hM]
          have : (0 : ℝ) ≤ |M| := abs_nonneg _
          linarith
        · push Not at hM
          rw [max_eq_left hM.le]
          linarith [le_abs_self M]
      have h12 : |g p.1 p.2 -
          (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1|
          ≤ |g p.1 p.2| +
              |(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1| :=
        abs_sub _ _
      rw [hCC]; linarith
    have h_norm_nn : 0 ≤ ‖g p.1 p.2 -
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ :=
      norm_nonneg _
    change (‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (CC ^ 2)
    have : ((‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)) = ENNReal.ofReal ‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ :=
      (ofReal_norm _).symm
    rw [this, ← ENNReal.ofReal_pow h_norm_nn]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)]
  have h_F_meas : ∀ n, Measurable (F n) := by
    intro n
    change Measurable (fun (p : Ω × ℝ) => (‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2)
    have h_eval_meas : Measurable (fun p : Ω × ℝ =>
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
      unfold SimplePredictable.eval
      refine Finset.measurable_sum _ ?_
      intro i _
      refine Measurable.ite ?_ ?_ measurable_const
      · refine MeasurableSet.inter ?_ ?_
        · exact measurable_snd (measurableSet_Ioi
            (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.castSucc))
        · exact measurable_snd (measurableSet_Iic
            (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.succ))
      · exact (dyadicAvg_shifted_brownian_measurable T g h_meas n i).comp measurable_fst
    have h_diff : Measurable (fun p : Ω × ℝ =>
        g p.1 p.2 -
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) :=
      (h_meas.comp (by fun_prop : Measurable (fun (p : Ω × ℝ) => (p.1, p.2)))).sub
        h_eval_meas
    exact ((ENNReal.continuous_coe.measurable.comp h_diff.nnnorm)).pow_const 2
  have h_bound_integrable : ∫⁻ _ : Ω × ℝ, ENNReal.ofReal (CC ^ 2)
      ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) ≠ ⊤ := by
    rw [MeasureTheory.lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (MeasureTheory.measure_ne_top _ _)
  have h_F_ae : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Filter.Tendsto (fun n => F n p) Filter.atTop (nhds 0) := by
    have h_ae := predictableDyadicSimple_brownian_ae_tendsto (P := P) hT g h_meas M h_bound
    filter_upwards [h_ae] with p hp
    change Filter.Tendsto (fun n => (‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2) Filter.atTop (nhds 0)
    have h_diff_zero : Filter.Tendsto
        (fun n => g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds 0) := by
      have hp' : Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2)) := hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using h_const.sub hp'
    have h_norm_zero : Filter.Tendsto
        (fun n => ‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊)
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0) = ‖(0 : ℝ)‖₊ from by simp]
      exact (continuous_nnnorm.tendsto _).comp h_diff_zero
    have h_enorm_zero : Filter.Tendsto
        (fun n => ((‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)))
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0∞) = ((0 : ℝ≥0) : ℝ≥0∞) from by simp]
      exact (ENNReal.continuous_coe.tendsto _).comp h_norm_zero
    have h_sq_continuous : Continuous (fun x : ℝ≥0∞ => x ^ 2) :=
      ENNReal.continuous_pow 2
    have : Filter.Tendsto (fun n => ((‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)) ^ 2) Filter.atTop (nhds ((0 : ℝ≥0∞) ^ 2)) :=
      (h_sq_continuous.tendsto _).comp h_enorm_zero
    simpa using this
  have h_DCT : Filter.Tendsto
      (fun n => ∫⁻ p, F n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
      Filter.atTop (nhds 0) := by
    have h_target : Filter.Tendsto (fun n => ∫⁻ p, F n p
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
        Filter.atTop
        (nhds (∫⁻ _ : Ω × ℝ, (0 : ℝ≥0∞)
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))) := by
      refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
        (bound := fun _ => ENNReal.ofReal (CC ^ 2))
        (fun n => (h_F_meas n).aemeasurable)
        ?_ h_bound_integrable h_F_ae
      intro n
      exact Filter.Eventually.of_forall (fun p => h_F_bound n p)
    simpa using h_target
  have h_eq : ∀ n, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s -
          (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ∫⁻ p, F n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
    intro n
    rw [MeasureTheory.lintegral_prod _ (h_F_meas n).aemeasurable]
  simp_rw [h_eq]
  exact h_DCT

/-- **Step 4 (chain assembly):** Bounded measurable functions are L²-approximable
by `SimplePredictable`. Direct construction via `dyadicSimplePredictable_brownian`. -/
lemma simplePredictable_dense_L2_bounded_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖g ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) :=
  ⟨fun n => dyadicSimplePredictable_brownian hT g h_meas M h_bound n,
   dyadicSimplePredictable_brownian_L2_converges hT g h_meas M h_bound⟩

/-- **Adapted bounded density (Brownian).** Bounded progressively measurable
functions are L²-approximable by ADAPTED `SimplePredictable`s.

Construction via `predictableDyadicSimple_brownian` (the left-shifted dyadic
average), which is `ℱ_{t_i}`-StronglyMeasurable for progressively measurable `g`. -/
lemma adaptedSimple_dense_L2_bounded_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ g)
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      (∀ n : ℕ, ∀ i : Fin (Hn n).N,
        @MeasureTheory.StronglyMeasurable Ω ℝ _
          (ℱ ((Hn n).partition i.castSucc)) ((Hn n).ξ i)) ∧
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖g ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) :=
  ⟨fun n => predictableDyadicSimple_brownian hT g h_meas M h_bound n,
   fun n i => predictableDyadicSimple_brownian_adapted ℱ hT g h_meas M h_bound
     h_progMeas n i,
   predictableDyadicSimple_brownian_L2_converges hT g h_meas M h_bound⟩

/-- **Partition endpoint of `predictableDyadicSimple_brownian` is T.** Trivially
inherited from `dyadicPartition_brownian_last`. -/
lemma predictableDyadicSimple_brownian_partition_last
    {T : ℝ} (hT : 0 < T) (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) :
    (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
      (Fin.last (predictableDyadicSimple_brownian hT g h_meas M h_bound n).N)
      = T := by
  change dyadicPartition_brownian T n (Fin.last (2 ^ n)) = T
  exact dyadicPartition_brownian_last T n

/-- **Joint measurability of `predictableDyadicSimple_brownian.eval`.**
The eval `(p : Ω × ℝ) ↦ (Hn n).eval p.2 p.1` is jointly measurable.
Uses the indicator-sum decomposition. -/
lemma predictableDyadicSimple_brownian_eval_jointly_measurable
    {T : ℝ} (hT : 0 < T) (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) :
    Measurable (fun (p : Ω × ℝ) =>
      (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
  unfold SimplePredictable.eval
  refine Finset.measurable_sum _ ?_
  intro i _
  refine Measurable.ite ?_ ?_ measurable_const
  · refine MeasurableSet.inter ?_ ?_
    · exact measurable_snd (measurableSet_Ioi
        (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
          i.castSucc))
    · exact measurable_snd (measurableSet_Iic
        (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
          i.succ))
  · exact (dyadicAvg_shifted_brownian_measurable T g h_meas n i).comp measurable_fst

/-- **Generic joint measurability of `SimplePredictable.eval`.** For any
`SimplePredictable Ω T`, the function `(p : Ω × ℝ) ↦ H.eval p.2 p.1` is measurable.

Proof: `eval` is a finite sum of indicator-times-coefficient terms, each measurable
since the indicator's set is `{p | partition i.castSucc < p.2 ≤ partition i.succ}`
(measurable in `snd`) and the coefficient is `H.ξ i ∘ fst` (measurable since
`H.ξ_measurable i`). -/
lemma SimplePredictable.eval_jointly_measurable
    {T : ℝ} (H : SimplePredictable Ω T) :
    Measurable (fun (p : Ω × ℝ) => H.eval p.2 p.1) := by
  unfold SimplePredictable.eval
  refine Finset.measurable_sum _ ?_
  intro i _
  refine Measurable.ite ?_ ?_ measurable_const
  · refine MeasurableSet.inter ?_ ?_
    · exact measurable_snd (measurableSet_Ioi (a := H.partition i.castSucc))
    · exact measurable_snd (measurableSet_Iic (a := H.partition i.succ))
  · exact (H.ξ_measurable i).comp measurable_fst

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **L²-Cauchy from L²-tendsto.** If a sequence `(Hn n).eval` converges to `H`
in `L²` (lintegral form), then `(Hn n).eval` is L²-Cauchy.

Triangle inequality `(a+b)² ≤ 2(a²+b²)` plus `Filter.Tendsto.eventually_lt_const`
for strict `<`. Takes joint measurability of `Hn n` and `H`. -/
lemma L2_cauchy_of_L2_tendsto_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ}
    (Hn : ℕ → SimplePredictable Ω T)
    (H : Ω → ℝ → ℝ)
    (h_meas_eval : ∀ n, Measurable (fun (p : Ω × ℝ) => (Hn n).eval p.2 p.1))
    (h_meas_H : Measurable (Function.uncurry H))
    (h_tendsto : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(Hn n).eval s ω - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε := by
  intro ε hε_pos
  have hε4_pos : (0 : ℝ≥0∞) < ε / 4 := by
    rw [ENNReal.div_pos_iff]
    refine ⟨hε_pos.ne', ?_⟩
    decide
  have h_eventually := h_tendsto.eventually_lt_const hε4_pos
  rw [Filter.eventually_atTop] at h_eventually
  obtain ⟨N, hN⟩ := h_eventually
  refine ⟨N, fun n m hn hm => ?_⟩
  have h_pointwise : ∀ ω s,
      (‖(Hn n).eval s ω - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖(Hn n).eval s ω - H ω s‖₊ : ℝ≥0∞) ^ 2
            + (‖H ω s - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω s
    have h_sum : ((Hn n).eval s ω - H ω s) + (H ω s - (Hn m).eval s ω)
        = (Hn n).eval s ω - (Hn m).eval s ω := by ring
    have := sq_nnnorm_add_le_two_mul_brownian
      ((Hn n).eval s ω - H ω s) (H ω s - (Hn m).eval s ω)
    rw [h_sum] at this
    exact this
  set A : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖(Hn n).eval s ω - H ω s‖₊ : ℝ≥0∞) ^ 2 with hA
  set B : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖H ω s - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hB
  set C : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖(Hn n).eval s ω - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hC
  have h_A_eq : ∀ ω s, A ω s = (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    simp only [hA]
    congr 1
    rw [show (Hn n).eval s ω - H ω s = -(H ω s - (Hn n).eval s ω) from by ring]
    rw [nnnorm_neg]
  have h_int_A_lt :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P) < ε / 4 := by
    have h_eq : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
      congr 1
      ext ω
      congr 1
      ext s
      exact h_A_eq ω s
    rw [h_eq]
    exact hN n hn
  have h_int_B_lt :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) < ε / 4 := by
    change ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ε / 4
    exact hN m hm
  have h_meas_A_s : ∀ ω, Measurable (fun s => A ω s) := by
    intro ω
    simp only [hA]
    have h_eval_n_meas : Measurable (fun s => (Hn n).eval s ω) :=
      (h_meas_eval n).comp (by fun_prop : Measurable (fun s : ℝ => ((ω, s) : Ω × ℝ)))
    have h_H_meas : Measurable (fun s : ℝ => H ω s) :=
      h_meas_H.comp (by fun_prop : Measurable (fun s : ℝ => (ω, s)))
    exact ((ENNReal.continuous_coe.measurable.comp
      (h_eval_n_meas.sub h_H_meas).nnnorm)).pow_const 2
  have h_meas_A_outer : Measurable (fun ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume) := by
    have h_meas_A_pair : Measurable (fun (q : Ω × ℝ) => A q.1 q.2) := by
      simp only [hA]
      have h_eval_n_pair : Measurable (fun (q : Ω × ℝ) =>
          (Hn n).eval q.2 q.1) := h_meas_eval n
      have h_H_pair : Measurable (fun (q : Ω × ℝ) => H q.1 q.2) :=
        h_meas_H.comp (by fun_prop : Measurable (fun (q : Ω × ℝ) => (q.1, q.2)))
      exact ((ENNReal.continuous_coe.measurable.comp
        (h_eval_n_pair.sub h_H_pair).nnnorm)).pow_const 2
    exact Measurable.lintegral_prod_right'
      (ν := volume.restrict (Set.Icc (0:ℝ) T)) h_meas_A_pair
  have h_C_int_le :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
      ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
    have h_inner : ∀ ω,
        (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume) ≤
          2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
            + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
      intro ω
      calc (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume)
          ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, 2 * (A ω s + B ω s) ∂volume :=
            MeasureTheory.lintegral_mono (h_pointwise ω)
        _ = 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, (A ω s + B ω s) ∂volume := by
            rw [MeasureTheory.lintegral_const_mul']
            simp
        _ = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
            + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
            congr 1
            rw [MeasureTheory.lintegral_add_left']
            exact (h_meas_A_s ω).aemeasurable
    calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
        ≤ ∫⁻ ω,
            2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P :=
          MeasureTheory.lintegral_mono h_inner
      _ = 2 * ∫⁻ ω,
            ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P := by
          rw [MeasureTheory.lintegral_const_mul']
          simp
      _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
          congr 1
          rw [MeasureTheory.lintegral_add_left']
          exact h_meas_A_outer.aemeasurable
  have h_AB_sum_lt :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
      + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P < ε / 4 + ε / 4 :=
    ENNReal.add_lt_add h_int_A_lt h_int_B_lt
  have h_2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_2_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_2_sum_lt :
      (2 : ℝ≥0∞) * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
      + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) <
      (2 : ℝ≥0∞) * (ε / 4 + ε / 4) :=
    ENNReal.mul_right_strictMono h_2_ne_zero h_2_ne_top h_AB_sum_lt
  have h_eq_ε : (2 : ℝ≥0∞) * (ε / 4 + ε / 4) = ε := by
    rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 from by norm_num]
    exact ENNReal.mul_div_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)
  rw [h_eq_ε] at h_2_sum_lt
  exact lt_of_le_of_lt h_C_int_le h_2_sum_lt

/-- **L²-Cauchy of `predictableDyadicSimple_brownian` evals.** Direct corollary of
`predictableDyadicSimple_brownian_L2_converges` + `L2_cauchy_of_L2_tendsto_brownian`. -/
lemma predictableDyadicSimple_brownian_L2_cauchy
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω -
          (predictableDyadicSimple_brownian hT g h_meas M h_bound m).eval s ω‖₊
          : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε :=
  L2_cauchy_of_L2_tendsto_brownian
    (fun n => predictableDyadicSimple_brownian hT g h_meas M h_bound n) g
    (fun n => predictableDyadicSimple_brownian_eval_jointly_measurable hT g h_meas M
      h_bound n)
    h_meas
    (predictableDyadicSimple_brownian_L2_converges hT g h_meas M h_bound)
end LevyStochCalc.Brownian.Ito
