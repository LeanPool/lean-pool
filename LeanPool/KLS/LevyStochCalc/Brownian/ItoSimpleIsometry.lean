/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoSimpleMoments

/-!
# The Itô isometry on simple predictable integrands

Expanding the square of the elementary integral into its diagonal and off-diagonal terms gives,
for an adapted simple predictable integrand `H` and a scalar Brownian motion `W`,
`E[(∫_0^T H dW) ^ 2] = ∑_i (t_{i+1} - t_i) · E[ξ_i ^ 2]`; combined with the energy of the
integrand this is the L²-isometry `E[(∫_0^T H dW) ^ 2] = ∫_0^T E[(H.eval s) ^ 2] ds`, stated
both for the lower integral and for the Bochner integral.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Bochner LHS reduction for Brownian.** -/
private lemma simpleIntegral_sq_bochner_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫ ω, (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω))^2 ∂P
      = ∑ i : Fin H.N,
        (H.partition i.succ - H.partition i.castSucc) *
        ∫ ω, (H.ξ i ω)^2 ∂P := by
  -- Expand (∑ a_i)² = ∑_{i,j} a_i a_j via Finset.sum_mul_sum.
  have h_expand : ∀ ω,
      (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                - W.W (H.partition i.castSucc) ω))^2
      = ∑ i : Fin H.N, ∑ j : Fin H.N,
          (H.ξ i ω * (W.W (H.partition i.succ) ω
                    - W.W (H.partition i.castSucc) ω)) *
          (H.ξ j ω * (W.W (H.partition j.succ) ω
                    - W.W (H.partition j.castSucc) ω)) := by
    intro ω; rw [sq]; exact Finset.sum_mul_sum _ _ _ _
  rw [show (fun ω => (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω))^2)
        = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N,
            (H.ξ i ω * (W.W (H.partition i.succ) ω
                      - W.W (H.partition i.castSucc) ω)) *
            (H.ξ j ω * (W.W (H.partition j.succ) ω
                      - W.W (H.partition j.castSucc) ω)) from funext h_expand]
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => MeasureTheory.integrable_finsetSum _
      (fun j _ => cross_sq_integrable W H i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _
    (fun j _ => cross_sq_integrable W H i j)]
  rw [Finset.sum_eq_single i]
  · -- j = i: diagonal Bochner
    have h_part_nn : 0 ≤ H.partition i.castSucc := by
      have : H.partition 0 ≤ H.partition i.castSucc :=
        H.partition_strictMono.monotone (Fin.zero_le _)
      rw [H.partition_zero] at this; exact this
    rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)) *
                       (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)))
          = fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                                - W.W (H.partition i.castSucc) ω))^2 from by
      funext ω; ring]
    exact simpleIntegral_diagonal_bochner W ℱ hℱ H i h_part_nn (h_adapt i)
  · -- j ≠ i: offDiagonal (with symmetry)
    intro j _ hj
    rcases lt_or_gt_of_ne hj with h_lt | h_gt
    · rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)) *
                         (H.ξ j ω * (W.W (H.partition j.succ) ω
                                  - W.W (H.partition j.castSucc) ω)))
            = fun ω => (H.ξ j ω * (W.W (H.partition j.succ) ω
                                  - W.W (H.partition j.castSucc) ω)) *
                       (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)) from by
        funext ω; ring]
      exact simpleIntegral_offDiagonal W ℱ hℱ H h_lt (h_adapt j) (h_adapt i)
    · exact simpleIntegral_offDiagonal W ℱ hℱ H h_gt (h_adapt i) (h_adapt j)
  · intro h_not; exact absurd (Finset.mem_univ _) h_not

-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **LHS reduction for Brownian Itô isometry on simples.** -/
lemma simpleIntegral_sq_lintegral_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∑ i : Fin H.N,
        ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
        ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  -- Expand simpleIntegral via simpleIntegral_eq_sum.
  simp_rw [simpleIntegral_eq_sum W H]
  -- Convert (‖x‖)² to ENNReal.ofReal(x²).
  have h_norm_sq_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal (x^2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖x‖^2 = x^2 from by rw [Real.norm_eq_abs, sq_abs]]
  rw [show (∫⁻ ω, (‖∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω)‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal
            ((∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)]
  -- Integrability of squared sum.
  have h_int_sum_sq : MeasureTheory.Integrable
      (fun ω => (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2) P := by
    have h_eq : ∀ ω, (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω))^2
                = ∑ i : Fin H.N, ∑ j : Fin H.N,
                  (H.ξ i ω * (W.W (H.partition i.succ) ω
                            - W.W (H.partition i.castSucc) ω)) *
                  (H.ξ j ω * (W.W (H.partition j.succ) ω
                            - W.W (H.partition j.castSucc) ω)) := by
      intro ω; rw [sq]; exact Finset.sum_mul_sum _ _ _ _
    rw [show (fun ω => (∑ i, H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2)
          = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N,
              (H.ξ i ω * (W.W (H.partition i.succ) ω
                        - W.W (H.partition i.castSucc) ω)) *
              (H.ξ j ω * (W.W (H.partition j.succ) ω
                        - W.W (H.partition j.castSucc) ω)) from funext h_eq]
    refine MeasureTheory.integrable_finsetSum _ (fun i _ => ?_)
    refine MeasureTheory.integrable_finsetSum _ (fun j _ => ?_)
    exact cross_sq_integrable W H i j
  have h_nn_sum_sq :
      0 ≤ᵐ[P] fun ω => (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2 := by
    filter_upwards with ω; exact sq_nonneg _
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_sum_sq h_nn_sum_sq]
  rw [simpleIntegral_sq_bochner_eq W ℱ hℱ H h_adapt]
  rw [show ENNReal.ofReal (∑ i : Fin H.N,
            (H.partition i.succ - H.partition i.castSucc) * ∫ ω, (H.ξ i ω)^2 ∂P)
        = ∑ i : Fin H.N,
          ENNReal.ofReal
            ((H.partition i.succ - H.partition i.castSucc) * ∫ ω, (H.ξ i ω)^2 ∂P) from by
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro i _
    refine mul_nonneg ?_ (MeasureTheory.integral_nonneg (fun ω => sq_nonneg _))
    have : H.partition i.castSucc < H.partition i.succ :=
      H.partition_strictMono Fin.castSucc_lt_succ
    linarith]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  obtain ⟨M, hM⟩ := H.ξ_bounded i
  have h_xi_sq_bound : ∀ ω : Ω, (H.ξ i ω)^2 ≤ M^2 := fun ω =>
    sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  have h_int_xi_sq : MeasureTheory.Integrable (fun ω => (H.ξ i ω)^2) P := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M^2)
      (MeasureTheory.integrable_const _) ?_ ?_
    · exact ((H.ξ_measurable i).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h_xi_sq_bound ω
  have h_nn_xi_sq : 0 ≤ᵐ[P] fun ω => (H.ξ i ω)^2 := by
    filter_upwards with ω; positivity
  have h_dt_nn : 0 ≤ H.partition i.succ - H.partition i.castSucc :=
    sub_nonneg.mpr (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ))
  rw [ENNReal.ofReal_mul h_dt_nn]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_xi_sq h_nn_xi_sq]
  rw [show (fun ω => ENNReal.ofReal ((H.ξ i ω)^2))
        = fun ω => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 from
    funext (fun ω => (h_norm_sq_eq _).symm)]

/-- **Itô isometry on simple integrands.** The L²-norm of the simple integral
equals the L²-norm of the integrand against `dP ⊗ ds`. -/
lemma simpleIntegral_isometry
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (_hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  rw [simpleIntegral_sq_lintegral_eq W ℱ hℱ H h_adapt]
  rw [lintegral_eval_sq_outer H]

/-- **L² isometry on simple integrands (Bochner sum form).**
For an adapted simple predictable integrand
`H = ∑_i ξ_i · 1_{(t_i, t_{i+1}]}`,
`E[(∑_i ξ_i ΔB_i)²] = Σ_i (t_{i+1} - t_i) · E[ξ_i²]`.

Cross terms vanish by `simpleIntegral_offDiagonal` (which is the integral
form of the Brownian-increment martingale-difference property — see
`martingale_simpleIntegral_brownian`); the diagonal is computed in
`simpleIntegral_diagonal_bochner`. -/
theorem simpleIntegral_L2_isometry_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫ ω, (simpleIntegral W H T ω) ^ 2 ∂P
      = ∑ i : Fin H.N, (H.partition i.succ - H.partition i.castSucc) *
          ∫ ω, (H.ξ i ω) ^ 2 ∂P := by
  have h_eq : ∀ ω, (simpleIntegral W H T ω) ^ 2
      = (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)) ^ 2 := by
    intro ω; rw [simpleIntegral_eq_sum]
  simp_rw [h_eq]
  exact simpleIntegral_sq_bochner_eq W ℱ hℱ H h_adapt

/-- **Inner Bochner integral of `(H.eval s ω)²` over `s ∈ [0, T]`** equals
the sum of `(t_{i+1} - t_i) · (ξ_i ω)²` over partition pieces. Bochner
mirror of `lintegral_eval_sq`. -/
lemma integral_eval_sq {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω) :
    ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume
      = ∑ i : Fin H.N, (H.partition i.succ - H.partition i.castSucc) * (H.ξ i ω) ^ 2 := by
  -- Real version of `eval_sq_eq_sum_indicator`.
  have h_sq_decomp : ∀ s, (H.eval s ω) ^ 2 = ∑ i : Fin H.N,
      (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
        (fun _ => (H.ξ i ω) ^ 2) s := by
    intro s
    rw [eval_eq_sum_indicator]
    by_cases h_any : ∃ i : Fin H.N,
        s ∈ Set.Ioc (H.partition i.castSucc) (H.partition i.succ)
    · obtain ⟨i₀, hi₀⟩ := h_any
      have h_unique : ∀ j : Fin H.N, j ≠ i₀ →
          s ∉ Set.Ioc (H.partition j.castSucc) (H.partition j.succ) := by
        intro j hj hj_mem
        have := partition_intervals_disjoint H hj
        exact Set.disjoint_left.mp this hj_mem hi₀
      have h_sum_eq : (∑ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => H.ξ i ω) s) = H.ξ i₀ ω := by
        rw [Finset.sum_eq_single i₀]
        · exact Set.indicator_of_mem hi₀ _
        · intro j _ hj
          exact Set.indicator_of_notMem (h_unique j hj) _
        · intro h_not; exact absurd (Finset.mem_univ _) h_not
      have h_sum_sq_eq : (∑ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => (H.ξ i ω) ^ 2) s) = (H.ξ i₀ ω) ^ 2 := by
        rw [Finset.sum_eq_single i₀]
        · exact Set.indicator_of_mem hi₀ _
        · intro j _ hj
          exact Set.indicator_of_notMem (h_unique j hj) _
        · intro h_not; exact absurd (Finset.mem_univ _) h_not
      rw [h_sum_eq, h_sum_sq_eq]
    · push Not at h_any
      have h_zero_sq : ∀ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => (H.ξ i ω) ^ 2) s = 0 :=
        fun i => Set.indicator_of_notMem (h_any i) _
      have h_zero : ∀ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => H.ξ i ω) s = 0 :=
        fun i => Set.indicator_of_notMem (h_any i) _
      rw [Finset.sum_eq_zero (fun i _ => h_zero i),
          Finset.sum_eq_zero (fun i _ => h_zero_sq i)]
      simp
  simp_rw [h_sq_decomp]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    have h_meas_set : MeasurableSet
        (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)) := measurableSet_Ioc
    have h_subset : Set.Ioc (H.partition i.castSucc) (H.partition i.succ)
        ⊆ Set.Icc (0 : ℝ) T := by
      intro x hx
      have h_part_zero_le : 0 ≤ H.partition i.castSucc := by
        have : H.partition 0 ≤ H.partition i.castSucc :=
          H.partition_strictMono.monotone (Fin.zero_le _)
        rw [H.partition_zero] at this; exact this
      have h_part_succ_le_T : H.partition i.succ ≤ T := by
        refine le_trans ?_ H.partition_le_T
        exact H.partition_strictMono.monotone (Fin.le_last _)
      refine ⟨?_, ?_⟩
      · exact h_part_zero_le.trans (le_of_lt hx.1)
      · exact hx.2.trans h_part_succ_le_T
    have h_dt_nn : 0 ≤ H.partition i.succ - H.partition i.castSucc :=
      sub_nonneg.mpr (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ))
    rw [MeasureTheory.integral_indicator h_meas_set]
    rw [MeasureTheory.setIntegral_const]
    rw [MeasureTheory.measureReal_def]
    rw [MeasureTheory.Measure.restrict_apply h_meas_set]
    rw [Set.inter_eq_left.mpr h_subset]
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal h_dt_nn]
    rw [smul_eq_mul]
  · intro i _
    refine MeasureTheory.Integrable.indicator ?_ measurableSet_Ioc
    exact MeasureTheory.integrable_const _

/-- **Outer Bochner integral of `(H.eval)²` over `Ω × [0,T]`** equals the
sum of `(t_{i+1} - t_i) · ∫ (ξ_i)² ∂P`. Bochner mirror of
`lintegral_eval_sq_outer`. -/
lemma integral_eval_sq_outer
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (H : SimplePredictable Ω T) :
    ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume ∂P
      = ∑ i : Fin H.N, (H.partition i.succ - H.partition i.castSucc) *
          ∫ ω, (H.ξ i ω) ^ 2 ∂P := by
  have h_inner : ∀ ω, ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume
      = ∑ i : Fin H.N, (H.partition i.succ - H.partition i.castSucc) * (H.ξ i ω) ^ 2 :=
    fun ω => integral_eval_sq H ω
  rw [show (fun ω => ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume)
      = (fun ω => ∑ i : Fin H.N,
          (H.partition i.succ - H.partition i.castSucc) * (H.ξ i ω) ^ 2) from
    funext h_inner]
  -- Per-term integrability of `(t_{i+1} - t_i) · (ξ_i)²`.
  have h_int_term : ∀ i ∈ (Finset.univ : Finset (Fin H.N)),
      MeasureTheory.Integrable
        (fun ω => (H.partition i.succ - H.partition i.castSucc) * (H.ξ i ω) ^ 2) P := by
    intro i _
    refine MeasureTheory.Integrable.const_mul ?_ _
    obtain ⟨M, hM⟩ := H.ξ_bounded i
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M ^ 2)
      (MeasureTheory.integrable_const _) ?_ ?_
    · exact ((H.ξ_measurable i).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  rw [MeasureTheory.integral_finsetSum _ h_int_term]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_const_mul]

/-- **A2: L² isometry on simple integrands (Bochner integral form).**
For an adapted simple predictable integrand `H`,
`E[(simpleIntegral W H T)²] = ∫_0^T E[(H.eval s)²] ds`.

Combines `simpleIntegral_L2_isometry_brownian` (sum form) with
`integral_eval_sq_outer` (which expresses the same Σ in step-function
integral form). -/
theorem simpleIntegral_L2_isometry_brownian_integral_form
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫ ω, (simpleIntegral W H T ω) ^ 2 ∂P
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume ∂P := by
  rw [simpleIntegral_L2_isometry_brownian W ℱ hℱ H h_adapt]
  rw [integral_eval_sq_outer H]
end LevyStochCalc.Brownian.Ito
