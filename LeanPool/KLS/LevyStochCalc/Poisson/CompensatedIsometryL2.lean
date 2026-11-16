/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedIsometryOrthogonality

/-!
# L²-isometry of the simple compensated-Poisson integral

Expansion of `(∑_i ξ_i · Ñ(B_i))²` into its diagonal and off-diagonal terms, the resulting
isometry `∫⁻ ‖simpleIntegral N φ T‖² ∂P = ∫⁻ ∫⁻ ∫⁻ ‖φ.eval‖² ∂ν ∂volume ∂P` together with
its Bochner sum form `∑_i ν̂(fullRect i).toReal · ∫ ξ_i² ∂P`, the finiteness of the
`L²`-norm and the membership `MemLp (simpleIntegral N φ T) 2 P`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Bochner version of `simpleIntegral_diagonal`.** Converts the lintegral form to
the Bochner form via `ofReal_integral_eq_lintegral_ofReal`. -/
private lemma simpleIntegral_diagonal_bochner
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N)
    (h_part_nn : 0 ≤ φ.partition i.castSucc)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    ∫ ω, (φ.ξ i ω * N.compensated (φ.timeRect i T) ω)^2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T)).toReal *
        ∫ ω, (φ.ξ i ω)^2 ∂P := by
  -- Common identity: (‖x‖₊ : ℝ≥0∞)² = ENNReal.ofReal(x²) for x : ℝ.
  have h_norm_sq_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal (x^2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖x‖^2 = x^2 from by rw [Real.norm_eq_abs, sq_abs]]
  -- Get the lintegral version of diagonal.
  have h_lint := simpleIntegral_diagonal N ℱ hℱ φ i h_part_nn h_adapt
  -- Rewrite (‖·‖)² to ENNReal.ofReal(·²) on both sides.
  rw [show (∫⁻ ω,
        (‖φ.ξ i ω * N.compensated (φ.timeRect i T) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((φ.ξ i ω * N.compensated (φ.timeRect i T) ω)^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  rw [show (∫⁻ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((φ.ξ i ω)^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  -- Establish integrability of ξ_i² and (ξ_i · Ñ_i)².
  have h_xi_bound : ∃ M : ℝ, ∀ ω : Ω, |φ.ξ i ω| ≤ M := φ.ξ_bounded i
  obtain ⟨M, hM⟩ := h_xi_bound
  have h_xi_sq_bound : ∀ ω : Ω, (φ.ξ i ω)^2 ≤ M^2 := by
    intro ω
    have := sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
    exact this
  have h_int_xi_sq : MeasureTheory.Integrable (fun ω => (φ.ξ i ω)^2) P := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M^2)
      (MeasureTheory.integrable_const _) ?_ ?_
    · exact ((φ.ξ_measurable i).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h_xi_sq_bound ω
  have h_B_meas : MeasurableSet (φ.timeRect i T) := by
    unfold SimplePredictable.timeRect
    exact measurableSet_Ioc.prod (φ.A_measurable i)
  have h_finite : LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T) ≠ ⊤ := by
    unfold SimplePredictable.timeRect LevyStochCalc.Poisson.referenceIntensity
    rw [MeasureTheory.Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ (φ.A_finite i)
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.Measure.restrict_le_self _)
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have h_int_compensated_sq : MeasureTheory.Integrable
      (fun ω => (N.compensated (φ.timeRect i T) ω)^2) P :=
    compensated_sq_integrable N h_B_meas h_finite
  have h_int_aN_sq : MeasureTheory.Integrable
      (fun ω => (φ.ξ i ω * N.compensated (φ.timeRect i T) ω)^2) P := by
    -- (ξ_i · Ñ)² = ξ_i² · Ñ². Bounded × integrable.
    have h_eq : ∀ ω, (φ.ξ i ω * N.compensated (φ.timeRect i T) ω)^2
              = (φ.ξ i ω)^2 * (N.compensated (φ.timeRect i T) ω)^2 := fun ω => by ring
    rw [show (fun ω => (φ.ξ i ω * N.compensated (φ.timeRect i T) ω)^2)
            = fun ω => (φ.ξ i ω)^2 * (N.compensated (φ.timeRect i T) ω)^2 from
      funext h_eq]
    refine MeasureTheory.Integrable.bdd_mul (c := M^2) h_int_compensated_sq
      ((φ.ξ_measurable i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact h_xi_sq_bound ω
  have h_nn_xi_sq : 0 ≤ᵐ[P] fun ω => (φ.ξ i ω)^2 := by
    filter_upwards with ω; positivity
  have h_nn_aN_sq : 0 ≤ᵐ[P] fun ω => (φ.ξ i ω * N.compensated (φ.timeRect i T) ω)^2 := by
    filter_upwards with ω; positivity
  -- Apply ofReal_integral_eq_lintegral_ofReal to convert lintegral to ENNReal.ofReal of Bochner.
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_aN_sq h_nn_aN_sq] at h_lint
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_xi_sq h_nn_xi_sq] at h_lint
  -- h_lint : ofReal(∫ (ξ_i · Ñ)²) = ν̂ * ofReal(∫ ξ_i²)
  -- Combine ν̂ * ofReal(...) into ofReal of product.
  have h_xi_int_nn : 0 ≤ ∫ ω, (φ.ξ i ω)^2 ∂P :=
    MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)
  have h_aN_int_nn : 0 ≤ ∫ ω, (φ.ξ i ω * N.compensated (φ.timeRect i T) ω)^2 ∂P :=
    MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)
  rw [show LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T) *
          ENNReal.ofReal (∫ ω, (φ.ξ i ω)^2 ∂P)
          = ENNReal.ofReal
              ((LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T)).toReal *
                ∫ ω, (φ.ξ i ω)^2 ∂P) from by
    conv_lhs =>
      rw [show LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T)
            = ENNReal.ofReal
                (LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T)).toReal from
        (ENNReal.ofReal_toReal h_finite).symm]
    rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]] at h_lint
  -- h_lint: ENNReal.ofReal(∫ (ξ_i · Ñ)²) = ENNReal.ofReal(ν̂.toReal · ∫ ξ_i²)
  -- Apply ENNReal.ofReal injective on ≥ 0.
  have h_rhs_nn : 0 ≤ (LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T)).toReal *
                      ∫ ω, (φ.ξ i ω)^2 ∂P :=
    mul_nonneg ENNReal.toReal_nonneg h_xi_int_nn
  exact (ENNReal.ofReal_eq_ofReal_iff h_aN_int_nn h_rhs_nn).mp h_lint

/-- **`simpleIntegral` as a sum over `fullRect i` (drops the `min` in `timeRect`).** -/
lemma simpleIntegral_eq_sum_fullRect
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (ω : Ω) :
    simpleIntegral N φ T ω
      = ∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.fullRect i) ω := by
  unfold simpleIntegral SimplePredictable.timeRect SimplePredictable.fullRect
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 2
  have h_t_i_succ_le_T : φ.partition i.succ ≤ T :=
    le_trans (φ.partition_strictMono.monotone (Fin.le_last _)) φ.partition_le_T
  have h_t_i_pre_le_T : φ.partition i.castSucc ≤ T := by
    refine le_of_lt ?_
    exact (φ.partition_strictMono Fin.castSucc_lt_succ).trans_le h_t_i_succ_le_T
  rw [min_eq_left h_t_i_pre_le_T, min_eq_left h_t_i_succ_le_T]

/-- **Bochner integrability of `ξ_i² · Ñ_j²` (cross product of squares).**
For pairs of compensated Poisson increments, the squared product is integrable
because each compensated value has finite second moment and ξ's are bounded. -/
private lemma cross_sq_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i j : Fin φ.N) :
    MeasureTheory.Integrable
      (fun ω => (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
                (φ.ξ j ω * N.compensated (φ.fullRect j) ω)) P := by
  have h_B_i_meas : MeasurableSet (φ.fullRect i) := by
    unfold SimplePredictable.fullRect
    exact measurableSet_Ioc.prod (φ.A_measurable i)
  have h_B_j_meas : MeasurableSet (φ.fullRect j) := by
    unfold SimplePredictable.fullRect
    exact measurableSet_Ioc.prod (φ.A_measurable j)
  have h_finite_i : LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) ≠ ⊤ := by
    rw [φ.referenceIntensity_fullRect i]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (φ.A_finite i)
  have h_finite_j : LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect j) ≠ ⊤ := by
    rw [φ.referenceIntensity_fullRect j]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (φ.A_finite j)
  have h_int_i_sq : MeasureTheory.Integrable
      (fun ω => (N.compensated (φ.fullRect i) ω)^2) P :=
    compensated_sq_integrable N h_B_i_meas h_finite_i
  have h_int_j_sq : MeasureTheory.Integrable
      (fun ω => (N.compensated (φ.fullRect j) ω)^2) P :=
    compensated_sq_integrable N h_B_j_meas h_finite_j
  -- |Ñ_i · Ñ_j| ≤ ½(Ñ_i² + Ñ_j²) — Cauchy-Schwarz / AM-GM.
  -- So Ñ_i · Ñ_j is integrable.
  have h_int_NN : MeasureTheory.Integrable
      (fun ω => N.compensated (φ.fullRect i) ω * N.compensated (φ.fullRect j) ω) P := by
    have h_meas_i : Measurable (fun ω => N.compensated (φ.fullRect i) ω) := by
      change Measurable (fun ω => (N.N ω (φ.fullRect i)).toReal -
        (LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)).toReal)
      exact (ENNReal.measurable_toReal.comp (N.measurable_eval h_B_i_meas)).sub_const _
    have h_meas_j : Measurable (fun ω => N.compensated (φ.fullRect j) ω) := by
      change Measurable (fun ω => (N.N ω (φ.fullRect j)).toReal -
        (LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect j)).toReal)
      exact (ENNReal.measurable_toReal.comp (N.measurable_eval h_B_j_meas)).sub_const _
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.Integrable.add (h_int_i_sq.const_mul (1/2 : ℝ))
        (h_int_j_sq.const_mul (1/2 : ℝ))) (h_meas_i.mul h_meas_j).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    have h_amgm : |N.compensated (φ.fullRect i) ω * N.compensated (φ.fullRect j) ω|
              ≤ (1/2) * (N.compensated (φ.fullRect i) ω)^2 +
                (1/2) * (N.compensated (φ.fullRect j) ω)^2 := by
      rw [abs_mul]
      have := sq_nonneg (|N.compensated (φ.fullRect i) ω| - |N.compensated (φ.fullRect j) ω|)
      nlinarith [sq_abs (N.compensated (φ.fullRect i) ω),
                 sq_abs (N.compensated (φ.fullRect j) ω)]
    exact h_amgm
  -- (ξ_i · Ñ_i)(ξ_j · Ñ_j) = (ξ_i · ξ_j) · (Ñ_i · Ñ_j). Bounded × integrable.
  obtain ⟨M_i, hM_i⟩ := φ.ξ_bounded i
  obtain ⟨M_j, hM_j⟩ := φ.ξ_bounded j
  have h_eq : ∀ ω, (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
                   (φ.ξ j ω * N.compensated (φ.fullRect j) ω)
            = (φ.ξ i ω * φ.ξ j ω) *
              (N.compensated (φ.fullRect i) ω * N.compensated (φ.fullRect j) ω) :=
    fun ω => by ring
  rw [show (fun ω => (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
                     (φ.ξ j ω * N.compensated (φ.fullRect j) ω))
        = fun ω => (φ.ξ i ω * φ.ξ j ω) *
                   (N.compensated (φ.fullRect i) ω * N.compensated (φ.fullRect j) ω) from
    funext h_eq]
  refine MeasureTheory.Integrable.bdd_mul (c := |M_i| * |M_j|) h_int_NN
    ((φ.ξ_measurable i).mul (φ.ξ_measurable j)).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (le_trans (hM_i ω) (le_abs_self _))
    (le_trans (hM_j ω) (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)

/-- `timeRect i T = fullRect i` (under the partition's `partition_le_T` constraint). -/
lemma SimplePredictable.timeRect_eq_fullRect
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) :
    φ.timeRect i T = φ.fullRect i := by
  unfold SimplePredictable.timeRect SimplePredictable.fullRect
  have h_t_i_succ_le_T : φ.partition i.succ ≤ T :=
    le_trans (φ.partition_strictMono.monotone (Fin.le_last _)) φ.partition_le_T
  have h_t_i_pre_le_T : φ.partition i.castSucc ≤ T :=
    le_of_lt ((φ.partition_strictMono Fin.castSucc_lt_succ).trans_le h_t_i_succ_le_T)
  rw [min_eq_left h_t_i_pre_le_T, min_eq_left h_t_i_succ_le_T]

/-- Bochner diagonal restated in `fullRect` form. -/
private lemma simpleIntegral_diagonal_bochner_fullRect
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N)
    (h_part_nn : 0 ≤ φ.partition i.castSucc)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    ∫ ω, (φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)).toReal *
        ∫ ω, (φ.ξ i ω)^2 ∂P := by
  rw [← φ.timeRect_eq_fullRect i]
  exact simpleIntegral_diagonal_bochner N ℱ hℱ φ i h_part_nn h_adapt

/-- OffDiagonal restated in `fullRect` form. -/
private lemma simpleIntegral_offDiagonal_fullRect
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) {i j : Fin φ.N} (hij : i < j)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i))
    (h_adapt_j : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition j.castSucc)) (φ.ξ j)) :
    ∫ ω, (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
         (φ.ξ j ω * N.compensated (φ.fullRect j) ω) ∂P = 0 := by
  rw [← φ.timeRect_eq_fullRect i, ← φ.timeRect_eq_fullRect j]
  exact simpleIntegral_offDiagonal N ℱ hℱ φ hij h_adapt_i h_adapt_j

-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Bochner LHS reduction.** Expand `(∑ a_i)² = ∑_{i,j} a_i a_j` via `Finset.sum_mul_sum`,
apply linearity, then split into diagonal (i = j) and off-diagonal (i ≠ j) terms. -/
private lemma simpleIntegral_sq_bochner_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    ∫ ω, (∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2 ∂P
      = ∑ i : Fin φ.N,
        (LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)).toReal *
        ∫ ω, (φ.ξ i ω)^2 ∂P := by
  -- Expand (∑ a_i)² = ∑_{i,j} a_i a_j via Finset.sum_mul_sum.
  have h_expand : ∀ ω,
      (∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2
      = ∑ i : Fin φ.N, ∑ j : Fin φ.N,
          (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
          (φ.ξ j ω * N.compensated (φ.fullRect j) ω) := by
    intro ω; rw [sq]; exact Finset.sum_mul_sum _ _ _ _
  rw [show (fun ω => (∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2)
        = fun ω => ∑ i : Fin φ.N, ∑ j : Fin φ.N,
            (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
            (φ.ξ j ω * N.compensated (φ.fullRect j) ω) from funext h_expand]
  -- Pull out outer sum (by linearity of Bochner integral over finite sums)
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => MeasureTheory.integrable_finsetSum _
      (fun j _ => cross_sq_integrable N φ i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- Pull out inner sum
  rw [MeasureTheory.integral_finsetSum _
    (fun j _ => cross_sq_integrable N φ i j)]
  -- Now: ∑ j, ∫ (a_i a_j) ∂P. Split via Finset.sum_eq_single i.
  rw [Finset.sum_eq_single i]
  · -- Term at j = i: ∫ (a_i)² ∂P = ν̂(fullRect i).toReal · ∫ ξ_i²
    have h_part_nn : 0 ≤ φ.partition i.castSucc := by
      have : φ.partition 0 ≤ φ.partition i.castSucc :=
        φ.partition_strictMono.monotone (Fin.zero_le _)
      rw [φ.partition_zero] at this; exact this
    rw [show (fun ω => (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
                       (φ.ξ i ω * N.compensated (φ.fullRect i) ω))
          = fun ω => (φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2 from by
      funext ω; ring]
    exact simpleIntegral_diagonal_bochner_fullRect N ℱ hℱ φ i h_part_nn (h_adapt i)
  · -- Terms at j ≠ i: vanish via offDiagonal (with symmetry).
    intro j _ hj
    rcases lt_or_gt_of_ne hj with h_lt | h_gt
    · -- j < i: rearrange via mul_comm, apply offDiagonal with j < i.
      rw [show (fun ω => (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
                         (φ.ξ j ω * N.compensated (φ.fullRect j) ω))
            = fun ω => (φ.ξ j ω * N.compensated (φ.fullRect j) ω) *
                       (φ.ξ i ω * N.compensated (φ.fullRect i) ω) from by
        funext ω; ring]
      exact simpleIntegral_offDiagonal_fullRect N ℱ hℱ φ h_lt (h_adapt j) (h_adapt i)
    · -- i < j: direct offDiagonal.
      exact simpleIntegral_offDiagonal_fullRect N ℱ hℱ φ h_gt (h_adapt i) (h_adapt j)
  · intro h_not; exact absurd (Finset.mem_univ _) h_not

-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **LHS reduction for the Itô-Lévy isometry on simples.** The L²-norm-squared
of the simple integral equals the canonical sum form. Combines diagonal +
offDiagonal via Bochner expansion. -/
lemma simpleIntegral_sq_lintegral_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (_hT : 0 < T) (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∑ i : Fin φ.N,
        LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) *
        ∫⁻ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  -- Step 1: rewrite simpleIntegral as sum over fullRect.
  simp_rw [simpleIntegral_eq_sum_fullRect N φ]
  -- Step 2: convert (‖x‖)² to ENNReal.ofReal(x²).
  have h_norm_sq_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal (x^2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖x‖^2 = x^2 from by rw [Real.norm_eq_abs, sq_abs]]
  rw [show (∫⁻ ω,
        (‖∑ i, φ.ξ i ω * N.compensated (φ.fullRect i) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal
            ((∑ i, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)]
  -- Step 3: integrability and nonnegativity for ofReal_integral_eq_lintegral_ofReal.
  have h_int_sum_sq : MeasureTheory.Integrable
      (fun ω => (∑ i, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2) P := by
    -- (∑ a)² = ∑∑ a_i a_j; sum of integrables.
    have h_eq : ∀ ω, (∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2
                = ∑ i : Fin φ.N, ∑ j : Fin φ.N,
                  (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
                  (φ.ξ j ω * N.compensated (φ.fullRect j) ω) := by
      intro ω; rw [sq]; exact Finset.sum_mul_sum _ _ _ _
    rw [show (fun ω => (∑ i, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2)
          = fun ω => ∑ i : Fin φ.N, ∑ j : Fin φ.N,
              (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
              (φ.ξ j ω * N.compensated (φ.fullRect j) ω) from funext h_eq]
    refine MeasureTheory.integrable_finsetSum _ (fun i _ => ?_)
    refine MeasureTheory.integrable_finsetSum _ (fun j _ => ?_)
    exact cross_sq_integrable N φ i j
  have h_nn_sum_sq :
      0 ≤ᵐ[P] fun ω => (∑ i, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2 := by
    filter_upwards with ω; exact sq_nonneg _
  -- Step 4: apply ofReal_integral_eq_lintegral_ofReal
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_sum_sq h_nn_sum_sq]
  -- Step 5: apply Bochner LHS reduction.
  rw [simpleIntegral_sq_bochner_eq N ℱ hℱ φ h_adapt]
  -- Step 6: convert ENNReal.ofReal of finite sum to finite sum of ENNReal terms.
  rw [show
        ENNReal.ofReal (∑ i : Fin φ.N,
          (LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)).toReal *
          ∫ ω, (φ.ξ i ω)^2 ∂P)
        = ∑ i : Fin φ.N,
          ENNReal.ofReal
            ((LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)).toReal *
            ∫ ω, (φ.ξ i ω)^2 ∂P) from by
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro i _
    refine mul_nonneg ENNReal.toReal_nonneg ?_
    exact MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)]
  -- Step 7: each term: ofReal(ν̂.toReal · ∫ ξ²) = ν̂ · ofReal(∫ ξ²)
  --   = ν̂ · ∫⁻ ‖ξ‖².
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h_finite_i : LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) ≠ ⊤ := by
    rw [φ.referenceIntensity_fullRect i]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (φ.A_finite i)
  -- Bound ξ_i² by M_i² to get integrability.
  obtain ⟨M, hM⟩ := φ.ξ_bounded i
  have h_xi_sq_bound : ∀ ω : Ω, (φ.ξ i ω)^2 ≤ M^2 := fun ω =>
    sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  have h_int_xi_sq : MeasureTheory.Integrable (fun ω => (φ.ξ i ω)^2) P := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M^2)
      (MeasureTheory.integrable_const _) ?_ ?_
    · exact ((φ.ξ_measurable i).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h_xi_sq_bound ω
  have h_nn_xi_sq : 0 ≤ᵐ[P] fun ω => (φ.ξ i ω)^2 := by
    filter_upwards with ω; positivity
  -- ofReal(ν̂.toReal · ∫ ξ²) = ofReal(ν̂.toReal) · ofReal(∫ ξ²)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  -- ofReal(ν̂.toReal) = ν̂
  rw [ENNReal.ofReal_toReal h_finite_i]
  -- ofReal(∫ ξ²) = ∫⁻ ENNReal.ofReal(ξ²)
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_xi_sq h_nn_xi_sq]
  -- ∫⁻ ENNReal.ofReal(ξ²) = ∫⁻ (‖ξ‖)² (by h_norm_sq_eq backwards)
  rw [show (fun ω => ENNReal.ofReal ((φ.ξ i ω)^2))
        = fun ω => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 from
    funext (fun ω => (h_norm_sq_eq _).symm)]

lemma simpleIntegral_isometry
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (hT : 0 < T) (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [simpleIntegral_sq_lintegral_eq N ℱ hℱ hT φ h_adapt]
  rw [SimplePredictable.lintegral_eval_sq_outer φ]

/-- **B3 sum form: L² isometry (Bochner) for the compensated-Poisson simple
integral.** For an adapted simple `φ`,
`E[(simpleIntegral N φ T)²] = Σ_i ν̂(fullRect i).toReal · E[ξ_i²]`.

Combines `simpleIntegral_eq_sum_fullRect` (sum decomposition of the
integral at time `T`) with the existing private `simpleIntegral_sq_bochner_eq`. -/
theorem simpleIntegral_L2_isometry_compensatedPoisson_sumForm
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    ∫ ω, (simpleIntegral N φ T ω) ^ 2 ∂P
      = ∑ i : Fin φ.N,
        (LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)).toReal *
        ∫ ω, (φ.ξ i ω) ^ 2 ∂P := by
  have h_eq : ∀ ω, (simpleIntegral N φ T ω) ^ 2
      = (∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.fullRect i) ω) ^ 2 := by
    intro ω; rw [simpleIntegral_eq_sum_fullRect]
  simp_rw [h_eq]
  exact simpleIntegral_sq_bochner_eq N ℱ hℱ φ h_adapt

/-! ## C0b-Compensated mirror chain

The `simpleIntegral N φ T` lifted into `Lp ℝ 2 P` framework, mirroring
`Brownian.SimplePredictableRefine.simpleIntegralLp_brownian` etc. -/

/-- **Finite L²-norm of `simpleIntegral N φ T`.** Combines `simpleIntegral_isometry`
(which gives `∫⁻ ‖simpleIntegral‖² = ∑_i ν̂(rect_i) · ∫⁻ ξ_i²`) with the
boundedness of `ξ_i` and finiteness of `ν̂(rect_i) = (t_{i+1} - t_i) · ν(A_i)`. -/
lemma simpleIntegral_lintegral_sq_finite_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (hT : 0 < T) (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
  rw [simpleIntegral_isometry N ℱ hℱ hT φ h_adapt]
  rw [SimplePredictable.lintegral_eval_sq_outer φ]
  -- Goal: ∑ i, ν̂(fullRect i) * ∫⁻ ‖ξ i‖₊² ∂P < ⊤
  refine ENNReal.sum_lt_top.mpr (fun i _ => ?_)
  refine ENNReal.mul_lt_top ?_ ?_
  · -- ν̂(fullRect i) < ⊤. fullRect i = (partition i.castSucc, partition i.succ] × A_i.
    -- referenceIntensity = vol.restrict [0, ∞) ⊗ ν.
    -- ν̂(rect) = (length of time interval) · ν(A_i). Both finite.
    unfold LevyStochCalc.Poisson.referenceIntensity SimplePredictable.fullRect
    rw [MeasureTheory.Measure.prod_prod]
    refine ENNReal.mul_lt_top ?_ ?_
    · -- vol.restrict [0,∞) (Ioc s t) ≤ vol (Ioc s t) = ENNReal.ofReal (t - s) < ⊤.
      refine lt_of_le_of_lt
        (MeasureTheory.Measure.restrict_apply_le (Set.Ici (0 : ℝ)) _) ?_
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    · exact lt_of_le_of_ne le_top (φ.A_finite i)
  · -- ∫⁻ ω, ‖ξ i ω‖₊² ∂P < ⊤. ξ_i bounded ⟹ integrand bounded ⟹ finite
    --   on probability.
    obtain ⟨M, hM⟩ := φ.ξ_bounded i
    have h_bound : ∀ ω, |φ.ξ i ω| ≤ max M 0 :=
      fun ω => le_trans (hM ω) (le_max_left _ _)
    have h_M_nn : 0 ≤ max M 0 := le_max_right _ _
    have h_norm_le : ∀ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (max M 0) := by
      intro ω
      rw [show (‖φ.ξ i ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖φ.ξ i ω‖
            from (ofReal_norm _).symm]
      exact ENNReal.ofReal_le_ofReal (Real.norm_eq_abs _ ▸ h_bound ω)
    calc ∫⁻ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ _ω, (ENNReal.ofReal (max M 0)) ^ 2 ∂P := by
          refine MeasureTheory.lintegral_mono (fun ω => ?_)
          exact pow_le_pow_left' (h_norm_le ω) 2
      _ = (ENNReal.ofReal (max M 0)) ^ 2 * P Set.univ := by
          rw [MeasureTheory.lintegral_const]
      _ < ⊤ := by
          rw [MeasureTheory.measure_univ, mul_one]
          exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

/-- **`simpleIntegral N φ T` is in `L²(P)`.** Combines AEStronglyMeasurability
(via `Finset.sum` of measurable terms) with `simpleIntegral_lintegral_sq_finite_compensated`
to produce a `MemLp 2 P` witness. Lifts the simple integral into Mathlib's `Lp`
framework, needed for L²-Cauchy completion. -/
lemma simpleIntegral_memLp_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (hT : 0 < T) (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    MeasureTheory.MemLp (fun ω => simpleIntegral N φ T ω) 2 P := by
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun ω => simpleIntegral N φ T ω) P := by
    refine Measurable.aestronglyMeasurable ?_
    unfold simpleIntegral
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Measurable.mul (φ.ξ_measurable i) ?_
    -- N.compensated B = (N.N · B).toReal - ν̂(B).toReal. Measurable in ω.
    unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
    refine Measurable.sub ?_ measurable_const
    have h_meas_NB : Measurable (fun ω => N.N ω (φ.timeRect i T)) := by
      apply N.measurable_eval
      -- timeRect i T is measurable (Ioc × A_i with A_i measurable).
      unfold SimplePredictable.timeRect
      exact MeasurableSet.prod measurableSet_Ioc (φ.A_measurable i)
    exact ENNReal.measurable_toReal.comp h_meas_NB
  · rw [MeasureTheory.memLp_iff, MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ⊤) hmeas]
    have h_two_toReal : (2 : ℝ≥0∞).toReal = 2 := by simp
    rw [h_two_toReal]
    have h_pre := simpleIntegral_lintegral_sq_finite_compensated N ℱ hℱ hT φ h_adapt
    have h_rewrite : ∀ ω : Ω,
        (‖simpleIntegral N φ T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
          = (‖simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro ω
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
      rfl
    rw [show (fun ω => (‖simpleIntegral N φ T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ))
          = (fun ω => (‖simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2) from
        funext h_rewrite]
    exact h_pre

/-- **B1: Simple integral against compensated Poisson `Ñ` (renamed alias).**

This is the standard `simpleIntegral` in this namespace, exposed under the
roadmap's explicit name `simpleIntegral_compensatedPoisson`. Mathematical
content:
`∫ g dÑ := ∑_i ξ_i · Ñ((t_i, t_{i+1}] × A_i)`
where `Ñ(B) := N(B) − ν̂(B)` is the compensated random measure
(`PoissonRandomMeasure.compensated`); equivalently
`∫ g dÑ = ∫ g dN − ∫ g(z) ν(dz) dt` for simple `g`. -/
@[reducible] noncomputable def simpleIntegral_compensatedPoisson
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (t : ℝ) (ω : Ω) : ℝ :=
  simpleIntegral N φ t ω

end LevyStochCalc.Poisson.Compensated
