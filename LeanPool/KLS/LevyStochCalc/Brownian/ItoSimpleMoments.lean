/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoSimpleIntegrand
public import LeanPool.KLS.LevyStochCalc.Brownian.Filtered

/-!
# Second moments of the terms of the elementary Brownian integral

For an adapted simple predictable integrand the diagonal term satisfies
`E[(ξ_i · ΔW_i) ^ 2] = (t_{i+1} - t_i) · E[ξ_i ^ 2]`, where
`ΔW_i = W_{t_{i+1}} - W_{t_i}`, since `ΔW_i` is independent of `ℱ_{t_i}` and centred Gaussian
with variance `t_{i+1} - t_i`, while for `i < j` the off-diagonal term vanishes,
`E[(ξ_i · ΔW_i) · (ξ_j · ΔW_j)] = 0`. Both rest on the integrability of the squared increments
and of the cross products.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Diagonal contribution: `E[ξ_i² · (W_{t_{i+1}} − W_{t_i})²]
= (t_{i+1} − t_i) · E[ξ_i²]`.

Proof: `(W_{t_{i+1}} − W_{t_i})²` is independent of `ξ_i²` (since the
increment is independent of `W_{t_i}`-past, and `ξ_i` is `F_{t_i}`-meas
by hypothesis `h_adapt`). The increment squared has expectation
`(t_{i+1} − t_i)` (Gaussian variance via `gaussianReal_second_moment`).

Hypotheses for the proof (added beyond what `SimplePredictable` provides):
* `h_part_nn`: the left endpoint `t_i := partition i.castSucc ≥ 0`,
  so the increment law applies.
* `h_adapt`: `ξ_i` is `ℱ t_i`-measurable. -/
lemma simpleIntegral_diagonal
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin H.N)
    (h_part_nn : 0 ≤ H.partition i.castSucc)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫⁻ ω,
      (‖H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω)‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
        ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  set s : ℝ := H.partition i.castSucc with hs_def
  set t : ℝ := H.partition i.succ with ht_def
  set ΔW : Ω → ℝ := fun ω => W.W t ω - W.W s ω with hΔW_def
  set ξ : Ω → ℝ := H.ξ i with hξ_def
  have hst : s < t := H.partition_strictMono Fin.castSucc_lt_succ
  have h_ξ_meas : Measurable ξ := H.ξ_measurable i
  have h_ΔW_meas : Measurable ΔW := (W.measurable_eval t).sub (W.measurable_eval s)
  -- Step 1: Show IndepFun ξ ΔW.
  -- By h_adapt, σ(ξ) ⊆ F_s. By joint_increment_independent, F_s ⊥ σ(ΔW).
  -- So σ(ξ) ⊥ σ(ΔW), i.e., IndepFun ξ ΔW.
  have h_indep_F_ΔW := hℱ.indep h_part_nn hst
  have h_ξ_comap_le : MeasurableSpace.comap ξ inferInstance ≤ ℱ s :=
    h_adapt.measurable.comap_le
  have h_indep_ξ_ΔW : ProbabilityTheory.IndepFun ξ ΔW P := by
    -- Indep σ(ξ) σ(ΔW) P, using h_indep_F_ΔW and σ(ξ) ⊆ F_s.
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : MeasurableSet[ℱ s] u := h_ξ_comap_le u hu
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW
    exact h_indep_F_ΔW u v hu_F hv
  -- Step 2: Compose with norm² to get IndepFun on ENNReal.
  have h_nn_meas : Measurable (fun x : ℝ => (‖x‖₊ : ℝ≥0∞)^2) := by fun_prop
  have h_indep_norm_sq :
      ProbabilityTheory.IndepFun
        (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2)
        (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞)^2) P := by
    have := h_indep_ξ_ΔW.comp h_nn_meas h_nn_meas
    simpa [Function.comp_def] using this
  -- Step 3: ‖ξ · ΔW‖₊² = ‖ξ‖₊² · ‖ΔW‖₊² pointwise.
  have h_norm_mul : ∀ ω, (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞)^2
      = (‖ξ ω‖₊ : ℝ≥0∞)^2 * (‖ΔW ω‖₊ : ℝ≥0∞)^2 := by
    intro ω
    rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞)
        = (‖ξ ω‖₊ : ℝ≥0∞) * (‖ΔW ω‖₊ : ℝ≥0∞) from by
      rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞)
          = ((‖ξ ω * ΔW ω‖₊ : ℝ≥0) : ℝ≥0∞) from rfl]
      rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0)
          = ‖ξ ω‖₊ * ‖ΔW ω‖₊ from nnNorm_mul _ _]
      push_cast; rfl]
    ring
  -- Step 4: Apply lintegral_mul for IndepFun.
  rw [show (∫⁻ ω, (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞)^2 * (‖ΔW ω‖₊ : ℝ≥0∞)^2 ∂P from
    MeasureTheory.lintegral_congr h_norm_mul]
  rw [show (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2 * (‖ΔW ω‖₊ : ℝ≥0∞)^2)
      = (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2)
        * (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞)^2) from rfl]
  have h_ξ_norm_sq_meas : Measurable (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2) := by fun_prop
  have h_ΔW_norm_sq_meas : Measurable (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞)^2) := by fun_prop
  rw [ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      h_ξ_norm_sq_meas h_ΔW_norm_sq_meas h_indep_norm_sq]
  -- Step 5: Compute ∫⁻ ‖ΔW‖₊² ∂P = ENNReal.ofReal(t - s).
  have h_ΔW_sq_int : ∫⁻ ω, (‖ΔW ω‖₊ : ℝ≥0∞)^2 ∂P
      = ENNReal.ofReal (t - s) := by
    -- Pushforward to gaussianReal:
    -- ∫⁻ ω, ‖ΔW‖₊² ∂P = ∫⁻ x, ‖x‖₊² ∂(P.map ΔW)
    --   = ∫⁻ x, ‖x‖₊² ∂(gaussianReal 0 ⟨t-s, _⟩)
    rw [show (∫⁻ ω, (‖ΔW ω‖₊ : ℝ≥0∞)^2 ∂P)
        = ∫⁻ x, (‖x‖₊ : ℝ≥0∞)^2 ∂(P.map ΔW) from
      (MeasureTheory.lintegral_map h_nn_meas h_ΔW_meas).symm]
    rw [W.increment_gaussian h_part_nn hst]
    -- ∫⁻ x, ‖x‖₊² ∂(gaussianReal 0 v) = ENNReal.ofReal v.
    -- Via ENNReal.ofReal of ∫ x², which equals v by gaussianReal_second_moment.
    have h_int_sq : MeasureTheory.Integrable (fun x : ℝ => x^2)
        (ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) := by
      have h_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 2
          (ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) :=
        ProbabilityTheory.memLp_id_gaussianReal' 2 (by simp)
      have h := h_memLp.integrable_norm_pow (p := 2) (by norm_num)
      convert h using 1
      ext x
      change x^2 = ‖x‖^2
      rw [Real.norm_eq_abs, sq_abs]
    have h_nn_sq : 0 ≤ᵐ[ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩]
        fun x : ℝ => x^2 := by
      filter_upwards with x
      positivity
    have h_norm_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal (x^2) := by
      intro x
      rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from
            ofReal_norm x |>.symm]
      rw [← ENNReal.ofReal_pow (norm_nonneg _)]
      rw [show ‖x‖^2 = x^2 from by rw [Real.norm_eq_abs, sq_abs]]
    rw [show (∫⁻ x, (‖x‖₊ : ℝ≥0∞)^2 ∂(ProbabilityTheory.gaussianReal 0
                ⟨t - s, by linarith⟩))
        = ∫⁻ x, ENNReal.ofReal (x^2) ∂(ProbabilityTheory.gaussianReal 0
                ⟨t - s, by linarith⟩) from
      MeasureTheory.lintegral_congr (fun x => h_norm_eq x)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_sq h_nn_sq]
    rw [LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment ⟨t - s, by linarith⟩]
    rfl
  rw [h_ΔW_sq_int]
  ring

/-- **Integrability of Brownian increment squared.** For `0 ≤ s < t`,
`(W_t − W_s)² ∈ L¹(P)`. Pushforward + Gaussian `MemLp 2`. -/
lemma brownian_increment_sq_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {s t : ℝ} (h_s_nn : 0 ≤ s) (h_st : s < t) :
    MeasureTheory.Integrable (fun ω => (W.W t ω - W.W s ω)^2) P := by
  have h_meas : Measurable (fun ω => W.W t ω - W.W s ω) :=
    (W.measurable_eval t).sub (W.measurable_eval s)
  have h_law := W.increment_gaussian h_s_nn h_st
  -- Convert to integrability on the pushforward measure (gaussianReal).
  have h_x_sq_meas : Measurable (fun x : ℝ => x^2) :=
    measurable_id.pow_const 2
  rw [show (fun ω => (W.W t ω - W.W s ω)^2)
        = (fun x : ℝ => x^2) ∘ (fun ω => W.W t ω - W.W s ω) from rfl]
  rw [(MeasureTheory.integrable_map_measure (μ := P)
      (f := fun ω => W.W t ω - W.W s ω)
      h_x_sq_meas.aestronglyMeasurable h_meas.aemeasurable).symm]
  rw [h_law]
  -- Integrable (fun x => x²) (gaussianReal 0 ⟨t-s, _⟩) via MemLp 2 of id.
  have h_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 2
      (ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) :=
    ProbabilityTheory.memLp_id_gaussianReal' 2 (by simp)
  have h := h_memLp.integrable_norm_pow (p := 2) (by norm_num)
  convert h using 1
  ext x
  change x^2 = ‖x‖^2
  rw [Real.norm_eq_abs, sq_abs]

/-- **Bochner version of `simpleIntegral_diagonal`** for Brownian. -/
lemma simpleIntegral_diagonal_bochner
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin H.N)
    (h_part_nn : 0 ≤ H.partition i.castSucc)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫ ω, (H.ξ i ω * (W.W (H.partition i.succ) ω
                    - W.W (H.partition i.castSucc) ω))^2 ∂P
      = (H.partition i.succ - H.partition i.castSucc) *
        ∫ ω, (H.ξ i ω)^2 ∂P := by
  have hst : H.partition i.castSucc < H.partition i.succ :=
    H.partition_strictMono Fin.castSucc_lt_succ
  -- Common identity.
  have h_norm_sq_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal (x^2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖x‖^2 = x^2 from by rw [Real.norm_eq_abs, sq_abs]]
  have h_lint := simpleIntegral_diagonal W ℱ hℱ H i h_part_nn h_adapt
  rw [show (∫⁻ ω, (‖H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω)‖₊ : ℝ≥0∞)^2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  rw [show (∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞)^2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((H.ξ i ω)^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  -- Integrabilities.
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
  have h_int_ΔW_sq : MeasureTheory.Integrable
      (fun ω => (W.W (H.partition i.succ) ω
                - W.W (H.partition i.castSucc) ω)^2) P :=
    brownian_increment_sq_integrable W h_part_nn hst
  have h_int_aN_sq : MeasureTheory.Integrable
      (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                - W.W (H.partition i.castSucc) ω))^2) P := by
    have h_eq : ∀ ω, (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω))^2
              = (H.ξ i ω)^2 *
                (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω)^2 := fun ω => by ring
    rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2)
            = fun ω => (H.ξ i ω)^2 *
                (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω)^2 from funext h_eq]
    refine MeasureTheory.Integrable.bdd_mul (c := M^2) h_int_ΔW_sq
      ((H.ξ_measurable i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact h_xi_sq_bound ω
  have h_nn_xi_sq : 0 ≤ᵐ[P] fun ω => (H.ξ i ω)^2 := by
    filter_upwards with ω; positivity
  have h_nn_aN_sq : 0 ≤ᵐ[P] fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2 := by
    filter_upwards with ω; positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_aN_sq h_nn_aN_sq] at h_lint
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_xi_sq h_nn_xi_sq] at h_lint
  -- Combine ENNReal.ofReal of constant * ofReal of integral.
  have h_xi_int_nn : 0 ≤ ∫ ω, (H.ξ i ω)^2 ∂P :=
    MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)
  have h_aN_int_nn : 0 ≤ ∫ ω, (H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2 ∂P :=
    MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)
  have h_dt_nn : 0 ≤ H.partition i.succ - H.partition i.castSucc := sub_nonneg.mpr (le_of_lt hst)
  rw [show ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
          ENNReal.ofReal (∫ ω, (H.ξ i ω)^2 ∂P)
          = ENNReal.ofReal
              ((H.partition i.succ - H.partition i.castSucc) *
                ∫ ω, (H.ξ i ω)^2 ∂P) from
    (ENNReal.ofReal_mul h_dt_nn).symm] at h_lint
  have h_rhs_nn : 0 ≤ (H.partition i.succ - H.partition i.castSucc) *
                      ∫ ω, (H.ξ i ω)^2 ∂P :=
    mul_nonneg h_dt_nn h_xi_int_nn
  exact (ENNReal.ofReal_eq_ofReal_iff h_aN_int_nn h_rhs_nn).mp h_lint

/-- Off-diagonal vanishing: for `i < j`,
`E[ξ_i ξ_j · ΔW_i · ΔW_j] = 0`.

Proof: `ξ_j` is `F_{t_j}`-measurable, `ΔW_j ⊥ F_{t_j}` (independence of
increment from past), and `E[ΔW_j] = 0` (Gaussian mean). Then
`E[ξ_i ξ_j ΔW_i ΔW_j | F_{t_j}] = ξ_i ξ_j ΔW_i · E[ΔW_j | F_{t_j}]
= ξ_i ξ_j ΔW_i · 0 = 0`. -/
lemma simpleIntegral_offDiagonal
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T) {i j : Fin H.N} (hij : i < j)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    (h_adapt_j : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition j.castSucc)) (H.ξ j)) :
    ∫ ω, (H.ξ i ω * (W.W (H.partition i.succ) ω
                    - W.W (H.partition i.castSucc) ω)) *
         (H.ξ j ω * (W.W (H.partition j.succ) ω
                    - W.W (H.partition j.castSucc) ω)) ∂P = 0 := by
  set t_i_pre : ℝ := H.partition i.castSucc with hti0_def
  set t_i : ℝ := H.partition i.succ with hti_def
  set t_j_pre : ℝ := H.partition j.castSucc with htj0_def
  set t_j : ℝ := H.partition j.succ with htj_def
  set ΔW_i : Ω → ℝ := fun ω => W.W t_i ω - W.W t_i_pre ω
  set ΔW_j : Ω → ℝ := fun ω => W.W t_j ω - W.W t_j_pre ω
  set ξ_i : Ω → ℝ := H.ξ i
  set ξ_j : Ω → ℝ := H.ξ j
  -- Partition monotonicity
  have h_part_zero_le_i_pre : 0 ≤ t_i_pre := by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  have h_i_pre_lt : t_i_pre < t_i := H.partition_strictMono Fin.castSucc_lt_succ
  have h_i_le_j_pre : t_i ≤ t_j_pre := by
    apply H.partition_strictMono.monotone
    exact Fin.succ_le_castSucc_iff.mpr hij
  have h_j_pre_lt : t_j_pre < t_j := H.partition_strictMono Fin.castSucc_lt_succ
  have h_j_pre_nn : 0 ≤ t_j_pre := h_part_zero_le_i_pre.trans (le_of_lt h_i_pre_lt)
    |>.trans h_i_le_j_pre
  -- The integrand factors as f · ΔW_j where f := ξ_i · ΔW_i · ξ_j.
  -- f is F_{t_j_pre}-measurable.
  set f : Ω → ℝ := fun ω => ξ_i ω * ΔW_i ω * ξ_j ω
  have h_factored : (fun ω => (ξ_i ω * ΔW_i ω) * (ξ_j ω * ΔW_j ω))
      = fun ω => f ω * ΔW_j ω := by
    funext ω
    change (ξ_i ω * ΔW_i ω) * (ξ_j ω * ΔW_j ω)
      = ξ_i ω * ΔW_i ω * ξ_j ω * ΔW_j ω
    ring
  rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                      - W.W (H.partition i.castSucc) ω))
              * (H.ξ j ω * (W.W (H.partition j.succ) ω
                          - W.W (H.partition j.castSucc) ω)))
        = fun ω => f ω * ΔW_j ω from h_factored]
  -- Step 1: f is F_{t_j_pre}-measurable.
  have h_t_i_pre_le_t_j_pre : t_i_pre ≤ t_j_pre :=
    (le_of_lt h_i_pre_lt).trans h_i_le_j_pre
  have h_F_i_pre_le_j_pre :
      ℱ t_i_pre
        ≤ ℱ t_j_pre :=
    ℱ.mono h_t_i_pre_le_t_j_pre
  -- Use the σ-algebra independence: σ(f) ⊆ F_{t_j_pre}; σ(ΔW_j) ⊥ F_{t_j_pre}.
  -- Then E[f * ΔW_j] = E[f] * E[ΔW_j] = E[f] * 0 = 0.
  -- Setup: F-measurability of pieces.
  have h_W_t_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t_j_pre) (W.W t_i) :=
    (hℱ.measurable t_i).stronglyMeasurable.mono (ℱ.mono h_i_le_j_pre)
  have h_W_t_pre_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t_j_pre) (W.W t_i_pre) :=
    (hℱ.measurable t_i_pre).stronglyMeasurable.mono
      (ℱ.mono ((le_of_lt h_i_pre_lt).trans h_i_le_j_pre))
  have h_ΔW_i_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t_j_pre) ΔW_i :=
    h_W_t_meas.sub h_W_t_pre_meas
  have h_ξ_i_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t_j_pre) ξ_i :=
    h_adapt_i.mono h_F_i_pre_le_j_pre
  have h_f_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t_j_pre) f :=
    (h_ξ_i_F_meas.mul h_ΔW_i_F_meas).mul h_adapt_j
  -- Step 2: IndepFun f ΔW_j
  have h_indep_F_ΔW_j := hℱ.indep h_j_pre_nn h_j_pre_lt
  have h_f_meas : Measurable f :=
    ((H.ξ_measurable i).mul ((W.measurable_eval t_i).sub
      (W.measurable_eval t_i_pre))).mul (H.ξ_measurable j)
  have h_ΔW_j_meas : Measurable ΔW_j :=
    (W.measurable_eval t_j).sub (W.measurable_eval t_j_pre)
  have h_f_comap_le : MeasurableSpace.comap f inferInstance ≤ ℱ t_j_pre :=
    h_f_F_meas.measurable.comap_le
  have h_indep_f_ΔW_j : ProbabilityTheory.IndepFun f ΔW_j P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : MeasurableSet[ℱ t_j_pre] u := h_f_comap_le u hu
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW_j
    exact h_indep_F_ΔW_j u v hu_F hv
  -- Step 3: ∫ ΔW_j = 0 (Gaussian mean).
  have h_ΔW_j_mean : ∫ ω, ΔW_j ω ∂P = 0 := by
    rw [show ∫ ω, ΔW_j ω ∂P = ∫ x, x ∂(P.map ΔW_j) from
      (MeasureTheory.integral_map h_ΔW_j_meas.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (id : ℝ → ℝ) _)).symm]
    rw [W.increment_gaussian h_j_pre_nn h_j_pre_lt]
    exact ProbabilityTheory.integral_id_gaussianReal
  -- Step 4: E[f · ΔW_j] = E[f] · E[ΔW_j] = E[f] · 0 = 0.
  rw [show (fun ω => f ω * ΔW_j ω) = f * ΔW_j from rfl]
  rw [h_indep_f_ΔW_j.integral_mul_eq_mul_integral h_f_meas.aestronglyMeasurable
    h_ΔW_j_meas.aestronglyMeasurable]
  rw [h_ΔW_j_mean, mul_zero]

/-- **Integrability of cross product `(ξ_i ΔW_i)(ξ_j ΔW_j)`** for Brownian. -/
lemma cross_sq_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (i j : Fin H.N) :
    MeasureTheory.Integrable
      (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                          - W.W (H.partition i.castSucc) ω)) *
                (H.ξ j ω * (W.W (H.partition j.succ) ω
                          - W.W (H.partition j.castSucc) ω))) P := by
  have h_part_i_nn : 0 ≤ H.partition i.castSucc := by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  have h_part_j_nn : 0 ≤ H.partition j.castSucc := by
    have : H.partition 0 ≤ H.partition j.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  have h_st_i : H.partition i.castSucc < H.partition i.succ :=
    H.partition_strictMono Fin.castSucc_lt_succ
  have h_st_j : H.partition j.castSucc < H.partition j.succ :=
    H.partition_strictMono Fin.castSucc_lt_succ
  have h_int_i_sq := brownian_increment_sq_integrable W h_part_i_nn h_st_i
  have h_int_j_sq := brownian_increment_sq_integrable W h_part_j_nn h_st_j
  -- Integrability of ΔW_i · ΔW_j via AM-GM.
  have h_meas_i : Measurable (fun ω => W.W (H.partition i.succ) ω
                                     - W.W (H.partition i.castSucc) ω) :=
    (W.measurable_eval _).sub (W.measurable_eval _)
  have h_meas_j : Measurable (fun ω => W.W (H.partition j.succ) ω
                                     - W.W (H.partition j.castSucc) ω) :=
    (W.measurable_eval _).sub (W.measurable_eval _)
  have h_int_ΔW : MeasureTheory.Integrable
      (fun ω => (W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω)
              * (W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω)) P := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.Integrable.add (h_int_i_sq.const_mul (1/2 : ℝ))
        (h_int_j_sq.const_mul (1/2 : ℝ))) (h_meas_i.mul h_meas_j).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul]
    have : |W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω| *
           |W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω|
        ≤ (1/2) * (W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω)^2 +
          (1/2) * (W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω)^2 := by
      nlinarith [sq_abs (W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω),
                 sq_abs (W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω),
                 sq_nonneg (|W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω| -
                            |W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω|)]
    exact this
  -- (ξ_i · ΔW_i) · (ξ_j · ΔW_j) = (ξ_i · ξ_j) · (ΔW_i · ΔW_j). Bounded × integrable.
  obtain ⟨M_i, hM_i⟩ := H.ξ_bounded i
  obtain ⟨M_j, hM_j⟩ := H.ξ_bounded j
  have h_eq : ∀ ω, (H.ξ i ω * (W.W (H.partition i.succ) ω
                              - W.W (H.partition i.castSucc) ω)) *
                   (H.ξ j ω * (W.W (H.partition j.succ) ω
                              - W.W (H.partition j.castSucc) ω))
            = (H.ξ i ω * H.ξ j ω) *
              ((W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω) *
              (W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω)) :=
    fun ω => by ring
  rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                                 - W.W (H.partition i.castSucc) ω)) *
                     (H.ξ j ω * (W.W (H.partition j.succ) ω
                                 - W.W (H.partition j.castSucc) ω)))
        = fun ω => (H.ξ i ω * H.ξ j ω) *
                   ((W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω) *
                   (W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω)) from
    funext h_eq]
  refine MeasureTheory.Integrable.bdd_mul (c := |M_i| * |M_j|) h_int_ΔW
    ((H.ξ_measurable i).mul (H.ξ_measurable j)).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (le_trans (hM_i ω) (le_abs_self _))
    (le_trans (hM_j ω) (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)
end LevyStochCalc.Brownian.Ito
