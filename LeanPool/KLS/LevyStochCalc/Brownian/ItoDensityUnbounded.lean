/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
-- Modified 2026-10-31 by the KLS formalization project: drop the measurability arguments that
-- `eLpNorm_add_le` no longer takes and pass the one that `eLpNorm_nnreal_pow_eq_lintegral` now
-- takes in Mathlib v4.35.0 (proof-only change); the two private `eLpNorm` helpers keep their
-- measurability premises unchanged, with the now-unused binders renamed `_hf`/`_hg`/`_hfn`.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoDensityPredictableL2

/-!
# Density of the simple predictable processes in `L²`

Removal of the boundedness restriction by truncation: the `eLpNorm`/`lintegral`
dictionary on the product measure, and the density results `simplePredictable_dense_L2`
and `adaptedSimple_dense_L2_brownian` for an arbitrary square-integrable integrand.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Reverse triangle for eLpNorm (tsub form).** Standard consequence of
`eLpNorm_add_le`: `eLpNorm f - eLpNorm g ≤ eLpNorm (f - g)` (ENNReal truncated). -/
private lemma eLpNorm_sub_eLpNorm_le_eLpNorm_sub
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α}
    {f g : α → E}
    (_hf : MeasureTheory.AEStronglyMeasurable f μ)
    (_hg : MeasureTheory.AEStronglyMeasurable g μ) :
    MeasureTheory.eLpNorm f p μ - MeasureTheory.eLpNorm g p μ
      ≤ MeasureTheory.eLpNorm (f - g) p μ := by
  rw [tsub_le_iff_left]
  have h_decomp : f = g + (f - g) := by ext x; simp
  conv_lhs => rw [h_decomp]
  exact MeasureTheory.eLpNorm_add_le hp

/-- **L²-norm continuity from L²-difference vanishing.** If
`eLpNorm (fn n - f) p μ → 0`, then `eLpNorm (fn n) p μ → eLpNorm f p μ`.

Squeeze argument:
* upper bound `eLpNorm (fn n) ≤ eLpNorm f + eLpNorm (fn n - f)` from
  `fn n = f + (fn n - f)` plus triangle (`eLpNorm_add_le`);
* lower bound `eLpNorm f - eLpNorm (fn n - f) ≤ eLpNorm (fn n)` from
  the same decomposition with the role of `f` and `fn n` swapped.

Both bounds tend to `eLpNorm f` (upper via `Tendsto.const_add`, lower via
`ENNReal.Tendsto.sub`); squeeze closes the proof. -/
private lemma eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α}
    {f : α → E} {fn : ℕ → α → E}
    (_hf : MeasureTheory.AEStronglyMeasurable f μ)
    (_hfn : ∀ n, MeasureTheory.AEStronglyMeasurable (fn n) μ)
    (h_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fn n - f) p μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fn n) p μ) Filter.atTop
      (nhds (MeasureTheory.eLpNorm f p μ)) := by
  have h_upper : ∀ n, MeasureTheory.eLpNorm (fn n) p μ ≤
      MeasureTheory.eLpNorm f p μ + MeasureTheory.eLpNorm (fn n - f) p μ := by
    intro n
    have h_decomp : fn n = f + (fn n - f) := by ext x; simp
    conv_lhs => rw [h_decomp]
    exact MeasureTheory.eLpNorm_add_le hp
  have h_lower : ∀ n,
      MeasureTheory.eLpNorm f p μ - MeasureTheory.eLpNorm (fn n - f) p μ
        ≤ MeasureTheory.eLpNorm (fn n) p μ := by
    intro n
    rw [tsub_le_iff_right]
    have h_decomp : f = fn n + -(fn n - f) := by ext x; simp
    calc MeasureTheory.eLpNorm f p μ
        = MeasureTheory.eLpNorm (fn n + -(fn n - f)) p μ := by rw [← h_decomp]
      _ ≤ MeasureTheory.eLpNorm (fn n) p μ
            + MeasureTheory.eLpNorm (-(fn n - f)) p μ :=
          MeasureTheory.eLpNorm_add_le hp
      _ = MeasureTheory.eLpNorm (fn n) p μ
            + MeasureTheory.eLpNorm (fn n - f) p μ := by
          rw [MeasureTheory.eLpNorm_neg]
  have h_lower_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm f p μ - MeasureTheory.eLpNorm (fn n - f) p μ)
      Filter.atTop (nhds (MeasureTheory.eLpNorm f p μ)) := by
    have h := ENNReal.Tendsto.sub
      (tendsto_const_nhds (x := MeasureTheory.eLpNorm f p μ))
      h_tendsto (Or.inr ENNReal.zero_ne_top)
    simpa using h
  have h_upper_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm f p μ + MeasureTheory.eLpNorm (fn n - f) p μ)
      Filter.atTop (nhds (MeasureTheory.eLpNorm f p μ)) := by
    have h := h_tendsto.const_add (MeasureTheory.eLpNorm f p μ)
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    h_lower_tendsto h_upper_tendsto h_lower h_upper

/-- **Bridge: nested-lintegral-of-squared-norm = `eLpNorm²` on product measure.**

For any `ℝ`-valued `h : Ω × ℝ → ℝ` measurable and `μ`-SFinite,
`∫⁻ ω, ∫⁻ s in Icc 0 T, ‖h (ω, s)‖₊² ∂vol ∂μ`
`  = eLpNorm h 2 (μ.prod (vol.restrict (Icc 0 T))) ^ 2`.
Tonelli + `eLpNorm_nnreal_pow_eq_lintegral` (instantiated at `p = 2`). -/
lemma lintegral_sq_eq_eLpNorm_sq_on_prod_brownian
    {μ : Measure Ω} {T : ℝ} (h : Ω × ℝ → ℝ) (hh : Measurable h) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖h (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
      = MeasureTheory.eLpNorm h 2
          (μ.prod (volume.restrict (Set.Icc (0 : ℝ) T))) ^ (2 : ℝ) := by
  set μν := μ.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμν
  have h_aem_sq : AEMeasurable
      (fun p : Ω × ℝ => (‖h p‖₊ : ℝ≥0∞) ^ 2) μν :=
    (hh.eNorm.pow_const 2).aemeasurable
  -- Tonelli on the squared integrand.
  have h_Tonelli :
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖h (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
        = ∫⁻ p, (‖h p‖₊ : ℝ≥0∞) ^ 2 ∂μν := by
    rw [MeasureTheory.lintegral_prod _ h_aem_sq]
  rw [h_Tonelli]
  -- Bridge: ∫⁻ p, (‖h p‖₊ : ℝ≥0∞)^2 ∂μν = eLpNorm h 2 μν ^ (2:ℝ).
  have h_pow_lemma := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
    (μ := μν) (p := (2 : NNReal)) (f := h)
    (by norm_num : (2 : NNReal) ≠ 0) hh.aestronglyMeasurable
  have h_two_R : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_num
  have h_two_ENNReal : ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) := by simp
  rw [h_two_ENNReal, h_two_R] at h_pow_lemma
  -- h_pow_lemma : eLpNorm h 2 μν ^ (2:ℝ) = ∫⁻ p, ‖h p‖ₑ ^ (2:ℝ) ∂μν
  rw [h_pow_lemma]
  -- Goal: ∫⁻ p, (‖h p‖₊ : ℝ≥0∞)^2 ∂μν
  --   = ∫⁻ p, ‖h p‖ₑ ^ (2:ℝ) ∂μν
  refine lintegral_congr (fun p => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rfl

/-- **General eval-norm-tendsto from diff-norm-tendsto, lintegral form.**

For any sequence of jointly-measurable `(p ↦ ev_n p.2 p.1)` and jointly-measurable
target `H` such that `∫⁻ ω, ∫⁻ s in [0,T], ‖H ω s - ev_n s ω‖₊² → 0`, we have
`∫⁻ ω, ∫⁻ s in [0,T], ‖ev_n s ω‖₊²`
`  → ∫⁻ ω, ∫⁻ s in [0,T], ‖H ω s‖₊²`.

Proof: bridge to `eLpNorm² _ 2 (μ.prod (vol.restrict (Icc 0 T)))` via Tonelli; the
square-root step gives `eLpNorm (F - Fn) → 0`; reverse-triangle squeeze
(`eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero`) closes; square back. -/
lemma lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian
    {μ : Measure Ω}
    {T : ℝ}
    (H : Ω → ℝ → ℝ) (h_H_meas : Measurable (Function.uncurry H))
    (ev : ℕ → ℝ → Ω → ℝ)
    (h_ev_meas : ∀ n, Measurable (fun (p : Ω × ℝ) => ev n p.2 p.1))
    (h_L2_diff : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      Filter.atTop
      (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)) := by
  set μν := μ.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμν
  set F : Ω × ℝ → ℝ := fun p => H p.1 p.2 with hF_def
  set Fn : ℕ → Ω × ℝ → ℝ := fun n p => ev n p.2 p.1 with hFn_def
  have h_F_meas : Measurable F := h_H_meas
  have h_Fn_meas : ∀ n, Measurable (Fn n) := h_ev_meas
  have h_F_aestrong : MeasureTheory.AEStronglyMeasurable F μν :=
    h_F_meas.stronglyMeasurable.aestronglyMeasurable
  have h_Fn_aestrong : ∀ n, MeasureTheory.AEStronglyMeasurable (Fn n) μν :=
    fun n => (h_Fn_meas n).stronglyMeasurable.aestronglyMeasurable
  have h_diff_meas : ∀ n, Measurable (F - Fn n) := fun n => h_F_meas.sub (h_Fn_meas n)
  -- Bridge each lintegral_sq form to its eLpNorm² counterpart.
  have h_F_bridge : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
        = MeasureTheory.eLpNorm F 2 μν ^ (2 : ℝ) :=
    lintegral_sq_eq_eLpNorm_sq_on_prod_brownian (μ := μ) F h_F_meas
  have h_Fn_bridge : ∀ n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
        = MeasureTheory.eLpNorm (Fn n) 2 μν ^ (2 : ℝ) := fun n =>
    lintegral_sq_eq_eLpNorm_sq_on_prod_brownian (μ := μ) (Fn n) (h_Fn_meas n)
  have h_diff_bridge : ∀ n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s - ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
        = MeasureTheory.eLpNorm (F - Fn n) 2 μν ^ (2 : ℝ) := fun n =>
    lintegral_sq_eq_eLpNorm_sq_on_prod_brownian (μ := μ) (T := T)
      (F - Fn n) (h_diff_meas n)
  -- Convert L²-converges (lintegral form) into eLpNorm² → 0.
  have h_eLpNorm_sq_diff_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν ^ (2 : ℝ))
      Filter.atTop (nhds 0) := by
    have h_eq : (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν ^ (2 : ℝ))
        = (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s - ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ) := by
      funext n
      exact (h_diff_bridge n).symm
    rw [h_eq]
    exact h_L2_diff
  -- Square root: eLpNorm² → 0 ⟹ eLpNorm → 0 (via rpow continuity at 0).
  have h_eLpNorm_diff_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν)
      Filter.atTop (nhds 0) := by
    have h_rpow : (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν)
        = (fun n => (MeasureTheory.eLpNorm (F - Fn n) 2 μν ^ (2 : ℝ)) ^ ((1 / 2 : ℝ))) := by
      funext n
      rw [← ENNReal.rpow_mul, show ((2 : ℝ) * (1 / 2)) = 1 from by norm_num,
          ENNReal.rpow_one]
    rw [h_rpow]
    have h := h_eLpNorm_sq_diff_tendsto.ennrpow_const (1 / 2 : ℝ)
    simpa [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using h
  -- Reverse triangle continuity: eLpNorm (Fn n - F) → 0 ⟹ eLpNorm Fn n → eLpNorm F.
  have h_diff_swap : ∀ n,
      MeasureTheory.eLpNorm (Fn n - F) 2 μν
        = MeasureTheory.eLpNorm (F - Fn n) 2 μν := by
    intro n
    have h_neg : Fn n - F = -(F - Fn n) := by ext p; simp [sub_eq_neg_add]
    rw [h_neg, MeasureTheory.eLpNorm_neg]
  have h_eLpNorm_diff_swap_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (Fn n - F) 2 μν)
      Filter.atTop (nhds 0) := by
    have h_eq : (fun n => MeasureTheory.eLpNorm (Fn n - F) 2 μν)
        = (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν) := funext h_diff_swap
    rw [h_eq]
    exact h_eLpNorm_diff_tendsto
  have h_eLpNorm_Fn_tendsto :=
    eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero
      (one_le_two : (1 : ℝ≥0∞) ≤ 2) h_F_aestrong h_Fn_aestrong h_eLpNorm_diff_swap_tendsto
  -- Square back: eLpNorm Fn n → eLpNorm F ⟹ eLpNorm² Fn n → eLpNorm² F.
  have h_eLpNorm_sq_Fn_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (Fn n) 2 μν ^ (2 : ℝ))
      Filter.atTop (nhds (MeasureTheory.eLpNorm F 2 μν ^ (2 : ℝ))) :=
    h_eLpNorm_Fn_tendsto.ennrpow_const 2
  -- Convert back to lintegral form via the bridges.
  have h_eq_func : (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      = (fun n => MeasureTheory.eLpNorm (Fn n) 2 μν ^ (2 : ℝ)) := funext h_Fn_bridge
  rw [h_eq_func, h_F_bridge]
  exact h_eLpNorm_sq_Fn_tendsto

/-- **Bounded dyadic eval lintegral_sq tendsto.** Specialization of
`lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian` to the
`predictableDyadicSimpleBrownian` sequence (bounded `g` case). -/
lemma predictableDyadicSimple_brownian_eval_norm_tendsto_bounded
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(predictableDyadicSimpleBrownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop
      (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) :=
  lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian (μ := P) (T := T) g h_meas
    (fun n => (predictableDyadicSimpleBrownian hT g h_meas M h_bound n).eval)
    (fun n => predictableDyadicSimple_brownian_eval_jointly_measurable hT g h_meas
      M h_bound n)
    (predictableDyadicSimple_brownian_L2_converges (P := P) hT g h_meas M h_bound)

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Adapted density (Brownian).** Every progressively-measurable
`H ∈ L²(Ω × [0,T], dP ⊗ ds)` is the L²-limit of ADAPTED simple predictable
integrands.

Mirrors `simplePredictable_dense_L2` but produces adapted simples when `H`
is progressively measurable. Uses `predictableDyadicSimpleBrownian` (the
left-shifted dyadic average construction) via
`adaptedSimple_dense_L2_bounded_brownian`. -/
lemma adaptedSimple_dense_L2_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (hT : 0 < T)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      (∀ n : ℕ, ∀ i : Fin (Hn n).N,
        @MeasureTheory.StronglyMeasurable Ω ℝ _
          (ℱ ((Hn n).partition i.castSucc)) ((Hn n).ξ i)) ∧
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) := by
  -- Truncation preserves measurability + progressive measurability.
  have h_clip_bound : ∀ M : ℕ, ∀ ω s,
      |max (-(M : ℝ)) (min (M : ℝ) (H ω s))| ≤ (M : ℝ) := by
    intro M ω s
    have h_M_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    rw [abs_le]
    refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have h_clip_meas : ∀ M : ℕ, Measurable
      (Function.uncurry (fun (ω : Ω) (s : ℝ) =>
        max (-(M : ℝ)) (min (M : ℝ) (H ω s)))) := by
    intro M
    have h : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
    exact h.comp h_meas
  -- Progressive measurability preserved under continuous clip.
  have h_clip_progMeas : ∀ M : ℕ, Probability.ProgressivelyMeasurable ℱ
      (fun ω s => max (-(M : ℝ)) (min (M : ℝ) (H ω s))) := by
    intro M
    have h_clip_cont : Continuous (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by
      fun_prop
    have h_clip_zero : max (-(M : ℝ)) (min (M : ℝ) 0) = 0 := by
      rw [min_eq_right (Nat.cast_nonneg M), max_eq_right (neg_nonpos.mpr (Nat.cast_nonneg M))]
    exact h_clip_cont.comp_progressivelyMeasurable h_clip_zero h_progMeas
  -- Apply bounded adapted-density.
  have h_bdd : ∀ M : ℕ, ∃ Hn : ℕ → SimplePredictable Ω T,
      (∀ n : ℕ, ∀ i : Fin (Hn n).N,
        @MeasureTheory.StronglyMeasurable Ω ℝ _
          (ℱ ((Hn n).partition i.castSucc)) ((Hn n).ξ i)) ∧
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖max (-(M : ℝ)) (min (M : ℝ) (H ω s)) - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P)
        Filter.atTop (nhds 0) :=
    fun M => adaptedSimple_dense_L2_bounded_brownian ℱ hT
      (fun ω s => max (-(M : ℝ)) (min (M : ℝ) (H ω s)))
      (h_clip_meas M) (h_clip_progMeas M) (M : ℝ) (h_clip_bound M)
  choose Hn_seq h_Hn_adapt h_Hn_seq using h_bdd
  -- Same diagonal selection as simplePredictable_dense_L2.
  have h_N : ∀ n : ℕ, ∃ N : ℕ, ∀ k ≥ N,
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
            - (Hn_seq n k).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P) ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have h_eps : ((n : ℝ≥0∞) + 1)⁻¹ > 0 := by
      apply ENNReal.inv_pos.mpr
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, by simp⟩
    exact (ENNReal.tendsto_atTop_zero.mp (h_Hn_seq n)) _ h_eps
  choose N_seq h_N_seq using h_N
  refine ⟨fun n => Hn_seq n (max n (N_seq n)), ?_, ?_⟩
  · -- Adaptedness inherited.
    intro n i
    exact h_Hn_adapt n (max n (N_seq n)) i
  -- Convergence: same proof as simplePredictable_dense_L2.
  have h_trunc := truncation_L2_converges_brownian H h_meas h_sq_int (T := T)
  rw [ENNReal.tendsto_atTop_zero] at h_trunc ⊢
  intro ε hε_pos
  have hε4_pos : (0 : ℝ≥0∞) < ε / 4 := by
    rw [ENNReal.div_pos_iff]
    refine ⟨hε_pos.ne', ?_⟩
    decide
  obtain ⟨N₁, hN₁⟩ := h_trunc (ε / 4) hε4_pos
  have h_inv_tendsto : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹)
      Filter.atTop (nhds 0) := by
    have h := ENNReal.tendsto_inv_nat_nhds_zero
    have hcomp :
        Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) :=
      h.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Nat.cast_add, Nat.cast_one] using hcomp
  obtain ⟨N₂, hN₂⟩ := (ENNReal.tendsto_atTop_zero.mp h_inv_tendsto) (ε / 4) hε4_pos
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  have h_pointwise : ∀ ω s,
      (‖H ω s - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
            + (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                  - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω s
    have h_sum : (H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
        + (max (-(n : ℝ)) (min (n : ℝ) (H ω s))
            - (Hn_seq n (max n (N_seq n))).eval s ω)
        = H ω s - (Hn_seq n (max n (N_seq n))).eval s ω := by ring
    have := sq_nnnorm_add_le_two_mul_brownian
      (H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
      (max (-(n : ℝ)) (min (n : ℝ) (H ω s))
        - (Hn_seq n (max n (N_seq n))).eval s ω)
    rw [h_sum] at this
    exact this
  set A : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖H ω s
      - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2 with hA
  set B : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                    - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hB
  set C : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖H ω s - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hC
  have h_C_le : ∀ ω s, C ω s ≤ 2 * (A ω s + B ω s) := h_pointwise
  have h_s_le : ∀ ω,
      (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume) ≤
        2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
          + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
    intro ω
    calc (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume)
        ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, 2 * (A ω s + B ω s) ∂volume :=
          MeasureTheory.lintegral_mono (h_C_le ω)
      _ = 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, (A ω s + B ω s) ∂volume := by
          rw [MeasureTheory.lintegral_const_mul']
          simp
      _ = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
          + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
          congr 1
          rw [MeasureTheory.lintegral_add_left']
          have h_meas_A_s : Measurable (fun s => A ω s) := by
            simp only [hA]
            exact ((by fun_prop : Measurable (fun s =>
              ‖H ω s
                - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊)).coe_nnreal_ennreal).pow_const 2
          exact h_meas_A_s.aemeasurable
  have h_double_le :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
      ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
    calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
        ≤ ∫⁻ ω,
            2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P :=
          MeasureTheory.lintegral_mono h_s_le
      _ = 2 * ∫⁻ ω,
            ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P := by
          rw [MeasureTheory.lintegral_const_mul']
          simp
      _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
          congr 1
          rw [MeasureTheory.lintegral_add_left']
          have h_meas_A_pair : Measurable (fun (q : Ω × ℝ) => A q.1 q.2) := by
            simp only [hA]
            exact ((by fun_prop : Measurable (fun (q : Ω × ℝ) =>
              ‖H q.1 q.2
                - max (-(n : ℝ)) (min (n : ℝ) (H q.1 q.2))‖₊)).coe_nnreal_ennreal)
                  |>.pow_const 2
          exact (Measurable.lintegral_prod_right'
            (ν := volume.restrict (Set.Icc (0:ℝ) T)) h_meas_A_pair).aemeasurable
  have h_first : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
      ∂volume ∂P) ≤ ε / 4 := hN₁ n hn₁
  have h_second : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
          - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2
      ∂volume ∂P) ≤ ε / 4 := by
    have h_max_ge : N_seq n ≤ max n (N_seq n) := le_max_right _ _
    exact (h_N_seq n (max n (N_seq n)) h_max_ge).trans (hN₂ n hn₂)
  calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P)
      ≤ 2 * (ε / 4 + ε / 4) := by
        refine h_double_le.trans ?_
        exact mul_le_mul_right (add_le_add h_first h_second) _
    _ = ε := by
        rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 from by norm_num]
        exact ENNReal.mul_div_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Density of simple predictable integrands in L².** Every
`H ∈ L²(Ω × [0,T], dP ⊗ ds)` is the L²-limit of simple predictable integrands. -/
lemma simplePredictable_dense_L2
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) := by
  -- For each M, get bounded approximation; pick diagonal.
  have h_clip_bound : ∀ M : ℕ, ∀ ω s,
      |max (-(M : ℝ)) (min (M : ℝ) (H ω s))| ≤ (M : ℝ) := by
    intro M ω s
    have h_M_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    rw [abs_le]
    refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have h_clip_meas : ∀ M : ℕ, Measurable
      (Function.uncurry
        (fun (ω : Ω) (s : ℝ) => max (-(M : ℝ)) (min (M : ℝ) (H ω s)))) := by
    intro M
    have h : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
    exact h.comp h_meas
  have h_bdd : ∀ M : ℕ, ∃ Hn : ℕ → SimplePredictable Ω T,
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖max (-(M : ℝ)) (min (M : ℝ) (H ω s)) - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P)
        Filter.atTop (nhds 0) :=
    fun M => simplePredictable_dense_L2_bounded_brownian hT
      (fun ω s => max (-(M : ℝ)) (min (M : ℝ) (H ω s)))
      (h_clip_meas M) (M : ℝ) (h_clip_bound M)
  choose Hn_seq h_Hn_seq using h_bdd
  have h_N : ∀ n : ℕ, ∃ N : ℕ, ∀ k ≥ N,
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
            - (Hn_seq n k).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P) ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have h_eps : ((n : ℝ≥0∞) + 1)⁻¹ > 0 := by
      apply ENNReal.inv_pos.mpr
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, by simp⟩
    exact (ENNReal.tendsto_atTop_zero.mp (h_Hn_seq n)) _ h_eps
  choose N_seq h_N_seq using h_N
  refine ⟨fun n => Hn_seq n (max n (N_seq n)), ?_⟩
  have h_trunc := truncation_L2_converges_brownian H h_meas h_sq_int (T := T)
  rw [ENNReal.tendsto_atTop_zero] at h_trunc ⊢
  intro ε hε_pos
  have hε4_pos : (0 : ℝ≥0∞) < ε / 4 := by
    rw [ENNReal.div_pos_iff]
    refine ⟨hε_pos.ne', ?_⟩
    decide
  obtain ⟨N₁, hN₁⟩ := h_trunc (ε / 4) hε4_pos
  have h_inv_tendsto : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹)
      Filter.atTop (nhds 0) := by
    have h := ENNReal.tendsto_inv_nat_nhds_zero
    have hcomp :
        Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) :=
      h.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Nat.cast_add, Nat.cast_one] using hcomp
  obtain ⟨N₂, hN₂⟩ := (ENNReal.tendsto_atTop_zero.mp h_inv_tendsto) (ε / 4) hε4_pos
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  -- Pointwise triangle inequality.
  have h_pointwise : ∀ ω s,
      (‖H ω s - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
            + (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                  - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω s
    have h_sum : (H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
        + (max (-(n : ℝ)) (min (n : ℝ) (H ω s))
            - (Hn_seq n (max n (N_seq n))).eval s ω)
        = H ω s - (Hn_seq n (max n (N_seq n))).eval s ω := by ring
    have := sq_nnnorm_add_le_two_mul_brownian
      (H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
      (max (-(n : ℝ)) (min (n : ℝ) (H ω s))
        - (Hn_seq n (max n (N_seq n))).eval s ω)
    rw [h_sum] at this
    exact this
  -- Abbreviate.
  set A : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖H ω s
      - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2 with hA
  set B : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                    - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hB
  set C : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖H ω s - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hC
  have h_C_le : ∀ ω s, C ω s ≤ 2 * (A ω s + B ω s) := h_pointwise
  -- Step 1: ∫⁻ s in Icc 0 T, C ω s ∂vol
  --   ≤ 2 * (∫⁻ s, A ω s ∂vol + ∫⁻ s, B ω s ∂vol).
  have h_s_le : ∀ ω,
      (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume) ≤
        2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
          + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
    intro ω
    calc (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume)
        ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, 2 * (A ω s + B ω s) ∂volume :=
          MeasureTheory.lintegral_mono (h_C_le ω)
      _ = 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, (A ω s + B ω s) ∂volume := by
          rw [MeasureTheory.lintegral_const_mul']
          simp
      _ = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
          + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
          congr 1
          rw [MeasureTheory.lintegral_add_left']
          have h_meas_A_s : Measurable (fun s => A ω s) := by
            simp only [hA]
            exact ((by fun_prop : Measurable (fun s =>
              ‖H ω s
                - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊)).coe_nnreal_ennreal).pow_const 2
          exact h_meas_A_s.aemeasurable
  -- Step 2: outer ∫⁻ ω.
  have h_double_le :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
      ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
    calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
        ≤ ∫⁻ ω,
            2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P :=
          MeasureTheory.lintegral_mono h_s_le
      _ = 2 * ∫⁻ ω,
            ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P := by
          rw [MeasureTheory.lintegral_const_mul']
          simp
      _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
          congr 1
          rw [MeasureTheory.lintegral_add_left']
          have h_meas_A_pair : Measurable (fun (q : Ω × ℝ) => A q.1 q.2) := by
            simp only [hA]
            exact ((by fun_prop : Measurable (fun (q : Ω × ℝ) =>
              ‖H q.1 q.2
                - max (-(n : ℝ)) (min (n : ℝ) (H q.1 q.2))‖₊)).coe_nnreal_ennreal)
                  |>.pow_const 2
          exact (Measurable.lintegral_prod_right'
            (ν := volume.restrict (Set.Icc (0:ℝ) T)) h_meas_A_pair).aemeasurable
  -- Apply bounds.
  have h_first : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
      ∂volume ∂P) ≤ ε / 4 := hN₁ n hn₁
  have h_second : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
          - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2
      ∂volume ∂P) ≤ ε / 4 := by
    have h_max_ge : N_seq n ≤ max n (N_seq n) := le_max_right _ _
    exact (h_N_seq n (max n (N_seq n)) h_max_ge).trans (hN₂ n hn₂)
  calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P)
      ≤ 2 * (ε / 4 + ε / 4) := by
        refine h_double_le.trans ?_
        exact mul_le_mul_right (add_le_add h_first h_second) _
    _ = ε := by
        rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 from by norm_num]
        exact ENNReal.mul_div_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)
end LevyStochCalc.Brownian.Ito
