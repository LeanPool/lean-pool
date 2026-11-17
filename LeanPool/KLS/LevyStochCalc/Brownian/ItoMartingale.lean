/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoSimple
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoDensity

/-!
# Martingale property of the simple Brownian integral

`simpleIntegral W H` is a martingale w.r.t. any filtration `ℱ` for which `W` is a
Brownian motion and `H` is adapted (`martingale_simpleIntegral_brownian`), via the
conditional-expectation identity for `W`. Builds on `Brownian/ItoSimple.lean` and
`Brownian/ItoDensity.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Per-term integrability** for `simpleIntegral`: each summand
`ξ_i · (W_{t_{i+1} ∧ t} - W_{t_i ∧ t})` is integrable, since `ξ_i` is
bounded and the increment has finite first moment (Brownian Gaussian
increment law). -/
private lemma simpleIntegral_term_integrable_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin H.N) (t : ℝ) :
    MeasureTheory.Integrable
      (fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) t) ω
          - W.W (min (H.partition i.castSucc) t) ω)) P := by
  obtain ⟨M, hM⟩ := H.ξ_bounded i
  have h_int_diff : MeasureTheory.Integrable
      (fun ω => W.W (min (H.partition i.succ) t) ω
                - W.W (min (H.partition i.castSucc) t) ω) P :=
    (LevyStochCalc.Brownian.Martingale.brownianMotion_integrable W _).sub
      (LevyStochCalc.Brownian.Martingale.brownianMotion_integrable W _)
  refine MeasureTheory.Integrable.bdd_mul h_int_diff
    (H.ξ_measurable i).aestronglyMeasurable (c := |M|) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact (hM ω).trans (le_abs_self _)

/-- **Per-term `ℱ_t`-adaptedness** for `simpleIntegral`. For `t ≥ t_i` each
factor is `ℱ_t`-measurable; for `t < t_i` the term collapses to `0`. -/
private lemma simpleIntegral_term_adapted_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin H.N) (t : ℝ)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t)
      (fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) t) ω
          - W.W (min (H.partition i.castSucc) t) ω)) := by
  have hpre_lt_post : H.partition i.castSucc < H.partition i.succ :=
    H.partition_strictMono Fin.castSucc_lt_succ
  by_cases ht_pre : H.partition i.castSucc ≤ t
  · -- `pre_t ≤ t`: each factor is `F_t`-meas.
    have h_min_post_le_t : min (H.partition i.succ) t ≤ t := min_le_right _ _
    have h_min_pre_le_t : min (H.partition i.castSucc) t ≤ t := min_le_right _ _
    have h_W_post : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq t)
        (W.W (min (H.partition i.succ) t)) :=
      ((hℱ.measurable (min (H.partition i.succ) t)).stronglyMeasurable).mono (ℱ.mono
        h_min_post_le_t)
    have h_W_pre : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq t)
        (W.W (min (H.partition i.castSucc) t)) :=
      ((hℱ.measurable (min (H.partition i.castSucc) t)).stronglyMeasurable).mono (ℱ.mono
        h_min_pre_le_t)
    have h_xi : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq t) (H.ξ i) :=
      h_adapt_i.mono (ℱ.mono ht_pre)
    exact h_xi.mul (h_W_post.sub h_W_pre)
  · -- `t < pre_t`: integrand is identically 0.
    push Not at ht_pre
    have h_t_lt_post : t < H.partition i.succ := lt_trans ht_pre hpre_lt_post
    have h_min_pre_t : min (H.partition i.castSucc) t = t := min_eq_right (le_of_lt ht_pre)
    have h_min_post_t : min (H.partition i.succ) t = t := min_eq_right (le_of_lt h_t_lt_post)
    have h_zero : (fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω))
        = (fun _ : Ω => (0 : ℝ)) := by
      funext ω; rw [h_min_pre_t, h_min_post_t]; ring
    rw [h_zero]
    exact MeasureTheory.stronglyMeasurable_const

/-- **Per-term cond-exp identity, `pre_t ≤ s` case (Case A).**

Direct computation: pull out `ξ_i` (which is `F_{pre_t}`-meas, hence `F_s`-meas
since `s ≥ pre_t`); reduce to `P[W_{min post_t t} - W_{pre_t} | F_s]`. The
`W_{pre_t}` factor is `F_s`-meas (cond-exp = self), and
`P[W_{min post_t t} | F_s] =ᵐ W_{min post_t s}` follows from the Brownian
martingale property at the appropriate times (case-split on whether
`min post_t t ≤ s`). -/
private lemma simpleIntegral_term_condExp_brownian_main
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin H.N)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    {s t : ℝ} (hpre_le_s : H.partition i.castSucc ≤ s) (hst : s ≤ t) :
    P[fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω)
        | ℱ s]
      =ᵐ[P] fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) s) ω - W.W (min (H.partition i.castSucc) s) ω) := by
  have hpre_lt_post : H.partition i.castSucc < H.partition i.succ :=
    H.partition_strictMono Fin.castSucc_lt_succ
  have hpre_nn : 0 ≤ H.partition i.castSucc := by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  have hs_nn : 0 ≤ s := hpre_nn.trans hpre_le_s
  have hpre_le_t : H.partition i.castSucc ≤ t := hpre_le_s.trans hst
  have h_min_pre_s : min (H.partition i.castSucc) s = H.partition i.castSucc :=
    min_eq_left hpre_le_s
  have h_min_pre_t : min (H.partition i.castSucc) t = H.partition i.castSucc :=
    min_eq_left hpre_le_t
  rw [h_min_pre_s, h_min_pre_t]
  set s' := min (H.partition i.succ) s
  set t' := min (H.partition i.succ) t
  have hs'_le_s : s' ≤ s := min_le_right _ _
  have hs'_le_t' : s' ≤ t' := min_le_min (le_refl _) hst
  have h_le_F : ℱ.seq s ≤ ‹MeasurableSpace Ω› := ℱ.le' s
  have h_xi_Fs : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s) (H.ξ i) :=
    h_adapt_i.mono (ℱ.mono hpre_le_s)
  have h_W_pre_Fs : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
      (W.W (H.partition i.castSucc)) :=
    ((hℱ.measurable (H.partition i.castSucc)).stronglyMeasurable).mono (ℱ.mono hpre_le_s)
  have h_W_s'_Fs : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s) (W.W s') :=
    ((hℱ.measurable s').stronglyMeasurable).mono
      (ℱ.mono hs'_le_s)
  obtain ⟨M, hM⟩ := H.ξ_bounded i
  have h_int_xi_meas : Measurable (H.ξ i) := H.ξ_measurable i
  have h_int_W_t' : MeasureTheory.Integrable (W.W t') P :=
    LevyStochCalc.Brownian.Martingale.brownianMotion_integrable W _
  have h_int_W_pre : MeasureTheory.Integrable (W.W (H.partition i.castSucc)) P :=
    LevyStochCalc.Brownian.Martingale.brownianMotion_integrable W _
  have h_int_inc_t' : MeasureTheory.Integrable
      (fun ω => W.W t' ω - W.W (H.partition i.castSucc) ω) P :=
    h_int_W_t'.sub h_int_W_pre
  have h_int_g_t : MeasureTheory.Integrable
      (fun ω => H.ξ i ω * (W.W t' ω - W.W (H.partition i.castSucc) ω)) P := by
    refine MeasureTheory.Integrable.bdd_mul h_int_inc_t'
      h_int_xi_meas.aestronglyMeasurable (c := |M|) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]; exact (hM ω).trans (le_abs_self _)
  -- Pull out ξ.
  have h_pull := MeasureTheory.condExp_mul_of_aestronglyMeasurable_left
    (m := ℱ.seq s) (μ := P) (f := H.ξ i)
    (g := fun ω => W.W t' ω - W.W (H.partition i.castSucc) ω)
    h_xi_Fs.aestronglyMeasurable h_int_g_t h_int_inc_t'
  -- `P[W_{t'} | F_s] =ᵐ W_{s'}`.
  have h_W_t'_condExp : P[W.W t' | ℱ.seq s] =ᵐ[P] W.W s' := by
    by_cases ht'_s : t' ≤ s
    · -- `t' ≤ s`: `W_{t'}` is `F_s`-meas; show `t' = s'` to identify.
      have h_t'_eq_s' : t' = s' := by
        by_cases hs_post : s ≤ H.partition i.succ
        · have h_s'_eq_s : s' = s := min_eq_right hs_post
          have h_s_le_t' : s ≤ t' := le_min hs_post hst
          have h_t'_eq_s : t' = s := le_antisymm ht'_s h_s_le_t'
          rw [h_t'_eq_s, h_s'_eq_s]
        · push Not at hs_post
          have h_s'_post : s' = H.partition i.succ := min_eq_left hs_post.le
          have hpost_le_t : H.partition i.succ ≤ t := hs_post.le.trans hst
          have h_t'_post : t' = H.partition i.succ := min_eq_left hpost_le_t
          rw [h_t'_post, h_s'_post]
      have h_W_t'_self : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s) (W.W t') :=
        ((hℱ.measurable t').stronglyMeasurable).mono
          (ℱ.mono ht'_s)
      have h_self := MeasureTheory.condExp_of_stronglyMeasurable h_le_F h_W_t'_self h_int_W_t'
      rw [h_self, h_t'_eq_s']
    · -- `s < t'`: Brownian martingale at `s ≤ t'`, then identify `W_s = W_{s'}`.
      push Not at ht'_s
      have h_post_gt_s : s < H.partition i.succ := lt_of_lt_of_le ht'_s (min_le_left _ _)
      have h_s'_eq_s : s' = s := min_eq_right h_post_gt_s.le
      have h_W_eq := hℱ.condExp_eq hs_nn (le_of_lt ht'_s)
      filter_upwards [h_W_eq] with ω hω
      rw [hω, h_s'_eq_s]
  -- `P[W_{t'} - W_{pre_t} | F_s] =ᵐ W_{s'} - W_{pre_t}`.
  have h_inc_eq : P[fun ω => W.W t' ω - W.W (H.partition i.castSucc) ω | ℱ.seq s] =ᵐ[P]
      fun ω => W.W s' ω - W.W (H.partition i.castSucc) ω := by
    have h_sub := MeasureTheory.condExp_sub h_int_W_t' h_int_W_pre (ℱ.seq s)
    have h_W_pre_self := MeasureTheory.condExp_of_stronglyMeasurable
      h_le_F h_W_pre_Fs h_int_W_pre
    filter_upwards [h_sub, h_W_t'_condExp] with ω h_sub_ω h_W_t'_ω
    change P[W.W t' - W.W (H.partition i.castSucc) | ℱ.seq s] ω
      = W.W s' ω - W.W (H.partition i.castSucc) ω
    rw [h_sub_ω, Pi.sub_apply, h_W_t'_ω, h_W_pre_self]
  filter_upwards [h_pull, h_inc_eq] with ω h_pull_ω h_inc_eq_ω
  change P[H.ξ i * fun ω => W.W t' ω - W.W (H.partition i.castSucc) ω | ℱ.seq s] ω
    = H.ξ i ω * (W.W s' ω - W.W (H.partition i.castSucc) ω)
  rw [h_pull_ω, Pi.mul_apply, h_inc_eq_ω]

/-- **Per-term cond-exp identity (full)** for `simpleIntegral`. Dispatches to
the `pre_t ≤ s` helper, with tower argument when `s < pre_t ≤ t` and a
`g_t = 0` argument when `t < pre_t`. -/
private lemma simpleIntegral_term_condExp_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin H.N)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    {s t : ℝ} (hst : s ≤ t) :
    P[fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω)
        | ℱ s]
      =ᵐ[P] fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) s) ω - W.W (min (H.partition i.castSucc) s) ω) := by
  have hpre_lt_post : H.partition i.castSucc < H.partition i.succ :=
    H.partition_strictMono Fin.castSucc_lt_succ
  -- The integrand at time `u ≤ pre_t` collapses to `0`.
  have h_g_zero_le_pre : ∀ u, u ≤ H.partition i.castSucc →
      (fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) u) ω - W.W (min (H.partition i.castSucc) u) ω))
      = (fun _ : Ω => (0 : ℝ)) := by
    intro u hu
    have h_min_pre_u : min (H.partition i.castSucc) u = u := min_eq_right hu
    have h_min_post_u : min (H.partition i.succ) u = u :=
      min_eq_right (hu.trans hpre_lt_post.le)
    funext ω
    rw [h_min_pre_u, h_min_post_u]
    ring
  by_cases hs_pre : H.partition i.castSucc ≤ s
  · exact simpleIntegral_term_condExp_brownian_main W ℱ hℱ H i h_adapt_i hs_pre hst
  · push Not at hs_pre
    have hs_lt_pre : s ≤ H.partition i.castSucc := hs_pre.le
    have h_g_s_zero := h_g_zero_le_pre s hs_lt_pre
    by_cases ht_pre : H.partition i.castSucc ≤ t
    · -- Case B: `s < pre_t ≤ t`. Tower through `F_{pre_t}`.
      have h_main := simpleIntegral_term_condExp_brownian_main W ℱ hℱ H i h_adapt_i
        (le_refl (H.partition i.castSucc)) ht_pre
      have h_g_pre_zero := h_g_zero_le_pre (H.partition i.castSucc) (le_refl _)
      rw [h_g_pre_zero] at h_main
      -- `h_main : P[g_t | F_{pre_t}] =ᵐ 0`.
      have h_le_F_pre : ℱ.seq s ≤ ℱ.seq (H.partition i.castSucc) := ℱ.mono hs_lt_pre
      have h_tower := MeasureTheory.condExp_condExp_of_le
        (μ := P)
        (f := fun ω => H.ξ i ω *
          (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω))
        h_le_F_pre (ℱ.le' (H.partition i.castSucc))
      have h_outer_zero := MeasureTheory.condExp_congr_ae
        (m := ℱ.seq s) (μ := P) h_main
      have h_zero_const := MeasureTheory.condExp_const (μ := P) (ℱ.le' s) (0 : ℝ)
      rw [h_g_s_zero]
      filter_upwards [h_tower, h_outer_zero] with ω h_tower_ω h_outer_zero_ω
      rw [← h_tower_ω, h_outer_zero_ω, h_zero_const]
    · -- Case C: `t < pre_t`. Both `g_s` and `g_t` are `0`.
      push Not at ht_pre
      have ht_lt_pre : t ≤ H.partition i.castSucc := ht_pre.le
      have h_g_t_zero := h_g_zero_le_pre t ht_lt_pre
      rw [h_g_t_zero, h_g_s_zero]
      have h_const := MeasureTheory.condExp_const (μ := P) (ℱ.le' s) (0 : ℝ)
      rw [h_const]

/-- **Martingale property of `simpleIntegral` (Brownian)** — for a simple
predictable integrand `H` adapted to a filtration `ℱ` for which `W` is a Brownian
motion, `t ↦ simpleIntegral W H t` is a martingale wrt `ℱ`.

Proof: `simpleIntegral W H t = ∑_i ξ_i · (W_{t_{i+1} ∧ t} - W_{t_i ∧ t})`.
Adaptedness reduces to per-term `F_t`-measurability via
`Finset.stronglyMeasurable_fun_sum`; the cond-exp identity reduces to the
per-term identity via `condExp_finset_sum` + `eventuallyEq_sum`. -/
lemma martingale_simpleIntegral_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.Martingale (fun t : ℝ => simpleIntegral W H t)
      ℱ P := by
  refine ⟨?_, ?_⟩
  · -- StronglyAdapted: per-term + `Finset.stronglyMeasurable_fun_sum`.
    intro t
    change @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq t)
      (fun ω => ∑ i : Fin H.N,
        H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
                  - W.W (min (H.partition i.castSucc) t) ω))
    apply Finset.stronglyMeasurable_fun_sum
    intro i _
    exact simpleIntegral_term_adapted_brownian W ℱ hℱ H i t (h_adapt i)
  · -- Cond-exp identity: per-term + `condExp_finset_sum`.
    intro s t hst
    -- Rewrite each `simpleIntegral W H u` as a Pi-sum of per-term functions.
    have h_unfold_pi : ∀ u : ℝ, (fun ω => simpleIntegral W H u ω) =
        ∑ i : Fin H.N, (fun ω : Ω => H.ξ i ω *
          (W.W (min (H.partition i.succ) u) ω
            - W.W (min (H.partition i.castSucc) u) ω)) := by
      intro u
      ext ω
      rw [Finset.sum_apply]
      rfl
    change P[fun ω => simpleIntegral W H t ω | ℱ.seq s] =ᵐ[P]
      fun ω => simpleIntegral W H s ω
    rw [h_unfold_pi t, h_unfold_pi s]
    have h_int : ∀ i ∈ (Finset.univ : Finset (Fin H.N)),
        MeasureTheory.Integrable (fun ω => H.ξ i ω *
          (W.W (min (H.partition i.succ) t) ω
            - W.W (min (H.partition i.castSucc) t) ω)) P :=
      fun i _ => simpleIntegral_term_integrable_brownian W H i t
    have h_step1 := MeasureTheory.condExp_finsetSum h_int (m := ℱ.seq s)
    refine h_step1.trans ?_
    refine eventuallyEq_sum ?_
    intro i _
    exact simpleIntegral_term_condExp_brownian W ℱ hℱ H i (h_adapt i) hst

/-- **C0a: Density of simple Brownian-predictable processes in `L²(Ω × [0, T])`.**
For every `H ∈ L²(Ω × [0, T], dP ⊗ ds)`, there exists a sequence of
`SimplePredictable` integrands whose `eval`s converge to `H` in
`L²(P ⊗ ds)`-norm. Public re-export of the existing
`simplePredictable_dense_L2` under the roadmap's name. -/
theorem simplePredictable_dense_Lp_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) :=
  simplePredictable_dense_L2 hT H h_meas h_sq_int

end LevyStochCalc.Brownian.Ito
