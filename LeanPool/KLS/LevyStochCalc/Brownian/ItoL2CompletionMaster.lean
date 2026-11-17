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
-- source adaptations (deprecated names, proof-context visibility, `MemLp` as `eLpNorm`
-- finiteness, a `gcongr` side goal) listed in vendor/port.patch.
-- Modified 2026-10-31 by the KLS formalization project: pass the existing
-- `AEStronglyMeasurable` witnesses now taken by `eLpNorm_two_rpow_eq_lintegral_sq` and
-- `eLpNorm_sq_eq_lintegral_nnnorm_sq`
-- (Mathlib v4.35.0 `eLpNorm` change); proof-only change.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoL2CompletionCompensator

/-!
# Brownian Itô integral: the master approximating sequence

The master sequence `masterApprox` of adapted simple predictable integrands on the
growing horizons `[0, n + 1]`, its Cauchy property in `L²(P)` uniformly on compact
time intervals, the limit `masterLp` and `stochasticIntegralBrownianLp` in
`Lp ℝ 2 P`, and the process `stochasticIntegralBrownian` together with its
adaptedness, vanishing on negative times and `ℱ`-martingale property.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- Positivity of the master horizon `(n : ℝ) + 1`. -/
lemma master_horizon_pos (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity

/-- Positivity of the master tolerance `((n : ℝ≥0∞) + 1)⁻¹`. -/
private lemma master_tol_pos (n : ℕ) : (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ :=
  ENNReal.inv_pos.mpr (by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩)

/-- **Master approximating sequence.** For each `n`, an adapted `SimplePredictable`
on horizon `(n : ℝ) + 1` within `((n : ℝ≥0∞) + 1)⁻¹` of `H` in `L²([0, n+1] × Ω)`.
The horizons grow to `∞`; zero-extension lets these be compared across `n`. -/
noncomputable def masterApprox (n : ℕ) : SimplePredictable Ω ((n : ℝ) + 1) :=
  (exists_adaptedSimple_within ℱ H h_meas h_progMeas (master_horizon_pos n)
    (h_sq_int_global _ (master_horizon_pos n))
    (show (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ by exact master_tol_pos n)).choose

lemma masterApprox_adapt (n : ℕ) :
    ∀ i : Fin (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).partition i.castSucc))
        ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ i) :=
  (exists_adaptedSimple_within ℱ H h_meas h_progMeas (master_horizon_pos n)
    (h_sq_int_global _ (master_horizon_pos n)) (master_tol_pos n)).choose_spec.1

lemma masterApprox_within (n : ℕ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) ((n : ℝ) + 1),
      (‖H ω s - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ((n : ℝ≥0∞) + 1)⁻¹ :=
  (exists_adaptedSimple_within ℱ H h_meas h_progMeas (master_horizon_pos n)
    (h_sq_int_global _ (master_horizon_pos n)) (master_tol_pos n)).choose_spec.2

include hℱ in
/-- **Cross-horizon difference isometry for the master sequence.** Extending both
`masterApprox n` and `masterApprox m` to the common horizon `max n m + 2` (via
`appendInterval`, which leaves their `simpleIntegral` and `eval` unchanged), the
difference isometry gives `∫⁻‖Iₙ(t) − Iₘ(t)‖² = ∫⁻∫⁻_{[0,t]}‖Gₙ.eval − Gₘ.eval‖²`
for every `t ≥ 0`. -/
lemma masterApprox_diff_isometry (n m : ℕ) {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ ω, (‖simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t ω
        - simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global m) t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖(masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω
            - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global m).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P := by
  set Gn := masterApprox ℱ H h_meas h_progMeas h_sq_int_global n with hGn
  set Gm := masterApprox ℱ H h_meas h_progMeas h_sq_int_global m with hGm
  have hKn : Gn.partition (Fin.last Gn.N) < (max n m : ℝ) + 2 := by
    have h1 : Gn.partition (Fin.last Gn.N) ≤ (n : ℝ) + 1 := Gn.partition_le_T
    have h2 : (n : ℝ) ≤ (max n m : ℝ) := by exact_mod_cast Nat.le_max_left n m
    linarith
  have hKm : Gm.partition (Fin.last Gm.N) < (max n m : ℝ) + 2 := by
    have h1 : Gm.partition (Fin.last Gm.N) ≤ (m : ℝ) + 1 := Gm.partition_le_T
    have h2 : (m : ℝ) ≤ (max n m : ℝ) := by exact_mod_cast Nat.le_max_right n m
    linarith
  have h_eq : (Gn.appendInterval hKn).partition (Fin.last (Gn.appendInterval hKn).N)
      = (Gm.appendInterval hKm).partition (Fin.last (Gm.appendInterval hKm).N) :=
    (Gn.appendInterval_partition_last hKn).trans (Gm.appendInterval_partition_last hKm).symm
  have ha_n := Gn.appendInterval_adapt ℱ hKn (masterApprox_adapt ℱ H h_meas h_progMeas
    h_sq_int_global n)
  have ha_m := Gm.appendInterval_adapt ℱ hKm (masterApprox_adapt ℱ H h_meas h_progMeas
    h_sq_int_global m)
  have hiso := simpleIntegral_intermediate_diff_isometry W ℱ hℱ (Gn.appendInterval hKn)
    (Gm.appendInterval hKm) h_eq ha_n ha_m ht_nn
  have hL : ∫⁻ ω, (‖simpleIntegral W Gn t ω - simpleIntegral W Gm t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖simpleIntegral W (Gn.appendInterval hKn) t ω
          - simpleIntegral W (Gm.appendInterval hKm) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr (fun ω => ?_)
    rw [Gn.appendInterval_simpleIntegral W hKn t ω, Gm.appendInterval_simpleIntegral W hKm t ω]
  have hR : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Gn.eval s ω - Gm.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖(Gn.appendInterval hKn).eval s ω - (Gm.appendInterval hKm).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P := by
    refine lintegral_congr (fun ω => ?_)
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
    rw [Gn.appendInterval_eval hKn s ω, Gm.appendInterval_eval hKm s ω]
  rw [hL, hR]; exact hiso

/-- `((n : ℝ≥0∞) + 1)⁻¹ → 0`. -/
private lemma tendsto_master_tol :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
  have := ENNReal.tendsto_inv_nat_nhds_zero.comp hg
  refine this.congr (fun n => ?_)
  simp [Nat.cast_add_one]

/-- **Per-time eval convergence of the master sequence.** For each `t ≥ 0`,
`∫⁻∫⁻_{[0,t]}‖H − Gₙ.eval‖² → 0`: eventually (`t ≤ n+1`) it is `≤ ((n:ℝ≥0∞)+1)⁻¹`
by `Set.Icc` monotonicity + `masterApprox_within`, and that bound tends to `0`. -/
lemma masterApprox_eval_tendsto {t : ℝ} :
    Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_master_tol
    (Filter.Eventually.of_forall (fun n => bot_le)) ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈t⌉₊] with n hn
  have htn : t ≤ (n : ℝ) + 1 := by
    have h1 : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have h2 : (⌈t⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖H ω s - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) ((n : ℝ) + 1),
          (‖H ω s - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P :=
        MeasureTheory.lintegral_mono
          (fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right htn))
    _ ≤ ((n : ℝ≥0∞) + 1)⁻¹ := le_of_lt (masterApprox_within ℱ H h_meas h_progMeas h_sq_int_global n)

include hℱ in
/-- **Cauchy bound for the master integrals.** Via the cross-horizon difference
isometry + the triangle `‖a − b‖² ≤ 2(‖a − H‖² + ‖H − b‖²)`. -/
lemma masterApprox_cauchy_le (n m : ℕ) {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ ω, (‖simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t ω
        - simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global m) t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global m).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P) := by
  set Gn := masterApprox ℱ H h_meas h_progMeas h_sq_int_global n with hGn
  set Gm := masterApprox ℱ H h_meas h_progMeas h_sq_int_global m with hGm
  rw [masterApprox_diff_isometry W ℱ hℱ H h_meas h_progMeas h_sq_int_global n m ht_nn]
  -- abbreviations for the two error densities
  set A : Ω → ℝ → ℝ≥0∞ := fun ω s => (‖H ω s - Gn.eval s ω‖₊ : ℝ≥0∞) ^ 2 with hA
  set B : Ω → ℝ → ℝ≥0∞ := fun ω s => (‖H ω s - Gm.eval s ω‖₊ : ℝ≥0∞) ^ 2 with hB
  have h_point : ∀ ω, ∀ s,
      (‖Gn.eval s ω - Gm.eval s ω‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (A ω s + B ω s) := by
    intro ω s
    have hrw : Gn.eval s ω - Gm.eval s ω
        = -(H ω s - Gn.eval s ω) + (H ω s - Gm.eval s ω) := by ring
    rw [hrw, hA, hB]
    refine le_trans (sq_nnnorm_add_le_two_mul_brownian _ _) ?_
    rw [show ‖-(H ω s - Gn.eval s ω)‖₊ = ‖H ω s - Gn.eval s ω‖₊ from by rw [nnnorm_neg]]
  -- joint measurability of `A` and the `s`-section measurability
  have hH_pair : Measurable (fun p : Ω × ℝ => H p.1 p.2) := h_meas
  have hA_pair : Measurable (fun p : Ω × ℝ => A p.1 p.2) := by
    rw [hA]
    exact (((hH_pair.sub Gn.eval_jointly_measurable).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hB_pair : Measurable (fun p : Ω × ℝ => B p.1 p.2) := by
    rw [hB]
    exact (((hH_pair.sub Gm.eval_jointly_measurable).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hA_s : ∀ ω, Measurable (A ω) := fun ω =>
    hA_pair.comp (measurable_const.prodMk measurable_id)
  have hA_outer : Measurable (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, A ω s ∂volume) :=
    Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t)) hA_pair
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖Gn.eval s ω - Gm.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, 2 * (A ω s + B ω s) ∂volume ∂P :=
        MeasureTheory.lintegral_mono (fun ω =>
          MeasureTheory.lintegral_mono (fun s => h_point ω s))
    _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, A ω s ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, B ω s ∂volume ∂P) := by
        have h_inner : ∀ ω, (∫⁻ s in Set.Icc (0 : ℝ) t, 2 * (A ω s + B ω s) ∂volume)
            = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) t, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) t, B ω s ∂volume) := by
          intro ω
          rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
              MeasureTheory.lintegral_add_left' (hA_s ω).aemeasurable]
        rw [MeasureTheory.lintegral_congr h_inner,
            MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
            MeasureTheory.lintegral_add_left' hA_outer.aemeasurable]

/-- The master integral `simpleIntegral W (masterApprox n) t` lifted to `Lp ℝ 2 P`
(for `0 ≤ t ≤ n+1`; `0` otherwise). The Itô integral process is its `L²`-limit. -/
noncomputable def masterLp (t : ℝ) (n : ℕ) : MeasureTheory.Lp ℝ 2 P :=
  if h : 0 ≤ t ∧ t ≤ (n : ℝ) + 1 then
    (simpleIntegral_memLp_intermediate_brownian W ℱ hℱ (master_horizon_pos n)
      (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n) h.1 h.2).toLp
  else 0

include hℱ in
lemma masterLp_coeFn {t : ℝ} (n : ℕ) (ht_nn : 0 ≤ t) (htn : t ≤ (n : ℝ) + 1) :
    (masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n : Ω → ℝ)
      =ᵐ[P] fun ω => simpleIntegral W (masterApprox ℱ H h_meas h_progMeas
        h_sq_int_global n) t ω := by
  rw [masterLp, dite_eq_left ⟨ht_nn, htn⟩]
  exact MeasureTheory.MemLp.coeFn_toLp _

include hℱ in
/-- The Itô-integral process is `L²`-Cauchy at each time `t ≥ 0`. -/
lemma masterLp_cauchySeq {t : ℝ} (ht_nn : 0 ≤ t) :
    CauchySeq (fun n => masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n) := by
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  by_cases hε_top : ε = ⊤
  · refine ⟨⌈t⌉₊, fun m hm n hn => ?_⟩
    rw [hε_top]; exact lt_top_iff_ne_top.mpr (edist_ne_top _ _)
  · set δ : ℝ≥0∞ := ε ^ (2 : ℝ) / 4 with hδ
    have hε2_ne_top : ε ^ (2 : ℝ) ≠ ⊤ := by
      simp [hε_top]
    have hδ_pos : 0 < δ := by
      rw [hδ]; exact ENNReal.div_pos (ENNReal.rpow_pos hε hε_top).ne' (by norm_num)
    have htend := masterApprox_eval_tendsto (t := t) ℱ H h_meas h_progMeas h_sq_int_global
    have hev : ∀ᶠ k in Filter.atTop,
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖H ω s - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global k).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P < δ := htend (Iio_mem_nhds hδ_pos)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N0, hN0⟩ := hev
    refine ⟨max N0 ⌈t⌉₊, fun m hm n hn => ?_⟩
    have hmt : t ≤ (m : ℝ) + 1 := by
      have : (⌈t⌉₊ : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_max_right N0 ⌈t⌉₊).trans hm
      have := Nat.le_ceil t; linarith
    have hnt : t ≤ (n : ℝ) + 1 := by
      have : (⌈t⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_max_right N0 ⌈t⌉₊).trans hn
      have := Nat.le_ceil t; linarith
    have hmN0 : N0 ≤ m := (le_max_left N0 ⌈t⌉₊).trans hm
    have hnN0 : N0 ≤ n := (le_max_left N0 ⌈t⌉₊).trans hn
    -- edist = eLpNorm of the integral difference
    have em : masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t m
        = (simpleIntegral_memLp_intermediate_brownian W ℱ hℱ (master_horizon_pos m)
            (masterApprox ℱ H h_meas h_progMeas h_sq_int_global m)
            (masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global m) ht_nn hmt).toLp := by
      rw [masterLp]; exact dite_eq_left ⟨ht_nn, hmt⟩
    have en : masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n
        = (simpleIntegral_memLp_intermediate_brownian W ℱ hℱ (master_horizon_pos n)
            (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
            (masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n) ht_nn hnt).toLp := by
      rw [masterLp]; exact dite_eq_left ⟨ht_nn, hnt⟩
    have h_edist : edist (masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t m)
          (masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n)
        = MeasureTheory.eLpNorm
            (fun ω => simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global m) t ω
              - simpleIntegral W (masterApprox ℱ H h_meas h_progMeas
                h_sq_int_global n) t ω) 2 P := by
      rw [em, en]
      exact MeasureTheory.Lp.edist_toLp_toLp _ _ _ _
    rw [h_edist]
    -- eLpNorm² < ε²  ⇒  eLpNorm < ε
    have h_sq_lt : MeasureTheory.eLpNorm
        (fun ω => simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global m) t ω
          - simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t ω) 2 P
          ^ (2 : ℝ) < ε ^ (2 : ℝ) := by
      have hmeas : MeasureTheory.AEStronglyMeasurable
          (fun ω => simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global m) t ω
            - simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t ω) P :=
        (simpleIntegral_memLp_intermediate_brownian W ℱ hℱ (master_horizon_pos m)
            (masterApprox ℱ H h_meas h_progMeas h_sq_int_global m)
            (masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global m) ht_nn
            hmt).aestronglyMeasurable.sub
          (simpleIntegral_memLp_intermediate_brownian W ℱ hℱ (master_horizon_pos n)
            (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
            (masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n) ht_nn
            hnt).aestronglyMeasurable
      rw [eLpNorm_two_rpow_eq_lintegral_sq _ hmeas]
      refine lt_of_le_of_lt
        (masterApprox_cauchy_le W ℱ hℱ H h_meas h_progMeas h_sq_int_global m n ht_nn) ?_
      have hsum : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global m).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P < δ + δ :=
        ENNReal.add_lt_add (hN0 m hmN0) (hN0 n hnN0)
      calc 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
                (‖H ω s - (masterApprox ℱ H h_meas h_progMeas
                  h_sq_int_global m).eval s ω‖₊ : ℝ≥0∞) ^ 2
                  ∂volume ∂P)
              + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
                (‖H ω s - (masterApprox ℱ H h_meas h_progMeas
                  h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
                  ∂volume ∂P)
          < 2 * (δ + δ) := by gcongr; simp
        _ = ε ^ (2 : ℝ) := by
            have h4 : (2 : ℝ≥0∞) * (δ + δ) = 4 * δ := by ring
            rw [h4, hδ, ENNReal.mul_div_cancel (show (4 : ℝ≥0∞) ≠ 0 by norm_num)
              (show (4 : ℝ≥0∞) ≠ ⊤ by simp)]
    exact (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp h_sq_lt

/-- The **L² Itô integral process** as an `Lp ℝ 2 P`-valued function of time: the
`L²`-limit of the master integral sequence. -/
noncomputable def stochasticIntegralBrownianLp (t : ℝ) : MeasureTheory.Lp ℝ 2 P :=
  Filter.limUnder Filter.atTop (fun n => masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n)

include hℱ in
/-- Each master integral lies in `lpMeas` — it is `ℱ_t`-measurable. -/
lemma masterLp_mem_lpMeas (t : ℝ) (n : ℕ) :
    masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n
      ∈ MeasureTheory.lpMeas ℝ ℝ
        (ℱ t) 2 P := by
  rw [masterLp]
  split_ifs with h
  · rw [MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable]
    refine ((simpleIntegral_stronglyAdapted_brownian W ℱ hℱ
      (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n)
        t).aestronglyMeasurable).congr ?_
    exact (MeasureTheory.MemLp.coeFn_toLp _).symm
  · exact Submodule.zero_mem _

include hℱ in
/-- The Itô integral process lies in `lpMeas` at each time (closedness of `lpMeas`
+ the `L²`-Cauchy limit of `ℱ_t`-measurable master integrals). -/
lemma stochasticIntegralBrownianLp_mem_lpMeas (t : ℝ) :
    stochasticIntegralBrownianLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t
      ∈ MeasureTheory.lpMeas ℝ ℝ
        (ℱ t) 2 P := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hcs : CauchySeq (fun n => masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n) := by
    rcases le_or_gt 0 t with ht | ht
    · exact masterLp_cauchySeq W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht
    · have heq : (fun n => masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n)
          = fun _ => (0 : MeasureTheory.Lp ℝ 2 P) := by
        funext n; rw [masterLp, dite_eq_right (fun h => absurd h.1 (not_le.mpr ht))]
      rw [heq]; exact (tendsto_const_nhds (x := (0 : MeasureTheory.Lp ℝ 2 P))).cauchySeq
  rw [MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable]
  have hclosed : IsClosed {f : MeasureTheory.Lp ℝ 2 P |
      AEStronglyMeasurable[ℱ t]
        (↑↑f : Ω → ℝ) P} :=
    MeasureTheory.isClosed_aestronglyMeasurable
      (ℱ.le t)
  exact hclosed.mem_of_tendsto hcs.tendsto_limUnder
    (Filter.Eventually.of_forall
      (fun n => MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable.mp
        (masterLp_mem_lpMeas W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n)))

include hℱ in
/-- `↑↑(Flp t)` is `ℱ_t`-a.e.-strongly-measurable. -/
lemma stochasticIntegralBrownian_aesm (t : ℝ) :
    AEStronglyMeasurable[ℱ t]
      (↑↑(stochasticIntegralBrownianLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t) : Ω → ℝ) P :=
  MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable.mp
    (stochasticIntegralBrownianLp_mem_lpMeas W ℱ hℱ H h_meas h_progMeas h_sq_int_global t)

/-- The **L² Itô integral** `t ↦ ∫_0^t H_s dW_s` as a process `ℝ → Ω → ℝ`, taken as
the honest `ℱ_t`-measurable representative of the `L²`-limit. -/
noncomputable def stochasticIntegralBrownian (t : ℝ) : Ω → ℝ :=
  (stochasticIntegralBrownian_aesm W ℱ hℱ H h_meas h_progMeas h_sq_int_global t).mk
    (↑↑(stochasticIntegralBrownianLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t))

include hℱ in
/-- The integral process is a.e.-equal to the `L²`-limit's `coeFn`. -/
lemma stochasticIntegralBrownian_ae_eq (t : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t
      =ᵐ[P] (↑↑(stochasticIntegralBrownianLp W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global t) : Ω → ℝ) :=
  (stochasticIntegralBrownian_aesm W ℱ hℱ H h_meas h_progMeas h_sq_int_global t).ae_eq_mk.symm

include hℱ in
/-- The integral process is strongly adapted to the natural filtration. -/
lemma stochasticIntegralBrownian_stronglyAdapted :
    MeasureTheory.StronglyAdapted ℱ
      (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global) :=
  fun t => (stochasticIntegralBrownian_aesm W ℱ hℱ H h_meas h_progMeas
    h_sq_int_global t).stronglyMeasurable_mk

include hℱ in
/-- **L²-convergence of the master integrals to the Itô integral process.** -/
lemma masterApprox_tendsto_L2 {t : ℝ} (ht_nn : 0 ≤ t) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm
        (fun ω => simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t ω
          - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) 2 P)
      Filter.atTop (nhds 0) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set Flp := stochasticIntegralBrownianLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t with hFlp
  have h1 : Filter.Tendsto (fun n => masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n)
      Filter.atTop (nhds Flp) :=
    (masterLp_cauchySeq W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht_nn).tendsto_limUnder
  have hmem : MeasureTheory.MemLp (↑↑Flp : Ω → ℝ) 2 P := MeasureTheory.Lp.memLp Flp
  rw [← MeasureTheory.Lp.toLp_coeFn Flp hmem] at h1
  have h2 := (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm
    (fun n => masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n) (↑↑Flp) hmem).mp h1
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈t⌉₊] with n hn
  have hcn : t ≤ (n : ℝ) + 1 := by
    have h1' : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have h2' : (⌈t⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  refine MeasureTheory.eLpNorm_congr_ae ?_
  filter_upwards [masterLp_coeFn W ℱ hℱ H h_meas h_progMeas h_sq_int_global n ht_nn hcn,
    stochasticIntegralBrownian_ae_eq W ℱ hℱ H h_meas h_progMeas h_sq_int_global t] with ω hω hF
  simp only [Pi.sub_apply]
  rw [hω, hF]

include hℱ in
/-- For `t < 0` the integral process is the zero `Lp` element. -/
lemma stochasticIntegralBrownianLp_eq_zero_of_neg {t : ℝ} (ht : t < 0) :
    stochasticIntegralBrownianLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t = 0 := by
  rw [stochasticIntegralBrownianLp]
  have heq : (fun n => masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t n)
      = fun _ => (0 : MeasureTheory.Lp ℝ 2 P) := by
    funext n; rw [masterLp, dite_eq_right (fun h => absurd h.1 (not_le.mpr ht))]
  rw [heq]
  exact tendsto_const_nhds.limUnder_eq

include hℱ in
/-- For `t < 0` the integral process is a.e. zero. -/
lemma stochasticIntegralBrownian_ae_zero_of_neg {t : ℝ} (ht : t < 0) :
    stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t =ᵐ[P] 0 := by
  refine (stochasticIntegralBrownian_ae_eq W ℱ hℱ H h_meas h_progMeas h_sq_int_global t).trans ?_
  rw [stochasticIntegralBrownianLp_eq_zero_of_neg W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht]
  exact MeasureTheory.Lp.coeFn_zero ℝ 2 P

include hℱ in
/-- **Conjunct 1: the Itô integral process is a martingale** (wrt the natural
filtration). The master integrals are martingales, converge in `L¹` (from `L²`),
and `F` is adapted + integrable. -/
lemma martingale_stochasticIntegralBrownian :
    MeasureTheory.Martingale (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global)
      ℱ P := by
  refine martingale_of_tendsto_eLpNorm_one
    (M := fun n t => simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t)
    (fun n => martingale_simpleIntegral_brownian W ℱ hℱ
      (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n))
    (fun n t => (martingale_simpleIntegral_brownian W ℱ hℱ
      (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n)).integrable t)
    (stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H h_meas h_progMeas h_sq_int_global)
    (fun t => ((MeasureTheory.Lp.memLp _).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).congr
      (stochasticIntegralBrownian_ae_eq W ℱ hℱ H h_meas h_progMeas h_sq_int_global t).symm)
    (fun t => ?_)
  rcases le_or_gt 0 t with ht | ht
  · refine tendsto_eLpNorm_one_of_eLpNorm_two (fun n => ?_)
      (masterApprox_tendsto_L2 W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht)
    refine (Measurable.aestronglyMeasurable ?_).sub
      (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global t).mono
        (ℱ.le t)).aestronglyMeasurable)
    unfold simpleIntegral
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).mul
      ((W.measurable_eval _).sub (W.measurable_eval _))
  · have hzero : ∀ n, MeasureTheory.eLpNorm
        ((fun t' => simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t') t
          - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t) 1 P = 0 := by
      intro n
      have hfae : ((fun t' => simpleIntegral W
            (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t') t
          - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t) =ᵐ[P] 0 := by
        filter_upwards [stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H h_meas h_progMeas
          h_sq_int_global ht] with ω hF
        simp only [Pi.sub_apply, Pi.zero_apply,
          simpleIntegral_eq_zero_of_nonpos W _ (le_of_lt ht) ω, hF, sub_zero]
      rw [MeasureTheory.eLpNorm_congr_ae hfae, MeasureTheory.eLpNorm_zero]
    simp only [hzero]
    exact tendsto_const_nhds

/-- **Eval-L²-norm convergence.** `∫⁻∫⁻_{[0,T]}‖Gₙ.eval‖² → ∫⁻∫⁻_{[0,T]}‖H‖²`.
Lift both to `L²` of the product measure `P ⊗ vol|_{[0,T]}` (Tonelli); the `L²`
difference vanishes (`masterApprox_eval_tendsto`), so the norms converge. -/
lemma masterApprox_evalNorm_tendsto {T : ℝ} (hT : 0 < T) :
    Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P)
      Filter.atTop
      (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set ν : MeasureTheory.Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hν
  set Hp : Ω × ℝ → ℝ := fun p => H p.1 p.2 with hHp
  set Gp : ℕ → Ω × ℝ → ℝ := fun n p =>
    (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval p.2 p.1 with hGp
  have hHp_meas : Measurable Hp := h_meas
  have hGp_meas : ∀ n, Measurable (Gp n) := fun n =>
    (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval_jointly_measurable
  -- Tonelli bridge: `eLpNorm f 2 (P⊗ν) ^ 2 = ∫⁻∫⁻_{[0,T]} ‖f(ω,·)‖²`.
  have hbridge : ∀ (f : Ω × ℝ → ℝ), Measurable f →
      MeasureTheory.eLpNorm f 2 (P.prod ν) ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    intro f hf
    rw [eLpNorm_sq_eq_lintegral_nnnorm_sq f hf.aestronglyMeasurable,
        MeasureTheory.lintegral_prod _
          (((hf.nnnorm.coe_nnreal_ennreal).pow_const 2).aemeasurable)]
  -- `eLpNorm < ⊤` from finiteness of the squared mass.
  have hfin : ∀ (f : Ω × ℝ → ℝ), Measurable f →
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) →
      MeasureTheory.eLpNorm f 2 (P.prod ν) < ⊤ := by
    intro f hf hfin
    refine lt_top_iff_ne_top.mpr (fun h => hfin ?_)
    rw [← hbridge f hf, h, ENNReal.top_rpow_of_pos (by norm_num)]
  have hHmemLp : MeasureTheory.MemLp Hp 2 (P.prod ν) :=
    MeasureTheory.memLp_iff.mpr (hfin Hp hHp_meas (h_sq_int_global T hT).ne)
  have hGmemLp : ∀ n, MeasureTheory.MemLp (Gp n) 2 (P.prod ν) := fun n =>
    MeasureTheory.memLp_iff.mpr (hfin (Gp n) (hGp_meas n)
      (eval_lintegral_sq_finite (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) T).ne)
  -- `Gp n → Hp` in `L²(P⊗ν)`.
  have hdiff : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν))
      Filter.atTop (nhds 0) := by
    have hsq : ∀ n, MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν) ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P := by
      intro n
      rw [hbridge (Gp n - Hp) ((hGp_meas n).sub hHp_meas)]
      refine lintegral_congr (fun ω =>
        MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_))
      rw [Pi.sub_apply, hGp, hHp, ← nnnorm_neg]
      congr 1; ring_nf
    have h2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν) ^ (2 : ℝ))
        Filter.atTop (nhds 0) := by
      simp_rw [hsq]
      exact masterApprox_eval_tendsto (t := T) ℱ H h_meas h_progMeas h_sq_int_global
    have h3 := h2.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    refine h3.congr (fun n => ?_)
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  -- transfer to `Lp`, take norms.
  have hLp := (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => Gp n)
    (fun n => hGmemLp n) Hp hHmemLp).mpr hdiff
  have hnorm := hLp.enorm
  simp only [MeasureTheory.Lp.enorm_def] at hnorm
  have hnorm2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Gp n) 2 (P.prod ν))
      Filter.atTop (nhds (MeasureTheory.eLpNorm Hp 2 (P.prod ν))) := by
    rw [MeasureTheory.eLpNorm_congr_ae (MeasureTheory.MemLp.coeFn_toLp hHmemLp)] at hnorm
    refine hnorm.congr (fun n => ?_)
    exact MeasureTheory.eLpNorm_congr_ae (MeasureTheory.MemLp.coeFn_toLp (hGmemLp n))
  -- square and convert via the bridge.
  have := hnorm2.ennrpow_const 2
  simp_rw [hbridge _ (hGp_meas _)] at this
  rw [hbridge Hp hHp_meas] at this
  exact this

end MasterSequence

end LevyStochCalc.Brownian.Ito
