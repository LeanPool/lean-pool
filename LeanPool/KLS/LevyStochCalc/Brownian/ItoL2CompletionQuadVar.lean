/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0; proofs follow
-- the v4.35.0 `eLpNorm` and `MemLp` API (measurability arguments dropped or supplied, `MemLp` as
-- `eLpNorm` finiteness).
-- Modified 2026-10-31 by the KLS formalization project: pass the existing
-- `AEStronglyMeasurable` witnesses now taken by `eLpNorm_sq_eq_lintegral_nnnorm_sq`
-- (Mathlib v4.35.0 `eLpNorm` change); proof-only change.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoL2CompletionMaster

/-!
# Brownian Itô integral: isometry, right continuity and quadratic variation

The `L²`-isometry `∫⁻ ‖stochasticIntegralBrownian T‖₊² = ∫⁻ ∫⁻_{[0, T]} ‖H‖₊²`,
membership of the process in `L²(P)`, right `L²`-continuity of its time slices and
the resulting martingale property with respect to `ℱ.rightCont`, and the compensator
`∫_{[0, t]} (H ω u)² du` with the `ℱ`-martingale property of the compensated
square.
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

include hℱ in
/-- **Conjunct 3: the L²-isometry** `∫⁻‖F T‖² = ∫⁻∫⁻_{[0,T]}‖H‖²` for `T > 0`.
The squared `L²`-norm of `Iₙ(T)` equals `∫⁻∫⁻_{[0,T]}‖Gₙ.eval‖²` (intermediate
isometry), converges to `∫⁻‖F T‖²` (norm continuity of the `L²`-limit) and to
`∫⁻∫⁻_{[0,T]}‖H‖²` (`masterApprox_evalNorm_tendsto`); uniqueness of limits. -/
lemma isometry_stochasticIntegralBrownian {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set Flp := stochasticIntegralBrownianLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global T with hFlp
  have htend : Filter.Tendsto (fun n => masterLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global T n)
      Filter.atTop (nhds Flp) :=
    (masterLp_cauchySeq W ℱ hℱ H h_meas h_progMeas h_sq_int_global (le_of_lt hT)).tendsto_limUnder
  have hn := (htend.enorm).ennrpow_const 2
  simp only [MeasureTheory.Lp.enorm_def] at hn
  -- limit `eLpNorm ↑↑Flp ^ 2 = ∫⁻‖F T‖²`
  have hlim : MeasureTheory.eLpNorm (↑↑Flp : Ω → ℝ) 2 P ^ (2 : ℝ)
      = ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    rw [eLpNorm_sq_eq_lintegral_nnnorm_sq _ (MeasureTheory.Lp.aestronglyMeasurable Flp)]
    refine lintegral_congr_ae ?_
    filter_upwards [stochasticIntegralBrownian_ae_eq W ℱ hℱ H h_meas h_progMeas h_sq_int_global T]
      with ω hF
    rw [hF]
  rw [hlim] at hn
  have h_a : Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop
      (nhds (∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global T ω‖₊
        : ℝ≥0∞) ^ 2 ∂P)) := by
    refine hn.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ⌈T⌉₊] with n hn'
    have hcn : T ≤ (n : ℝ) + 1 := by
      have h1' : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
      have h2' : (⌈T⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
      linarith
    rw [MeasureTheory.eLpNorm_congr_ae
        (masterLp_coeFn W ℱ hℱ H h_meas h_progMeas h_sq_int_global n (le_of_lt hT) hcn),
      eLpNorm_sq_eq_lintegral_nnnorm_sq,
      simpleIntegral_intermediate_isometry W ℱ hℱ
        (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
        (masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n) (le_of_lt hT)]
    exact (simpleIntegral_memLp_intermediate_brownian W ℱ hℱ (master_horizon_pos n)
      (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n) (le_of_lt hT)
      hcn).aestronglyMeasurable
  exact tendsto_nhds_unique h_a
    (masterApprox_evalNorm_tendsto ℱ H h_meas h_progMeas h_sq_int_global hT)

include hℱ in
/-- `F t ∈ L²(P)`. -/
lemma stochasticIntegralBrownian_memLp (t : ℝ) :
    MeasureTheory.MemLp (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global t) 2 P :=
  (MeasureTheory.Lp.memLp _).ae_eq
    (stochasticIntegralBrownian_ae_eq W ℱ hℱ H h_meas h_progMeas h_sq_int_global t).symm

include hℱ in
/-- `F t =ᵐ 0` for `t ≤ 0`. -/
lemma stochasticIntegralBrownian_ae_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t =ᵐ[P] 0 := by
  rcases lt_or_eq_of_le ht with ht' | ht'
  · exact stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht'
  · subst ht'
    have h := masterApprox_tendsto_L2 W ℱ hℱ H h_meas h_progMeas h_sq_int_global (le_refl (0 : ℝ))
    have hconst : ∀ n, MeasureTheory.eLpNorm
        (fun ω => simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) 0 ω
          - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global 0 ω) 2 P
        = MeasureTheory.eLpNorm
          (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global 0) 2 P := by
      intro n
      rw [← MeasureTheory.eLpNorm_neg
        (f := stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global 0)]
      refine MeasureTheory.eLpNorm_congr_ae ?_
      filter_upwards with ω
      simp [simpleIntegral_eq_zero_of_nonpos W _ (le_refl (0 : ℝ)) ω]
    simp only [hconst] at h
    have hz : MeasureTheory.eLpNorm
        (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global 0) 2 P = 0 :=
      tendsto_nhds_unique tendsto_const_nhds h
    rwa [MeasureTheory.eLpNorm_eq_zero_iff (by norm_num)] at hz

include hℱ in
/-- `∫⁻‖F t‖² = ∫⁻∫⁻_{[0,t]}‖H‖²` for all `t ≥ 0` (isometry, incl. `t = 0`). -/
lemma stochasticIntegralBrownian_lintegral_sq {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  rcases lt_or_eq_of_le ht with ht' | ht'
  · exact isometry_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht'
  · subst ht'
    rw [lintegral_congr_ae (by
      filter_upwards [stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global (le_refl (0:ℝ))] with ω hω; rw [hω]; simp : _ =ᵐ[P] fun _ => (0:ℝ≥0∞))]
    rw [MeasureTheory.lintegral_zero]
    symm
    rw [← MeasureTheory.lintegral_zero (μ := P)]
    refine lintegral_congr (fun ω => ?_)
    rw [MeasureTheory.setLIntegral_measure_zero _ _ (by simp)]

include h_meas in
omit [IsProbabilityMeasure P] in
/-- Additivity of the horizon integral: `[0,r] = [0,s] ⊎ (s,r]`. -/
lemma horizon_lintegral_add {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ u in Set.Ioc s r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hinner : ∀ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume
        + ∫⁻ u in Set.Ioc s r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    rw [← Set.Icc_union_Ioc_eq_Icc hs hsr,
        MeasureTheory.lintegral_union measurableSet_Ioc
          (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)))]
  rw [MeasureTheory.lintegral_congr hinner]
  exact MeasureTheory.lintegral_add_left'
    ((Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) s))
      (((h_meas.nnnorm).coe_nnreal_ennreal).pow_const 2)).aemeasurable) _

include h_meas h_sq_int_global in
/-- Right-continuity of the horizon integral `r ↦ ∫⁻∫⁻_{[0,r]}‖H‖²` at `s ≥ 0`. -/
lemma horizon_lintegral_right_tendsto {s : ℝ} (hs : 0 ≤ s) :
    Filter.Tendsto (fun r => ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r,
        (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      (nhdsWithin s (Set.Ioi s))
      (nhds (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
  have hz : Filter.Tendsto (fun r => ∫⁻ ω, ∫⁻ u in Set.Ioc s r,
        (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) (nhdsWithin s (Set.Ioi s)) (nhds 0) :=
    tendsto_setLIntegral_Ioc_prod_zero (fun ω u => (‖H ω u‖₊ : ℝ≥0∞) ^ 2)
      ((h_meas.nnnorm.coe_nnreal_ennreal).pow_const 2) hs (lt_add_one s)
      (h_sq_int_global (s + 1) (by linarith)).ne
  have ht := (tendsto_const_nhds (x := ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s,
    (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)).add hz
  rw [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (horizon_lintegral_add H h_meas hs (le_of_lt hr)).symm

include hℱ in
/-- **Right-`L²`-continuity of the Itô integral process.** `‖F r − F s‖_{L²} → 0` as
`r ↓ s`. The squared increment `∫⁻‖F r − F s‖²` equals `ofReal((∫⁻∫⁻_{[0,r]}).toReal −
(∫⁻∫⁻_{[0,s]}).toReal)` (orthogonality + isometry) and `→ 0` by horizon
right-continuity. -/
lemma stochasticIntegralBrownian_eLpNorm_two_right_tendsto (s : ℝ) :
    Filter.Tendsto (fun r => MeasureTheory.eLpNorm
        (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global r
          - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global s) 2 P)
      (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
  suffices hsq : Filter.Tendsto (fun r => ∫⁻ ω,
      (‖(stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global r
        - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
          h_sq_int_global s) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      (nhdsWithin s (Set.Ioi s)) (nhds 0) by
    have h2 := hsq.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    refine h2.congr (fun r => ?_)
    rw [← eLpNorm_sq_eq_lintegral_nnnorm_sq _
        ((stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global r).sub
          (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global
            s)).aestronglyMeasurable,
      ← ENNReal.rpow_mul,
      show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  -- the squared increment
  rcases le_or_gt 0 s with hs | hs
  · -- s ≥ 0: orthogonality + isometry + horizon continuity
    have hFsq : ∀ {t : ℝ}, 0 ≤ t →
        ∫ ω, (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2 ∂P
          = (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) t, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal := by
      intro t ht
      have hb := lintegral_nnnorm_sq_eq_ofReal_integral
        (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global t)
      rw [stochasticIntegralBrownian_lintegral_sq W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global ht] at hb
      rw [hb, ENNReal.toReal_ofReal (integral_nonneg (fun ω => sq_nonneg _))]
    have hincr : ∀ {r : ℝ}, s ≤ r →
        ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global r ω
          - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas
            h_sq_int_global s ω‖₊ : ℝ≥0∞) ^ 2 ∂P
          = ENNReal.ofReal
            ((∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal
              - (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal) := by
      intro r hsr
      rw [lintegral_nnnorm_sq_eq_ofReal_integral
        (g := fun ω => stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global r ω
          - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global s ω)
        ((stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global r).sub
          (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global s))]
      congr 1
      rw [integral_sq_increment_eq_of_martingale
        (martingale_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global)
        (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global s)
        (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq_int_global r) hsr,
        hFsq (le_trans hs hsr), hFsq hs]
    -- the toReal-difference → 0
    have hcont : Filter.Tendsto (fun r =>
        ((∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal
          - (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal))
        (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
      have hfin_s : ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ :=
        ne_top_of_le_ne_top (h_sq_int_global (s + 1) (by linarith)).ne
          (MeasureTheory.lintegral_mono (fun ω =>
            lintegral_mono_set (Set.Icc_subset_Icc_right (by linarith))))
      have h0 := (ENNReal.tendsto_toReal hfin_s).comp
        (horizon_lintegral_right_tendsto H h_meas h_sq_int_global hs)
      have h1 := h0.sub_const
        ((∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal)
      rw [sub_self] at h1
      exact h1
    have hof := (ENNReal.continuous_ofReal.tendsto 0).comp hcont
    rw [ENNReal.ofReal_zero] at hof
    refine hof.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hincr (le_of_lt hr)).symm
  · -- s < 0: eventually zero
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hs] with r hr
    symm
    rw [← MeasureTheory.lintegral_zero (μ := P)]
    refine lintegral_congr_ae ?_
    filter_upwards [stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H h_meas h_progMeas
        h_sq_int_global hr.2,
      stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H h_meas h_progMeas h_sq_int_global hs]
      with ω hr0 hs0
    simp [hr0, hs0]

include hℱ in
/-- **Conjunct 1 on `rightCont`: `F` is a martingale wrt `ℱ.rightCont`.**
Right-`L²`-continuity of the slices (`stochasticIntegralBrownian_eLpNorm_two_right_tendsto`)
feeds `martingale_rightCont_of_tendsto_eLpNorm_one`. -/
lemma martingale_rightCont_stochasticIntegralBrownian :
    MeasureTheory.Martingale (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global)
      ℱ.rightCont P := by
  refine LevyStochCalc.Martingale.martingale_rightCont_of_tendsto_eLpNorm_one
    (martingale_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global) (fun s => ?_)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (stochasticIntegralBrownian_eLpNorm_two_right_tendsto W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global s)
    (Filter.Eventually.of_forall (fun r => bot_le))
    (Filter.Eventually.of_forall (fun r => MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
      (by norm_num)))

include h_meas h_sq_int_global in
omit [IsProbabilityMeasure P] in
/-- The `H`-compensator `A_t = ∫₀ᵗ H² ds` is finite in `L²(P ⊗ vol|_{[0,t]})`,
i.e. `(ω, u) ↦ H ω u` is square-integrable over the product. -/
lemma compensatorH_memLp_prod {t : ℝ} (ht : 0 < t) :
    MeasureTheory.MemLp (fun p : Ω × ℝ => H p.1 p.2) 2
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := by
  rw [MeasureTheory.memLp_iff, MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (f := fun p : Ω × ℝ => H p.1 p.2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) h_meas.aestronglyMeasurable,
    show (2 : ℝ≥0∞).toReal = 2 from by simp]
  have hbridge : ∫⁻ p : Ω × ℝ, (‖H p.1 p.2‖ₑ) ^ (2 : ℝ)
        ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) t)))
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    rw [MeasureTheory.lintegral_prod _
      ((((h_meas.nnnorm).coe_nnreal_ennreal).pow_const 2).aemeasurable.congr
        (Filter.Eventually.of_forall (fun p => by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl)))]
    refine lintegral_congr (fun ω => ?_)
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl
  rw [hbridge]; exact h_sq_int_global t ht

include h_meas h_sq_int_global in
/-- The `H`-compensator `A_t = ∫₀ᵗ H² ds` is `P`-integrable (`t ≥ 0`). -/
lemma compensatorH_integrable {t : ℝ} (ht : 0 ≤ t) :
    MeasureTheory.Integrable (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P := by
  rcases lt_or_eq_of_le ht with ht' | ht'
  · exact (compensatorH_memLp_prod H h_meas h_sq_int_global ht').integrable_sq.integral_prod_left
  · have heq : (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) = fun _ => (0 : ℝ) := by
      funext ω; rw [← ht', Set.Icc_self, MeasureTheory.setIntegral_measure_zero _ (by simp)]
    rw [heq]; exact MeasureTheory.integrable_const 0

include h_progMeas in
/-- The `H`-compensator `A_t = ∫₀ᵗ H² ds` is `ℱ_t`-adapted. -/
lemma compensatorH_adapted (t : ℝ) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ t)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) := by
  rcases le_or_gt 0 t with ht | ht
  · have hsq : Probability.ProgressivelyMeasurable ℱ fun ω s => (H ω s) ^ 2 :=
      (continuous_pow 2).comp_progressivelyMeasurable (by simp) h_progMeas
    exact hsq.stronglyMeasurable_setIntegral measurableSet_Icc Set.Icc_subset_Iic_self volume
  · have heq : (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) = fun _ => (0 : ℝ) := by
      funext ω; rw [Set.Icc_eq_empty (not_le.mpr ht)]; simp
    rw [heq]; exact stronglyMeasurable_const

include h_meas h_progMeas h_sq_int_global in
/-- **Compensator `L¹`-convergence.** `∫₀ᵗ (Gₙ.eval)² → ∫₀ᵗ H²` in `L¹(P)`.
The eval-squares converge to `H²` in `L¹(P ⊗ vol|_{[0,t]})`
(`tendsto_eLpNorm_one_sq_sub` from `L²`-convergence of the evals), and the
`L¹(P)`-norm of the `u`-marginal is dominated by the joint `L¹`-norm. -/
lemma masterApprox_compensator_tendsto_L1 {t : ℝ} (ht : 0 ≤ t) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm
      (fun ω => (∫ u in Set.Icc (0 : ℝ) t,
          ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P)
      Filter.atTop (nhds 0) := by
  rcases lt_or_eq_of_le ht with ht' | ht'
  · set ν : MeasureTheory.Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) t) with hν
    set Hp : Ω × ℝ → ℝ := fun p => H p.1 p.2 with hHp
    set Gp : ℕ → Ω × ℝ → ℝ := fun n p =>
      (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval p.2 p.1 with hGp
    have hHp_meas : Measurable Hp := h_meas
    have hGp_meas : ∀ n, Measurable (Gp n) := fun n =>
      (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval_jointly_measurable
    have hHmem := compensatorH_memLp_prod H h_meas h_sq_int_global ht'
    -- `Gp n → Hp` in `L²(P ⊗ ν)`.
    have hbridge : ∀ (f : Ω × ℝ → ℝ), Measurable f →
        MeasureTheory.eLpNorm f 2 (P.prod ν) ^ (2 : ℝ)
          = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
      intro f hf
      rw [eLpNorm_sq_eq_lintegral_nnnorm_sq f hf.aestronglyMeasurable,
          MeasureTheory.lintegral_prod _
            (((hf.nnnorm.coe_nnreal_ennreal).pow_const 2).aemeasurable)]
    have hfin2 : ∀ (f : Ω × ℝ → ℝ), Measurable f →
        (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) →
        MeasureTheory.eLpNorm f 2 (P.prod ν) < ⊤ :=
      fun f hf hfv => lt_top_iff_ne_top.mpr (fun h => hfv (by
        rw [← hbridge f hf, h, ENNReal.top_rpow_of_pos (by norm_num)]))
    have hL2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν))
        Filter.atTop (nhds 0) := by
      have hsq : ∀ n, MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν) ^ (2 : ℝ)
          = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖H ω s - (masterApprox ℱ H h_meas h_progMeas
                h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
                ∂volume ∂P := by
        intro n
        rw [hbridge (Gp n - Hp) ((hGp_meas n).sub hHp_meas)]
        refine lintegral_congr (fun ω =>
          MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_))
        simp only [Pi.sub_apply, hGp, hHp]
        rw [show (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω - H ω s
              = -(H ω s - (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval s ω)
            from by ring, nnnorm_neg]
      have h2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν) ^ (2 : ℝ))
          Filter.atTop (nhds 0) := by
        simp_rw [hsq]
        exact masterApprox_eval_tendsto (t := t) ℱ H h_meas h_progMeas h_sq_int_global
      have h3 := h2.ennrpow_const ((1 : ℝ) / 2)
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
      refine h3.congr (fun n => ?_)
      rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
    -- squares converge in `L¹(P ⊗ ν)`.
    have hjoint : Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm (fun p => (Gp n p) ^ 2 - (Hp p) ^ 2) 1 (P.prod ν))
        Filter.atTop (nhds 0) :=
      tendsto_eLpNorm_one_sq_sub (fun n => (hGp_meas n).aemeasurable) hHp_meas.aemeasurable
        hHmem.eLpNorm_lt_top.ne hL2
    -- marginal `L¹(P)` ≤ joint `L¹(P ⊗ ν)`.
    have hmarg : ∀ n, MeasureTheory.eLpNorm
        (fun ω => (∫ u in Set.Icc (0 : ℝ) t,
            ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P
        ≤ MeasureTheory.eLpNorm (fun p => (Gp n p) ^ 2 - (Hp p) ^ 2) 1 (P.prod ν) := by
      intro n
      set dsq : Ω × ℝ → ℝ := fun p => (Gp n p) ^ 2 - (Hp p) ^ 2 with hdsq
      have hGsq_int : MeasureTheory.Integrable (fun p => (Gp n p) ^ 2) (P.prod ν) :=
        MeasureTheory.MemLp.integrable_sq
          (show MeasureTheory.MemLp (Gp n) 2 (P.prod ν) from
            MeasureTheory.memLp_iff.mpr (hfin2 (Gp n) (hGp_meas n)
              (eval_lintegral_sq_finite
                (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t).ne))
      have hHsq_int : MeasureTheory.Integrable (fun p => (Hp p) ^ 2) (P.prod ν) :=
        hHmem.integrable_sq
      have hdsq_int : MeasureTheory.Integrable dsq (P.prod ν) := hGsq_int.sub hHsq_int
      have hmarg_aesm : MeasureTheory.AEStronglyMeasurable
          (fun ω => (∫ u in Set.Icc (0 : ℝ) t,
            ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P :=
        (hGsq_int.integral_prod_left.sub hHsq_int.integral_prod_left).aestronglyMeasurable
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm hmarg_aesm,
        MeasureTheory.eLpNorm_one_eq_lintegral_enorm hdsq_int.aestronglyMeasurable,
        MeasureTheory.lintegral_prod _ hdsq_int.aestronglyMeasurable.enorm]
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [hGsq_int.prod_right_ae, hHsq_int.prod_right_ae] with ω hGω hHω
      have hcomb : (∫ u in Set.Icc (0 : ℝ) t,
            ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume
          = ∫ u, dsq (ω, u) ∂ν := by
        rw [hdsq]; exact (MeasureTheory.integral_sub hGω hHω).symm
      rw [hcomb]
      exact MeasureTheory.enorm_integral_le_lintegral_enorm _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hjoint
      (Filter.Eventually.of_forall (fun n => bot_le)) (Filter.Eventually.of_forall hmarg)
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    symm
    rw [← ht']
    have hz : (fun ω => (∫ u in Set.Icc (0 : ℝ) (0 : ℝ),
        ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) (0 : ℝ), (H ω u) ^ 2 ∂volume) = (0 : Ω → ℝ) := by
      funext ω
      rw [Set.Icc_self, MeasureTheory.setIntegral_measure_zero _ (by simp),
        MeasureTheory.setIntegral_measure_zero _ (by simp), sub_zero]; rfl
    rw [hz, MeasureTheory.eLpNorm_zero]

include h_meas h_progMeas h_sq_int_global hℱ in
/-- **Conjunct 2: the compensated square is a martingale.**
`t ↦ (F t)² − ∫₀ᵗ H² ds` is an `ℱ`-martingale. The simple-level
compensated squares `martingale_simpleIntegral_sq_sub_compensator` (for `masterApprox n`)
are martingales converging in `L¹` to the `F`-process: the integrand-squares converge
(`masterApprox_tendsto_L2` + `tendsto_eLpNorm_one_sq_sub`) and the compensators
converge (`masterApprox_compensator_tendsto_L1`). -/
lemma martingale_quadVar_stochasticIntegralBrownian :
    MeasureTheory.Martingale
      (fun t ω => (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume)
      ℱ P := by
  set F := stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global with hF
  have hAHint : ∀ t, MeasureTheory.Integrable
      (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact compensatorH_integrable H h_meas h_sq_int_global ht
    · have heq : (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) = fun _ => (0 : ℝ) := by
        funext ω; rw [Set.Icc_eq_empty (not_le.mpr ht)]; simp
      rw [heq]; exact MeasureTheory.integrable_const 0
  refine martingale_of_tendsto_eLpNorm_one
    (M := fun n t ω =>
      (simpleIntegral W (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n) t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t,
            ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
    (fun n => martingale_simpleIntegral_sq_sub_compensator W ℱ hℱ (master_horizon_pos n)
      (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n))
    (fun n t => (martingale_simpleIntegral_sq_sub_compensator W ℱ hℱ (master_horizon_pos n)
      (masterApprox ℱ H h_meas h_progMeas h_sq_int_global n)
      (masterApprox_adapt ℱ H h_meas h_progMeas h_sq_int_global n)).integrable t)
    (fun t => ?_) (fun t => ?_) (fun t => ?_)
  · -- StronglyAdapted
    have hFsq : @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ t) (fun ω => (F t ω) ^ 2) := by
      simpa [pow_two, Pi.mul_def] using
        (stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H h_meas h_progMeas
          h_sq_int_global t).mul
          (stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H h_meas h_progMeas h_sq_int_global t)
    exact hFsq.sub (compensatorH_adapted ℱ H h_progMeas t)
  · -- integrability of the F-process at each `t`
    exact ((stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global t).integrable_sq).sub
      (hAHint t)
  · -- `L¹`-convergence of the simple compensated squares to the F-process
    rcases le_or_gt 0 t with ht | ht
    · have hX : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
          (fun ω => (simpleIntegral W (masterApprox ℱ H h_meas h_progMeas
            h_sq_int_global n) t ω) ^ 2
            - (F t ω) ^ 2) 1 P) Filter.atTop (nhds 0) :=
        tendsto_eLpNorm_one_sq_sub
          (fun n => (Finset.measurable_sum _ (fun i _ =>
            ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).mul
              ((W.measurable_eval _).sub (W.measurable_eval _)))).aemeasurable)
          (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
            h_sq_int_global t).aestronglyMeasurable.aemeasurable
          (stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas
            h_sq_int_global t).eLpNorm_lt_top.ne
          (masterApprox_tendsto_L2 W ℱ hℱ H h_meas h_progMeas h_sq_int_global ht)
      have hY := masterApprox_compensator_tendsto_L1 ℱ H h_meas h_progMeas h_sq_int_global ht
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa using hX.add hY)
        (Filter.Eventually.of_forall (fun n => bot_le))
        (Filter.Eventually.of_forall (fun n => ?_))
      calc MeasureTheory.eLpNorm
            ((fun t' ω => (simpleIntegral W (masterApprox ℱ H h_meas h_progMeas
              h_sq_int_global n) t' ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t', ((masterApprox ℱ H h_meas h_progMeas
                  h_sq_int_global n).eval u ω) ^ 2 ∂volume) t
              - fun ω => (F t ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P
          = MeasureTheory.eLpNorm
              ((fun ω => (simpleIntegral W (masterApprox ℱ H h_meas h_progMeas
                h_sq_int_global n) t ω) ^ 2
                  - (F t ω) ^ 2)
                - fun ω => (∫ u in Set.Icc (0 : ℝ) t,
                    ((masterApprox ℱ H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
                  - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P := by
            refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
            simp only [Pi.sub_apply]; ring
        _ ≤ _ := MeasureTheory.eLpNorm_sub_le le_rfl
    · have hzero : ∀ n, MeasureTheory.eLpNorm
          ((fun t' ω => (simpleIntegral W (masterApprox ℱ H h_meas h_progMeas
            h_sq_int_global n) t' ω) ^ 2
              - ∫ u in Set.Icc (0 : ℝ) t', ((masterApprox ℱ H h_meas h_progMeas
                h_sq_int_global n).eval u ω) ^ 2 ∂volume) t
            - fun ω => (F t ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P = 0 := by
        intro n
        refine (MeasureTheory.eLpNorm_eq_zero_of_ae_zero ?_)
        filter_upwards [stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H h_meas h_progMeas
          h_sq_int_global ht] with ω hF0
        simp only [Pi.sub_apply, Pi.zero_apply,
          simpleIntegral_eq_zero_of_nonpos W _ (le_of_lt ht) ω, hF, hF0,
          Set.Icc_eq_empty (not_le.mpr ht)]
        simp
      simp only [hzero]; exact tendsto_const_nhds

end MasterSequence

end LevyStochCalc.Brownian.Ito
