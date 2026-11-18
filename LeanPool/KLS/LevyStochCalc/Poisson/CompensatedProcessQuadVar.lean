/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system (module
-- header, public imports, exposed public section) for Lean/Mathlib v4.35.0; proofs use the v4.35.0
-- `eLpNorm`/`MemLp` API.
-- Modified 2026-10-31 by the KLS formalization project: pass the existing
-- `AEStronglyMeasurable` witnesses now taken by `eLpNorm_sq_eq_lintegral_nnnorm_sq`
-- (Mathlib v4.35.0 `eLpNorm` change); proof-only change.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedQuadVar

/-!
# The quadratic-variation martingale of the compensated integral process

The compensated square `t ↦ F_t² − ∫_0^t ∫_E φ(u, e)² ν(de) du` of the `L²` integral process
`F` is a martingale on the natural filtration and on its right-continuous augmentation. The
stage compensated squares are martingales (`MarkStep.martingale_sq_sub_compensator`) and
converge in `L¹` to the compensated square of the process: the stage integrands converge to
`φ` in `L²` of the product measure on `Ω × [0, t] × E`, so their squares converge in `L¹`, and
the `L¹(P)`-distance of the compensators is dominated by the joint `L¹`-distance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Compensator

variable (ν : Measure E) (φ : Ω → ℝ → E → ℝ)

/-- The compensator `∫_0^t ∫_E φ(u, e)² ν(de) du` of the integrand. -/
noncomputable def compensator (t : ℝ) (ω : Ω) : ℝ :=
  ∫ u in Set.Icc (0 : ℝ) t, ∫ e, (φ ω u e) ^ 2 ∂ν ∂volume

omit [MeasurableSpace Ω] in
/-- The compensator vanishes at nonpositive times. -/
lemma compensator_of_nonpos {t : ℝ} (ht : t ≤ 0) : compensator ν φ t = fun _ => 0 := by
  funext ω
  unfold compensator
  rw [Measure.restrict_eq_zero.2 (by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_of_nonpos (by linarith)), integral_zero_measure]

/-- The product measure of `P`, Lebesgue measure on `[0, t]` and `ν` on `Ω × ℝ × E`. -/
noncomputable abbrev horizonMeasure (P : Measure Ω) (t : ℝ) : Measure (Ω × ℝ × E) :=
  P.prod ((volume.restrict (Set.Icc (0 : ℝ) t)).prod ν)

lemma coe_nnnorm_sq_eq_ofReal_sq (x : ℝ) : (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm _).symm,
    ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

end Compensator

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

omit [IsProbabilityMeasure P] in
/-- The nested triple integral over `Ω`, `[0, t]` and `E` as an integral for the horizon
measure. -/
lemma lintegral_horizonMeasure (t : ℝ) (f : Ω → ℝ → E → ℝ≥0∞)
    (hf : Measurable (fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2)) :
    ∫⁻ p, f p.1 p.2.1 p.2.2 ∂(horizonMeasure ν P t)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e, f ω s e ∂ν ∂volume ∂P := by
  rw [horizonMeasure, lintegral_prod _ hf.aemeasurable]
  refine lintegral_congr fun ω => ?_
  rw [lintegral_prod (fun y : ℝ × E => f (ω, y).1 (ω, y).2.1 (ω, y).2.2)
    (hf.comp (measurable_prodMk_left (x := ω))).aemeasurable]

include h_progMeas in
/-- The compensator is adapted to the natural filtration. -/
lemma compensator_stronglyAdapted :
    StronglyAdapted ℱ (compensator ν φ) := by
  intro t
  rcases le_or_gt 0 t with ht | ht
  · exact ((continuous_pow 2).comp_markedProgressivelyMeasurable (by simp)
      h_progMeas).stronglyMeasurable_setIntegral_integral measurableSet_Icc
      Set.Icc_subset_Iic_self volume ν
  · rw [compensator_of_nonpos ν φ ht.le]
    exact stronglyMeasurable_const

omit [IsProbabilityMeasure P] in
include h_meas h_sq_int_global in
/-- The integrand is square-integrable for the horizon measure. -/
lemma memLp_phi_horizon {t : ℝ} (ht : 0 < t) :
    MemLp (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (horizonMeasure ν P t) := by
  refine (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 2)).1 ?_
  rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq _ h_meas.aestronglyMeasurable,
    lintegral_horizonMeasure t (fun ω s e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2)
      ((ENNReal.continuous_coe.measurable.comp h_meas.nnnorm).pow_const 2)]
  exact h_sq_int_global t ht

include h_meas h_sq_int_global in
/-- The compensator is integrable at every time. -/
lemma integrable_compensator (t : ℝ) : Integrable (compensator ν φ t) P := by
  rcases le_or_gt t 0 with ht | ht
  · rw [compensator_of_nonpos ν φ ht]
    exact integrable_const 0
  · have hint := (memLp_phi_horizon φ h_meas h_sq_int_global ht).integrable_sq
    refine hint.integral_prod_left.congr ?_
    filter_upwards [hint.prod_right_ae] with ω hω
    exact integral_prod _ hω

/-- The integrand of the stage-`n` approximant as a function on `Ω × ℝ × E`. -/
noncomputable def stageEval (n : ℕ) (p : Ω × ℝ × E) : ℝ :=
  (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.eval p.2.1 p.2.2 p.1

lemma measurable_stageEval (n : ℕ) :
    Measurable (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n) :=
  (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.eval_measurable

/-- The stage integrands converge to `φ` in `L²` of the horizon measure at every time. -/
lemma stageEval_tendsto (t : ℝ) :
    Tendsto (fun n => eLpNorm (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n
      - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (horizonMeasure ν P t)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => eLpNorm (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n
      - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (horizonMeasure ν P t) ^ (2 : ℝ))
      atTop (𝓝 0) := by
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, t ≤ stageHorizon N₀ := by
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt t (one_lt_two : (1 : ℝ) < 2)
      exact ⟨k, hk.le⟩
    have hbound : ∀ n, N₀ ≤ n → eLpNorm (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n
        - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (horizonMeasure ν P t) ^ (2 : ℝ)
        ≤ stageErr φ P n (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 := by
      intro n hn
      set G := (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 with hG
      have hdm : Measurable (fun p : Ω × ℝ × E =>
          (‖φ p.1 p.2.1 p.2.2 - G.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
        (ENNReal.continuous_coe.measurable.comp (h_meas.sub G.eval_measurable).nnnorm).pow_const 2
      calc eLpNorm (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n
            - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (horizonMeasure ν P t) ^ (2 : ℝ)
          = ∫⁻ p, (‖(stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n
              - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) p‖₊ : ℝ≥0∞) ^ 2
              ∂(horizonMeasure ν P t) :=
            LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq _
              ((measurable_stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n).sub
                h_meas).aestronglyMeasurable
        _ = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
              (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
            rw [← lintegral_horizonMeasure t
              (fun ω s e => (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hdm]
            refine lintegral_congr fun q => ?_
            rw [Pi.sub_apply, ← nnnorm_neg, neg_sub]
            rfl
        _ ≤ stageErr φ P n G := lintegral_mono fun ω =>
            lintegral_mono_set (Set.Icc_subset_Icc_right (hN₀.trans (stageHorizon_mono hn)))
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp [Function.comp]
    have herr : Tendsto (fun n => stageErr φ P n
        (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv (fun _ => bot_le)
        (fun n => (master_err N ℱ φ h_meas h_progMeas h_sq_int_global n).le)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herr
      (Eventually.of_forall fun _ => bot_le) (eventually_atTop.2 ⟨N₀, hbound⟩)
  have h := hsq.ennrpow_const ((1 : ℝ) / 2)
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  refine h.congr (fun n => ?_)
  rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]

include hℱ in
/-- The stage integrands are square-integrable for the horizon measure. -/
lemma memLp_stageEval (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n) 2 (horizonMeasure ν P t) := by
  refine (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 2)).1 ?_
  rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq _
    (measurable_stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n).aestronglyMeasurable]
  unfold stageEval
  set G := (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2 with hG
  have hm : Measurable (fun p : Ω × ℝ × E => (‖G.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp G.eval_measurable.nnnorm).pow_const 2
  rw [lintegral_horizonMeasure t (fun ω s e => (‖G.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hm]
  have h1 := G.lintegral_integral_sq_at N hℱ (master_adapted N ℱ φ h_meas h_progMeas
    h_sq_int_global n)
    ht
  have h2 : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e, (‖G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      = ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P :=
    lintegral_congr fun ω =>
      (lintegral_swap_es (fun ω s e => (‖G.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hm ω).symm
  rw [h2, ← h1, ← LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq]
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (G.memLp_integral N t).eLpNorm_ne_top
  · exact (G.memLp_integral N t).aestronglyMeasurable

include hℱ in
/-- The stage compensators converge in `L¹` to the compensator of the integrand. -/
lemma stage_compensator_tendsto_L1 (t : ℝ) :
    Tendsto (fun n => eLpNorm (fun ω =>
      (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.compensator t ω
        - compensator ν φ t ω) 1 P) atTop (𝓝 0) := by
  rcases le_or_gt t 0 with ht | ht
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    symm
    rw [show (fun ω => (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.compensator t ω
        - compensator ν φ t ω) = (0 : Ω → ℝ) from by
      funext ω
      rw [MarkStep.compensator_of_nonpos _ ht, compensator_of_nonpos ν φ ht]
      simp]
    exact eLpNorm_zero
  · have hgmem := memLp_phi_horizon φ h_meas h_sq_int_global ht
    have hjoint : Tendsto (fun n => eLpNorm (fun p : Ω × ℝ × E =>
        (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n p) ^ 2 - (φ p.1 p.2.1 p.2.2) ^ 2) 1
        (horizonMeasure ν P t)) atTop (𝓝 0) :=
      LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_sq_sub
        (fun n => (measurable_stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n).aemeasurable)
        h_meas.aemeasurable hgmem.eLpNorm_ne_top (stageEval_tendsto N ℱ φ h_meas h_progMeas
          h_sq_int_global t)
    have hmarg : ∀ n, eLpNorm (fun ω =>
        (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.compensator t ω
          - compensator ν φ t ω) 1 P
        ≤ eLpNorm (fun p : Ω × ℝ × E =>
          (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n p) ^ 2 - (φ p.1 p.2.1 p.2.2) ^
            2) 1
          (horizonMeasure ν P t) := by
      intro n
      have hGsq : Integrable (fun p : Ω × ℝ × E =>
          (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n p) ^ 2) (horizonMeasure ν P t) :=
        (memLp_stageEval N ℱ hℱ φ h_meas h_progMeas h_sq_int_global n ht.le).integrable_sq
      have hgsq : Integrable (fun p : Ω × ℝ × E => (φ p.1 p.2.1 p.2.2) ^ 2)
          (horizonMeasure ν P t) := hgmem.integrable_sq
      have hd : Integrable (fun p : Ω × ℝ × E =>
          (stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n p) ^ 2 - (φ p.1 p.2.1 p.2.2) ^ 2)
          (horizonMeasure ν P t) := hGsq.sub hgsq
      rw [eLpNorm_one_eq_lintegral_enorm
          (f := fun ω => (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.compensator t ω
            - compensator ν φ t ω)
          (((master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.integrable_compensator
            t).aestronglyMeasurable.sub
            (integrable_compensator φ h_meas h_sq_int_global t).aestronglyMeasurable),
        eLpNorm_one_eq_lintegral_enorm hd.aestronglyMeasurable,
        lintegral_prod _ hd.aestronglyMeasurable.enorm]
      refine lintegral_mono_ae ?_
      filter_upwards [hGsq.prod_right_ae, hgsq.prod_right_ae] with ω hGω hgω
      have hcomb : (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.compensator t ω
          - compensator ν φ t ω
          = ∫ y, ((stageEval N ℱ φ h_meas h_progMeas h_sq_int_global n (ω, y)) ^ 2
              - (φ ω y.1 y.2) ^ 2) ∂((volume.restrict (Set.Icc (0 : ℝ) t)).prod ν) := by
        rw [integral_sub hGω hgω, integral_prod _ hGω, integral_prod _ hgω]
        rfl
      rw [hcomb]
      exact enorm_integral_le_lintegral_enorm _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hjoint
      (Eventually.of_forall fun n => bot_le) (Eventually.of_forall hmarg)

include hℱ in
/-- The compensated square of the process is a martingale on the natural filtration. -/
theorem martingale_quadVar_process :
    Martingale (fun t ω => (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2
      - compensator ν φ t ω) ℱ P := by
  refine LevyStochCalc.Brownian.Ito.martingale_of_tendsto_eLpNorm_one
    (M := fun n t ω => (stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω) ^ 2
      - (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.compensator t ω)
    (fun n => (master N ℱ φ h_meas h_progMeas h_sq_int_global
      n).2.martingale_sq_sub_compensator N hℱ
      (master_adapted N ℱ φ h_meas h_progMeas h_sq_int_global n))
    (fun n t => ((master N ℱ φ h_meas h_progMeas h_sq_int_global
      n).2.martingale_sq_sub_compensator N hℱ (master_adapted N ℱ φ h_meas h_progMeas
        h_sq_int_global n)).integrable t)
    (fun t => ((process_stronglyAdapted N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).pow 2).sub
      (compensator_stronglyAdapted ℱ φ h_progMeas t))
    (fun t => (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).integrable_sq.sub
      (integrable_compensator φ h_meas h_sq_int_global t))
    (fun t => ?_)
  have hX : Tendsto (fun n => eLpNorm (fun ω =>
      (stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω) ^ 2
        - (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2) 1 P) atTop (𝓝 0) :=
    LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_sq_sub
      (fun n => (memLp_stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n
        t).aestronglyMeasurable.aemeasurable)
      (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).aestronglyMeasurable.aemeasurable
      (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).eLpNorm_ne_top
      (stageIntegral_tendsto_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t)
  have hY := stage_compensator_tendsto_L1 N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hX.add hY)
    (Eventually.of_forall fun n => bot_le) (Eventually.of_forall fun n => ?_)
  calc eLpNorm ((fun ω => (stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω) ^ 2
          - (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.compensator t ω)
        - fun ω => (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2
          - compensator ν φ t ω) 1 P
      = eLpNorm ((fun ω => (stageIntegral N ℱ φ h_meas h_progMeas h_sq_int_global n t ω) ^ 2
            - (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2)
          - fun ω => (master N ℱ φ h_meas h_progMeas h_sq_int_global n).2.compensator t ω
            - compensator ν φ t ω) 1 P := by
        refine eLpNorm_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [Pi.sub_apply]
        ring
    _ ≤ _ := eLpNorm_sub_le le_rfl

include h_meas h_sq_int_global in
/-- Right-`L¹`-continuity of the compensator. -/
lemma compensator_right_tendsto_L1 (s : ℝ) :
    Tendsto (fun r => eLpNorm (fun ω => compensator ν φ r ω - compensator ν φ s ω) 1 P)
      (𝓝[>] s) (𝓝 0) := by
  rcases le_or_gt 0 s with hs | hs
  · have hslab := LevyStochCalc.Brownian.Ito.tendsto_setLIntegral_Ioc_prod_zero (P := P)
      (markSq (ν := ν) φ) (measurable_markSq φ h_meas) hs (lt_add_one s)
      (horizonInt_lt_top φ h_sq_int_global (s + 1)).ne
    refine hslab.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hsr : s ≤ r := hr.le
    have hint := (memLp_phi_horizon φ h_meas h_sq_int_global (hs.trans_lt hr)).integrable_sq
    rw [eLpNorm_one_eq_lintegral_enorm
      (f := fun ω => compensator ν φ r ω - compensator ν φ s ω)
      ((integrable_compensator φ h_meas h_sq_int_global r).aestronglyMeasurable.sub
        (integrable_compensator φ h_meas h_sq_int_global s).aestronglyMeasurable)]
    refine (lintegral_congr_ae ?_).symm
    filter_upwards [hint.prod_right_ae] with ω hω
    have hu : Integrable (fun u => ∫ e, (φ ω u e) ^ 2 ∂ν) (volume.restrict (Set.Icc (0 : ℝ) r)) :=
      hω.integral_prod_left
    have hus : IntegrableOn (fun u => ∫ e, (φ ω u e) ^ 2 ∂ν) (Set.Icc (0 : ℝ) s) volume :=
      hu.mono_measure (Measure.restrict_mono (Set.Icc_subset_Icc_right hsr) le_rfl)
    have hsub : Set.Ioc s r ⊆ Set.Icc (0 : ℝ) r :=
      Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_left hs)
    have huc : IntegrableOn (fun u => ∫ e, (φ ω u e) ^ 2 ∂ν) (Set.Ioc s r) volume :=
      hu.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hsplit : compensator ν φ r ω - compensator ν φ s ω
        = ∫ u in Set.Ioc s r, ∫ e, (φ ω u e) ^ 2 ∂ν ∂volume := by
      unfold compensator
      rw [← Set.Icc_union_Ioc_eq_Icc hs hsr, setIntegral_union
        (Set.disjoint_left.2 fun x hx hx' => not_le.2 hx'.1 hx.2) measurableSet_Ioc hus huc]
      ring
    have hnn : ∀ u, 0 ≤ ∫ e, (φ ω u e) ^ 2 ∂ν := fun u => integral_nonneg fun _ => sq_nonneg _
    rw [hsplit, Real.enorm_eq_ofReal (integral_nonneg fun u => hnn u),
      ofReal_integral_eq_lintegral_ofReal huc (Eventually.of_forall hnn)]
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ u ∂(volume.restrict (Set.Ioc s r)), Integrable (fun e => (φ ω u e) ^ 2) ν :=
      ae_restrict_of_ae_restrict_of_subset hsub hω.prod_right_ae
    filter_upwards [hae] with u hu'
    rw [ofReal_integral_eq_lintegral_ofReal hu' (Eventually.of_forall fun e => sq_nonneg _),
      markSq]
    exact lintegral_congr fun e => (coe_nnnorm_sq_eq_ofReal_sq _).symm
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hs] with r hr
    symm
    rw [show (fun ω => compensator ν φ r ω - compensator ν φ s ω) = (0 : Ω → ℝ) from by
      funext ω
      rw [compensator_of_nonpos ν φ hr.2.le, compensator_of_nonpos ν φ hs.le]
      simp]
    exact eLpNorm_zero

include hℱ in
/-- The compensated square of the process is a martingale on the right-continuous natural
filtration. -/
theorem martingale_rightCont_quadVar_process :
    Martingale (fun t ω => (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2
      - compensator ν φ t ω) ℱ.rightCont P := by
  refine LevyStochCalc.Martingale.martingale_rightCont_of_tendsto_eLpNorm_one
    (martingale_quadVar_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global) fun s => ?_
  have hF2 : Tendsto (fun r => eLpNorm (fun ω =>
      (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r ω) ^ 2
        - (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s ω) ^ 2) 1 P) (𝓝[>] s) (𝓝 0) :=
    LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_sq_sub (l := 𝓝[>] s)
      (a := fun r => process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r)
      (b := process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s)
      (fun r => (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global
        r).aestronglyMeasurable.aemeasurable)
      (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s).aestronglyMeasurable.aemeasurable
      (process_memLp N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s).eLpNorm_ne_top
      (process_eLpNorm_two_right_tendsto N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s)
  have hA := compensator_right_tendsto_L1 φ h_meas h_sq_int_global s
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hF2.add hA)
    (Eventually.of_forall fun r => bot_le) (Eventually.of_forall fun r => ?_)
  calc eLpNorm ((fun ω => (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r ω) ^ 2
          - compensator ν φ r ω)
        - fun ω => (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s ω) ^ 2
          - compensator ν φ s ω) 1 P
      = eLpNorm ((fun ω => (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global r ω) ^ 2
            - (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s ω) ^ 2)
          - fun ω => compensator ν φ r ω - compensator ν φ s ω) 1 P := by
        refine eLpNorm_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [Pi.sub_apply]
        ring
    _ ≤ _ := eLpNorm_sub_le le_rfl

end LevyStochCalc.Poisson.Compensated
