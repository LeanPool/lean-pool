/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
module

public import LeanPool.Vlasov.OT.Continuation
import all LeanPool.Vlasov.OT.Continuation
import all LeanPool.Vlasov.OT.LocalWellPosedness
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Well-posedness ladder for the Vlasov equation + Dobrushin stability

This file builds on the characteristic-flow infrastructure of
`LeanPool/Vlasov/OT/CharacteristicFlow.lean` and carries the theorem ladder of the
development:

* §9 local existence and uniqueness (`vlasovWellPosedness_local` and its
  Picard / final-assembly sub-helpers);
* the fixed-`T_0` continuation tower — the one-window glue step
  `vlasovWellPosedness_glue` (with its `vlasovGlue_*` helper family),
  `exists_localSmallness_window`, and the forward iteration to arbitrary
  `T_target`;
* per-window uniqueness over `IsLagrangianVlasovSolutionOn` and the
  universal-in-`t` bridge to `IsLagrangianVlasovSolution`;
* the §10 marquee results: `vlasovWellPosedness` (forward-in-time existence),
  `vlasovWellPosedness_uniqueness`, `dobrushin` (W₁ stability, proved by
  coupling the two flows and a Grönwall estimate), and the mean-field limit;
* the wiring layer `dobrushin_on` / `dobrushin_forward` /
  `vlasovWellPosedness_stability`: the window and forward-global stability
  forms with the explicit uniform constant `C = 2 · max 1 L`, whose
  hypotheses are exactly the clauses `vlasovWellPosedness` emits.

See `formalize/DESIGN.md` (in the source repository) for the overall design.
-/

@[expose] public section

namespace Vlasov

open MeasureTheory ENNReal

-- Preserve existing private names when moving their proofs.
private alias envelopeStep_contractionInputs :=
  _root_.Vlasov.envelopeStep_contractionInputs

private alias picardCharFlow_aemeasurable :=
  _root_.Vlasov.picardCharFlow_aemeasurable

private alias picardFlow_clamp_bundle :=
  _root_.Vlasov.picardFlow_clamp_bundle

private alias picardLimit_fixed_point_eq :=
  _root_.Vlasov.picardLimit_fixed_point_eq

private alias picardLimit_flow_pointwise_contraction :=
  _root_.Vlasov.picardLimit_flow_pointwise_contraction

private alias picardLimit_self_consistency :=
  _root_.Vlasov.picardLimit_self_consistency

private alias vlasovWellPosedness_local_picard_sequence :=
  _root_.Vlasov.vlasovWellPosedness_local_picard_sequence

private alias dobrushinFlow_marginal_gradW_integrable :=
  _root_.Vlasov.dobrushinFlow_marginal_gradW_integrable

private alias exists_localSmallness_window._simp_1_1 :=
  _root_.Vlasov.exists_localSmallness_window._simp_1_1

private alias exists_localSmallness_window._simp_1_2 :=
  _root_.Vlasov.exists_localSmallness_window._simp_1_2

private alias exists_localSmallness_window._simp_1_3 :=
  _root_.Vlasov.exists_localSmallness_window._simp_1_3

private alias exists_localSmallness_window._simp_1_4 :=
  _root_.Vlasov.exists_localSmallness_window._simp_1_4

private alias exists_localSmallness_window._simp_1_5 :=
  _root_.Vlasov.exists_localSmallness_window._simp_1_5

private alias exists_localSmallness_window._simp_1_6 :=
  _root_.Vlasov.exists_localSmallness_window._simp_1_6

private alias exists_localSmallness_window._simp_1_7 :=
  _root_.Vlasov.exists_localSmallness_window._simp_1_7

private alias vlasovGlue_composed_integral_eq :=
  _root_.Vlasov.vlasovGlue_composed_integral_eq

private alias vlasovGlue_composed_pushforward :=
  _root_.Vlasov.vlasovGlue_composed_pushforward

private alias vlasovGlue_conv_force_bound :=
  _root_.Vlasov.vlasovGlue_conv_force_bound

private alias vlasovGlue_diff_ne :=
  _root_.Vlasov.vlasovGlue_diff_ne

private alias vlasovGlue_flowV_hasDerivAt :=
  _root_.Vlasov.vlasovGlue_flowV_hasDerivAt

private alias vlasovGlue_flowX_hasDerivAt :=
  _root_.Vlasov.vlasovGlue_flowX_hasDerivAt

private alias vlasovGlue_flow_aemeasurable :=
  _root_.Vlasov.vlasovGlue_flow_aemeasurable

private alias vlasovGlue_flow_growthBound :=
  _root_.Vlasov.vlasovGlue_flow_growthBound

private alias vlasovGlue_flow_growthBound._simp_1_1 :=
  _root_.Vlasov.vlasovGlue_flow_growthBound._simp_1_1

private alias vlasovGlue_gradVφ_continuous :=
  _root_.Vlasov.vlasovGlue_gradVφ_continuous

private alias vlasovGlue_gradXφ_continuous :=
  _root_.Vlasov.vlasovGlue_gradXφ_continuous

private alias vlasovGlue_gradφ_bound :=
  _root_.Vlasov.vlasovGlue_gradφ_bound

private alias vlasovGlue_intCont_left :=
  _root_.Vlasov.vlasovGlue_intCont_left

private alias vlasovGlue_intCont_right :=
  _root_.Vlasov.vlasovGlue_intCont_right

private alias vlasovGlue_marginal_norm_integrable :=
  _root_.Vlasov.vlasovGlue_marginal_norm_integrable

private alias vlasovGlue_moment :=
  _root_.Vlasov.vlasovGlue_moment

private alias vlasovGlue_moment_flat :=
  _root_.Vlasov.vlasovGlue_moment_flat

private alias vlasovGlue_pushforward_eq :=
  _root_.Vlasov.vlasovGlue_pushforward_eq

private alias vlasovGlue_seam_contLeft :=
  _root_.Vlasov.vlasovGlue_seam_contLeft

private alias vlasovGlue_seam_contRight :=
  _root_.Vlasov.vlasovGlue_seam_contRight

private alias vlasovGlue_seam_forceIntegral_cont :=
  _root_.Vlasov.vlasovGlue_seam_forceIntegral_cont

private alias vlasovGlue_shifted_flow_contWithin :=
  _root_.Vlasov.vlasovGlue_shifted_flow_contWithin

private alias vlasovWellPosedness_glue_boundary :=
  _root_.Vlasov.vlasovWellPosedness_glue_boundary

private alias vlasovWellPosedness_glue_boundary_seam :=
  _root_.Vlasov.vlasovWellPosedness_glue_boundary_seam

/-! ## Uniqueness over `IsLagrangianVlasovSolutionOn` per window -/
-- Two Lagrangian solutions on `[0, T_target]` with the same initial measure
-- agree on `[0, T_target]`.  The argument: contraction in `Phi_supW1_contraction`
-- + Banach fixed-point uniqueness on the iterated windows.  Within the
-- `IsLagrangianVlasovSolutionOn` class, the flow witness is bundled, so
-- pushforward + flow uniqueness chains directly.  (The broader uniqueness
-- over `IsVlasovSolution` — weak-PDE-only solutions without an explicit
-- flow — requires the Eulerian-to-Lagrangian / DiPerna-Lions superposition
-- principle, which is out of scope.)
--
-- The uniqueness proof bounds the *integrated trajectory distance*
-- `∫ ‖Φ_f − Φ_g‖ ∂μ₀` directly via `integrated_coupling_gronwall_bound` (the
-- `Q 0 = 0` case) — never forming `t ↦ (wasserstein1 (f t) (g t)).toReal` —
-- so closed-window continuity of the real-valued W₁ distance is not needed.


/-- The origin trajectory `s ↦ (charX s 0, charV s 0)` of a flow continuous on
`[0, T]` is norm-bounded by some `Kc ≥ 0` (compactness). -/
private lemma dobrushinFlow_origin_trajectory_bound
    {d : ℕ} (T : ℝ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hcont : ContinuousOn (fun s => (charX s 0, charV s 0)) (Set.Icc (0 : ℝ) T)) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖(charX s 0, charV s 0)‖ ≤ Kc := by
  have hbdd : BddAbove ((fun s => ‖(charX s 0, charV s 0)‖) '' Set.Icc (0 : ℝ) T) :=
    IsCompact.bddAbove_image isCompact_Icc hcont.norm
  obtain ⟨Kc, hKc⟩ := hbdd
  refine ⟨max Kc 0, le_max_right _ _, fun s hs => ?_⟩
  exact le_trans (hKc (Set.mem_image_of_mem _ hs)) (le_max_left _ _)

/-- Linear-in-`‖ω‖` norm bound on a flow from its Lipschitz-in-`z` estimate and
a bound on the origin trajectory: `‖Φ s ω‖ ≤ e^{KT} ‖ω‖ + Kc` on `[0, T]`. -/
private lemma dobrushinFlow_flow_norm_bound
    {d : ℕ}
    (T : ℝ) (K : NNReal)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (Kc : ℝ)
    (hlip : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂) ≤
      dist z₁ z₂ * Real.exp (((K : NNReal) : ℝ) * (s - 0)))
    (hKc : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖(charX s 0, charV s 0)‖ ≤ Kc) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω : PhaseSpace d,
      ‖(charX s ω, charV s ω)‖ ≤ Real.exp (((K : NNReal) : ℝ) * T) * ‖ω‖ + Kc := by
  have hK_nn : (0 : ℝ) ≤ ((K : NNReal) : ℝ) := K.coe_nonneg
  set EKT : ℝ := Real.exp (((K : NNReal) : ℝ) * T) with hEKT_def
  intro s hs ω
  have htri : ‖(charX s ω, charV s ω)‖ ≤
      dist ((charX s ω, charV s ω) : PhaseSpace d) (charX s 0, charV s 0)
        + ‖(charX s 0, charV s 0)‖ := by
    rw [dist_eq_norm]
    calc ‖(charX s ω, charV s ω)‖
        = ‖((charX s ω, charV s ω) - (charX s 0, charV s 0))
            + ((charX s 0, charV s 0) : PhaseSpace d)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖((charX s ω, charV s ω) : PhaseSpace d) - (charX s 0, charV s 0)‖
            + ‖(charX s 0, charV s 0)‖ := norm_add_le _ _
  have hdist_le : dist ((charX s ω, charV s ω) : PhaseSpace d) (charX s 0, charV s 0)
      ≤ EKT * ‖ω‖ := by
    refine le_trans (hlip s hs ω 0) ?_
    rw [dist_zero_right]
    have hsT : (((K : NNReal) : ℝ)) * (s - 0) ≤ (((K : NNReal) : ℝ)) * T := by
      rw [sub_zero]; exact mul_le_mul_of_nonneg_left hs.2 hK_nn
    have hexp_le : Real.exp (((K : NNReal) : ℝ) * (s - 0)) ≤ EKT :=
      Real.exp_le_exp.mpr hsT
    calc ‖ω‖ * Real.exp (((K : NNReal) : ℝ) * (s - 0))
        ≤ ‖ω‖ * EKT := mul_le_mul_of_nonneg_left hexp_le (norm_nonneg _)
      _ = EKT * ‖ω‖ := by ring
  calc ‖(charX s ω, charV s ω)‖
      ≤ dist ((charX s ω, charV s ω) : PhaseSpace d) (charX s 0, charV s 0)
          + ‖(charX s 0, charV s 0)‖ := htri
    _ ≤ EKT * ‖ω‖ + Kc := by
        gcongr
        exact hKc s hs

/-- Pushforward-convolution identity, generic in the base `ν`: when
`μ s = (charX s, charV s)_# ν`, the convolution force against the spatial
marginal of `μ s` is the `ν`-integral of the pushed-forward kernel. -/
private lemma dobrushinFlow_conv_pushforward
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (T : ℝ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (μ : ℝ → Measure (PhaseSpace d)) (ν : Measure (PhaseSpace d))
    (hpush : ∀ t ∈ Set.Icc (0 : ℝ) T,
      μ t = Measure.map (fun z => (charX t z, charV t z)) ν)
    (haem : ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) ν) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x : PhysSpace d,
      convolveFunctionMeasure gradW (spatialMarginal (μ s)) x
        = ∫ ω', gradW (x - charX s ω') ∂ν := by
  intro s hs x
  unfold convolveFunctionMeasure spatialMarginal
  rw [hpush s hs]
  have haem_s : AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) ν :=
    haem s hs
  have hmeas_gradW : AEStronglyMeasurable
      (fun y : PhysSpace d => gradW (x - y))
      (Measure.map Prod.fst (Measure.map (fun z => (charX s z, charV s z)) ν)) :=
    (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  rw [integral_map measurable_fst.aemeasurable hmeas_gradW]
  have hmeas_inner : AEStronglyMeasurable
      (fun z : PhaseSpace d => gradW (x - z.1))
      (Measure.map (fun z => (charX s z, charV s z)) ν) :=
    ((hL.continuous.comp (continuous_const.sub continuous_fst))).aestronglyMeasurable
  rw [integral_map haem_s hmeas_inner]

/-- Companion integrability transfer for `dobrushinFlow_conv_pushforward`,
generic in the base `ν`. -/
private lemma dobrushinFlow_gradW_int_pushforward
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (T : ℝ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (μ : ℝ → Measure (PhaseSpace d)) (ν : Measure (PhaseSpace d))
    (hpush : ∀ t ∈ Set.Icc (0 : ℝ) T,
      μ t = Measure.map (fun z => (charX t z, charV t z)) ν)
    (haem : ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) ν)
    (hint_sm : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (μ t))) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x : PhysSpace d,
      Integrable (fun ω' => gradW (x - charX s ω')) ν := by
  intro s hs x
  have hsm := hint_sm s hs x
  unfold spatialMarginal at hsm
  rw [hpush s hs] at hsm
  rw [integrable_map_measure
    (g := fun y : PhysSpace d => gradW (x - y))
    ((hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    measurable_fst.aemeasurable] at hsm
  simp only [Function.comp_def] at hsm
  rw [integrable_map_measure
    (g := fun z : PhaseSpace d => gradW (x - z.1))
    ((hL.continuous.comp (continuous_const.sub continuous_fst)).aestronglyMeasurable)
    (haem s hs)] at hsm
  exact hsm

/-- Phase-space integrability of a pushforward flow over its base, from the
first moments of the pushed-forward curve. -/
private lemma dobrushinFlow_phase_int_pushforward
    {d : ℕ} (T : ℝ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (μ : ℝ → Measure (PhaseSpace d)) (ν : Measure (PhaseSpace d))
    (hpush : ∀ t ∈ Set.Icc (0 : ℝ) T,
      μ t = Measure.map (fun z => (charX t z, charV t z)) ν)
    (haem : ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) ν)
    (hmom : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun z : PhaseSpace d => ‖z‖) (μ t)) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun ω' : PhaseSpace d => (charX s ω', charV s ω')) ν := by
  intro s hs
  have hid : Integrable (fun z : PhaseSpace d => z) (μ s) :=
    (integrable_norm_iff aestronglyMeasurable_id).mp (hmom s hs)
  rw [hpush s hs] at hid
  rw [integrable_map_measure
    (g := fun z : PhaseSpace d => z) aestronglyMeasurable_id (haem s hs)] at hid
  exact hid

/-- Global continuity in `s` of the clamped Vlasov field along a clamped
trajectory: velocity slot continuous from the flow; force slot a pushforward
integral over the base `ν`, continuous by moment-free dominated convergence.
Generic in the base `ν` and clamp `clampT`. -/
private lemma dobrushinFlow_field_continuous
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (T : ℝ) (K : NNReal)
    (clampT : ℝ → ℝ) (hclampT_mem : ∀ s, clampT s ∈ Set.Icc (0 : ℝ) T)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (μ : ℝ → Measure (PhaseSpace d)) (ν : Measure (PhaseSpace d)) (Kc : ℝ)
    (b : ℝ → PhaseSpace d → PhaseSpace d) (X : ℝ → PhaseSpace d → PhaseSpace d)
    (hb : b = fun s => vlasovVectorField gradW (fun s => spatialMarginal (μ (clampT s))) s)
    (hX : X = fun s ω => (charX (clampT s) ω, charV (clampT s) ω))
    (hflowcont : ∀ z, Continuous (fun s => (charX (clampT s) z, charV (clampT s) z)))
    (hpush : ∀ t ∈ Set.Icc (0 : ℝ) T,
      μ t = Measure.map (fun z => (charX t z, charV t z)) ν)
    (haem : ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) ν)
    (hν_prob : IsProbabilityMeasure ν)
    (hν_mom : Integrable (fun z : PhaseSpace d => ‖z‖) ν)
    (hKc : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖(charX s 0, charV s 0)‖ ≤ Kc)
    (hlip : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂) ≤
      dist z₁ z₂ * Real.exp (((K : NNReal) : ℝ) * (s - 0))) :
    ∀ ω, Continuous (fun s => b s (X s ω)) := by
  intro ω
  have := hν_prob
  set EKT : ℝ := Real.exp (((K : NNReal) : ℝ) * T) with hEKT_def
  have hΦnorm : ∀ s : ℝ, ∀ z : PhaseSpace d,
      ‖(charX (clampT s) z, charV (clampT s) z)‖ ≤ EKT * ‖z‖ + Kc := by
    rw [hEKT_def]
    exact fun s z =>
      dobrushinFlow_flow_norm_bound T K charX charV Kc hlip hKc
        (clampT s) (hclampT_mem s) z
  subst hb hX
  set xS : ℝ → PhysSpace d := fun s => charX (clampT s) ω with hxS_def
  have hxS_cont : Continuous xS := (continuous_fst.comp (hflowcont ω))
  have hforce_eq : ∀ s : ℝ,
      convolveFunctionMeasure gradW (spatialMarginal (μ (clampT s))) (xS s)
        = ∫ ω', gradW (xS s - charX (clampT s) ω') ∂ν := by
    intro s
    exact dobrushinFlow_conv_pushforward gradW L hL T charX charV μ ν hpush haem
      (clampT s) (hclampT_mem s) (xS s)
  have hforce_cont : Continuous
      (fun s => ∫ ω', gradW (xS s - charX (clampT s) ω') ∂ν) := by
    set bnd : PhaseSpace d → ℝ := fun ω' =>
      ‖gradW 0‖ + (L : ℝ) * ((EKT * ‖ω‖ + Kc) + (EKT * ‖ω'‖ + Kc)) with hbnd_def
    have hbnd_int : Integrable bnd ν := by
      simp only [hbnd_def]
      have hmom : Integrable (fun ω' : PhaseSpace d => ‖ω'‖) ν := hν_mom
      have hL_EKT : Integrable (fun ω' : PhaseSpace d => (L : ℝ) * (EKT * ‖ω'‖)) ν := by
        have : Integrable (fun ω' : PhaseSpace d => EKT * ‖ω'‖) ν :=
          hmom.const_mul EKT
        exact this.const_mul (L : ℝ)
      have heq : (fun ω' : PhaseSpace d =>
          ‖gradW 0‖ + (L : ℝ) * ((EKT * ‖ω‖ + Kc) + (EKT * ‖ω'‖ + Kc))) =
          fun ω' => (‖gradW 0‖ + (L : ℝ) * ((EKT * ‖ω‖ + Kc) + Kc))
            + (L : ℝ) * (EKT * ‖ω'‖) := by
        funext ω'; ring
      rw [heq]; exact (integrable_const _).add hL_EKT
    refine continuous_of_dominated
      (fun s => ?_) (fun s => Filter.Eventually.of_forall (fun ω' => ?_)) hbnd_int
      (Filter.Eventually.of_forall (fun ω' => ?_))
    · have haem_charX : AEMeasurable (fun ω' : PhaseSpace d => charX (clampT s) ω') ν :=
        (measurable_fst.comp_aemeasurable (haem (clampT s) (hclampT_mem s)))
      exact ((hL.continuous.comp
          (continuous_const.sub continuous_id)).measurable.comp_aemeasurable
        haem_charX).aestronglyMeasurable
    · have hd := hL.dist_le_mul (xS s - charX (clampT s) ω') 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (xS s - charX (clampT s) ω')‖ ≤
          ‖gradW 0‖ + ‖gradW (xS s - charX (clampT s) ω') - gradW 0‖ := by
        have := norm_add_le (gradW (xS s - charX (clampT s) ω') - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      have hsub_le : ‖xS s - charX (clampT s) ω'‖ ≤ ‖xS s‖ + ‖charX (clampT s) ω'‖ :=
        norm_sub_le _ _
      have hxS_le : ‖xS s‖ ≤ EKT * ‖ω‖ + Kc := by
        simp only [hxS_def]
        exact le_trans
          (norm_fst_le ((charX (clampT s) ω, charV (clampT s) ω) : PhaseSpace d))
          (hΦnorm s ω)
      have hcharX_le : ‖charX (clampT s) ω'‖ ≤ EKT * ‖ω'‖ + Kc :=
        le_trans
          (norm_fst_le ((charX (clampT s) ω', charV (clampT s) ω') : PhaseSpace d))
          (hΦnorm s ω')
      have h_mul := mul_le_mul_of_nonneg_left
        (le_trans hsub_le (add_le_add hxS_le hcharX_le)) L.coe_nonneg
      simp only [hbnd_def]; linarith
    · exact hL.continuous.comp (hxS_cont.sub
        (continuous_fst.comp (hflowcont ω')))
  have hvel_cont : Continuous (fun s => (charX (clampT s) ω, charV (clampT s) ω).2) :=
    continuous_snd.comp (hflowcont ω)
  have hbody : (fun s => vlasovVectorField gradW
        (fun s => spatialMarginal (μ (clampT s))) s
        ((charX (clampT s) ω, charV (clampT s) ω)))
      = fun s => ((charX (clampT s) ω, charV (clampT s) ω).2,
          -(∫ ω', gradW (xS s - charX (clampT s) ω') ∂ν)) := by
    funext s
    simp only [vlasovVectorField]
    refine Prod.ext rfl ?_
    change -(convolveFunctionMeasure gradW (spatialMarginal (μ (clampT s)))
        (charX (clampT s) ω, charV (clampT s) ω).1)
      = -(∫ ω', gradW (xS s - charX (clampT s) ω') ∂ν)
    rw [hforce_eq s]
  rw [hbody]
  exact hvel_cont.prodMk hforce_cont.neg

/-- Open-window flow ODE in `z` for the clamped field: on `Ioo 0 T` the clamp
is the identity, so the witness `HasDerivAt` pair transfers to
`HasDerivWithinAt` on `Ici s` against the clamped vector field. -/
private lemma dobrushinFlow_deriv_Ioo
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (T : ℝ) (clampT : ℝ → ℝ)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (μ : ℝ → Measure (PhaseSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow_x : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
      HasDerivAt (fun s' => charX s' z) (charV s z) s)
    (hflow_v : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
      HasDerivAt (fun s' => charV s' z)
        (-(convolveFunctionMeasure gradW (spatialMarginal (μ s)) (charX s z))) s) :
    ∀ z : PhaseSpace d, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW (fun s => spatialMarginal (μ (clampT s))) s
          (charX s z, charV s z)) (Set.Ici s) s := by
  intro z s hs
  have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
  have hat : HasDerivAt (fun s' => (charX s' z, charV s' z))
      (vlasovVectorField gradW (fun s => spatialMarginal (μ s)) s
        (charX s z, charV s z)) s := by
    change HasDerivAt (fun s' => (charX s' z, charV s' z))
      ((charX s z, charV s z).2,
       -(convolveFunctionMeasure gradW (spatialMarginal (μ s))
          (charX s z, charV s z).1)) s
    exact (hflow_x s hs z (Set.mem_univ z)).prodMk (hflow_v s hs z (Set.mem_univ z))
  have hmeas : spatialMarginal (μ (clampT s)) = spatialMarginal (μ s) := by
    rw [hclampT_id s hsIcc]
  have hvf_eq : vlasovVectorField gradW (fun s => spatialMarginal (μ (clampT s))) s
        (charX s z, charV s z)
      = vlasovVectorField gradW (fun s => spatialMarginal (μ s)) s
        (charX s z, charV s z) := by
    simp only [vlasovVectorField, hmeas]
  rw [hvf_eq]; exact hat.hasDerivWithinAt

/-- Per-`ω` continuity on `[0, T]` of a clamped trajectory family read through
a projection: the clamp composes continuously and is the identity on-window. -/
private lemma dobrushinFlow_clamped_cont
    {d : ℕ} {Ω : Type*}
    (T : ℝ) (clampT : ℝ → ℝ) (hclampT_cont : Continuous clampT)
    (hclampT_mem : ∀ s, clampT s ∈ Set.Icc (0 : ℝ) T)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (proj : Ω → PhaseSpace d)
    (hcontIcc : ∀ z, ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc 0 T))
    (X : ℝ → Ω → PhaseSpace d)
    (hX : X = fun s ω => (charX (clampT s) (proj ω), charV (clampT s) (proj ω))) :
    ∀ ω, ContinuousOn (fun s => X s ω) (Set.Icc 0 T) := by
  intro ω
  have hbase : ContinuousOn (fun s => (charX s (proj ω), charV s (proj ω)))
      (Set.Icc 0 T) := hcontIcc (proj ω)
  apply ContinuousOn.congr
    (f := fun s => (charX (clampT s) (proj ω), charV (clampT s) (proj ω)))
  · exact hbase.comp hclampT_cont.continuousOn (fun s hs => hclampT_mem s)
  · intro s hs; simp only [hX, hclampT_id s hs]

/-- Per-`ω` ODE on `Ioo 0 T` of a clamped trajectory family against the
clamped field (`HasDerivWithinAt` on `Ioi s`), via the witness `HasDerivAt`
pair and on-window clamp-identity congruence. -/
private lemma dobrushinFlow_clamped_deriv
    {d : ℕ} {Ω : Type*}
    (gradW : PhysSpace d → PhysSpace d)
    (T : ℝ) (clampT : ℝ → ℝ)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (μ : ℝ → Measure (PhaseSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (proj : Ω → PhaseSpace d)
    (hflow_x : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
      HasDerivAt (fun s' => charX s' z) (charV s z) s)
    (hflow_v : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
      HasDerivAt (fun s' => charV s' z)
        (-(convolveFunctionMeasure gradW (spatialMarginal (μ s)) (charX s z))) s)
    (b : ℝ → PhaseSpace d → PhaseSpace d)
    (hb_id : ∀ s ∈ Set.Icc (0 : ℝ) T,
      b s = vlasovVectorField gradW (fun s => spatialMarginal (μ s)) s)
    (X : ℝ → Ω → PhaseSpace d)
    (hX : X = fun s ω => (charX (clampT s) (proj ω), charV (clampT s) (proj ω))) :
    ∀ ω, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => X s ω) (b s (X s ω)) (Set.Ioi s) s := by
  intro ω s hs
  have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
  have hat : HasDerivAt (fun s' => (charX s' (proj ω), charV s' (proj ω)))
      (vlasovVectorField gradW (fun s => spatialMarginal (μ s)) s
        (charX s (proj ω), charV s (proj ω))) s := by
    change HasDerivAt (fun s' => (charX s' (proj ω), charV s' (proj ω)))
      ((charX s (proj ω), charV s (proj ω)).2,
       -(convolveFunctionMeasure gradW (spatialMarginal (μ s))
          (charX s (proj ω), charV s (proj ω)).1)) s
    exact (hflow_x s hs (proj ω) (Set.mem_univ _)).prodMk
      (hflow_v s hs (proj ω) (Set.mem_univ _))
  have hwithin : HasDerivWithinAt (fun s' => (charX s' (proj ω), charV s' (proj ω)))
      (vlasovVectorField gradW (fun s => spatialMarginal (μ s)) s
        (charX s (proj ω), charV s (proj ω))) (Set.Ioi s) s := hat.hasDerivWithinAt
  have heq : Set.EqOn (fun s' => X s' ω)
      (fun s' => (charX s' (proj ω), charV s' (proj ω))) (Set.Ioo (0 : ℝ) T) := by
    intro s' hs'; simp only [hX, hclampT_id s' ⟨hs'.1.le, hs'.2.le⟩]
  have hmem_nhds : Set.Ioo (0 : ℝ) T ∈ nhdsWithin s (Set.Ioi s) :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hs)
  have hx : X s ω = (charX s (proj ω), charV s (proj ω)) := by
    simp only [hX, hclampT_id s hsIcc]
  have hwithin' := hwithin.congr_of_eventuallyEq
    (Filter.eventually_of_mem hmem_nhds (fun s' hs' => heq hs'))
    hx
  rw [hb_id s hsIcc, hx]; exact hwithin'


/-- First-moment transfer to the base: `∫ ‖proj ω‖ dπ₀` is finite when the
pushed-forward marginal has a finite first moment. -/
private lemma dobrushinFlow_proj_moment
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (π₀ : Measure Ω) (proj : Ω → PhaseSpace d) (hproj : Measurable proj)
    (μ0 : Measure (PhaseSpace d)) (hmarg : μ0 = Measure.map proj π₀)
    (hmom : Integrable (fun z : PhaseSpace d => ‖z‖) μ0) :
    Integrable (fun ω : Ω => ‖proj ω‖) π₀ := by
  have hmap : Integrable (fun z : PhaseSpace d => ‖z‖) (Measure.map proj π₀) := by
    rw [← hmarg]; exact hmom
  exact (integrable_map_measure continuous_norm.aestronglyMeasurable
    hproj.aemeasurable).mp hmap

/-- On `[0, T]` the clamped Vlasov field coincides with the genuine field. -/
private lemma dobrushinFlow_clamped_field_id
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (T : ℝ) (clampT : ℝ → ℝ)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (μ : ℝ → Measure (PhaseSpace d))
    (b : ℝ → PhaseSpace d → PhaseSpace d)
    (hb : b = fun s => vlasovVectorField gradW (fun s => spatialMarginal (μ (clampT s))) s) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      b s = vlasovVectorField gradW (fun s => spatialMarginal (μ s)) s := by
  intro s hs
  have hmeas : spatialMarginal (μ (clampT s)) = spatialMarginal (μ s) := by
    rw [hclampT_id s hs]
  funext z; simp only [hb, vlasovVectorField, hmeas]

/-- Moment-free dominator bound: the coupled trajectory difference is bounded
by `e^{KT}(‖proj_f ω‖ + ‖proj_g ω‖) + (K_f + K_g)` on `[0, T]`. -/
private lemma dobrushinFlow_dominator_bound
    {d : ℕ} {Ω : Type*}
    (T : ℝ) (clampT : ℝ → ℝ)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (charX_f charV_f charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (proj_f proj_g : Ω → PhaseSpace d)
    (EKT K_f K_g : ℝ)
    (hfnorm : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω : PhaseSpace d,
      ‖(charX_f s ω, charV_f s ω)‖ ≤ EKT * ‖ω‖ + K_f)
    (hgnorm : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω : PhaseSpace d,
      ‖(charX_g s ω, charV_g s ω)‖ ≤ EKT * ‖ω‖ + K_g)
    (X_f X_g : ℝ → Ω → PhaseSpace d)
    (hX_f : X_f = fun s ω => (charX_f (clampT s) (proj_f ω), charV_f (clampT s) (proj_f ω)))
    (hX_g : X_g = fun s ω => (charX_g (clampT s) (proj_g ω), charV_g (clampT s) (proj_g ω))) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω,
      ‖X_f s ω - X_g s ω‖ ≤ EKT * ‖proj_f ω‖ + EKT * ‖proj_g ω‖ + (K_f + K_g) := by
  intro s hs ω
  have hclamp_eq : clampT s = s := hclampT_id s hs
  have hXf : X_f s ω = (charX_f s (proj_f ω), charV_f s (proj_f ω)) := by
    simp only [hX_f, hclamp_eq]
  have hXg : X_g s ω = (charX_g s (proj_g ω), charV_g s (proj_g ω)) := by
    simp only [hX_g, hclamp_eq]
  rw [hXf, hXg]
  calc ‖(charX_f s (proj_f ω), charV_f s (proj_f ω))
          - (charX_g s (proj_g ω), charV_g s (proj_g ω))‖
      ≤ ‖(charX_f s (proj_f ω), charV_f s (proj_f ω))‖
          + ‖(charX_g s (proj_g ω), charV_g s (proj_g ω))‖ := norm_sub_le _ _
    _ ≤ (EKT * ‖proj_f ω‖ + K_f) + (EKT * ‖proj_g ω‖ + K_g) := by
        have hf_bd := hfnorm s hs (proj_f ω)
        have hg_bd := hgnorm s hs (proj_g ω)
        gcongr
    _ = EKT * ‖proj_f ω‖ + EKT * ‖proj_g ω‖ + (K_f + K_g) := by ring

/-- Global continuity in `s` of the integrated trajectory distance
`s ↦ ∫ ‖X_f s − X_g s‖ dπ₀`, by moment-free dominated convergence (the clamp
makes the integrand globally continuous per `ω` and globally dominated). -/
private lemma dobrushinFlow_Q_continuous
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (T : ℝ) (clampT : ℝ → ℝ) (hclampT_cont : Continuous clampT)
    (hclampT_mem : ∀ s, clampT s ∈ Set.Icc (0 : ℝ) T)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (π₀ : Measure Ω)
    (charX_f charV_f charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (proj_f proj_g : Ω → PhaseSpace d)
    (hcontIcc_f : ∀ z, ContinuousOn (fun s => (charX_f s z, charV_f s z)) (Set.Icc 0 T))
    (hcontIcc_g : ∀ z, ContinuousOn (fun s => (charX_g s z, charV_g s z)) (Set.Icc 0 T))
    (X_f X_g : ℝ → Ω → PhaseSpace d)
    (hX_f : X_f = fun s ω => (charX_f (clampT s) (proj_f ω), charV_f (clampT s) (proj_f ω)))
    (hX_g : X_g = fun s ω => (charX_g (clampT s) (proj_g ω), charV_g (clampT s) (proj_g ω)))
    (hmeas_f : ∀ s, Measurable (X_f s)) (hmeas_g : ∀ s, Measurable (X_g s))
    (dom : Ω → ℝ) (hdom_int : Integrable dom π₀)
    (hdom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, ‖X_f s ω - X_g s ω‖ ≤ dom ω) :
    Continuous (fun s => ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀) := by
  have hXf_cont_glob : ∀ ω, Continuous (fun s => X_f s ω) := by
    intro ω
    have : Continuous (fun s => (charX_f (clampT s) (proj_f ω), charV_f (clampT s) (proj_f ω))) :=
      (hcontIcc_f (proj_f ω)).comp_continuous hclampT_cont (fun s => hclampT_mem s)
    simpa only [hX_f] using this
  have hXg_cont_glob : ∀ ω, Continuous (fun s => X_g s ω) := by
    intro ω
    have : Continuous (fun s => (charX_g (clampT s) (proj_g ω), charV_g (clampT s) (proj_g ω))) :=
      (hcontIcc_g (proj_g ω)).comp_continuous hclampT_cont (fun s => hclampT_mem s)
    simpa only [hX_g] using this
  refine continuous_of_dominated
    (fun s => ((hmeas_f s).sub (hmeas_g s)).norm.aestronglyMeasurable)
    (fun s => Filter.Eventually.of_forall (fun ω => ?_))
    hdom_int
    (Filter.Eventually.of_forall (fun ω => ((hXf_cont_glob ω).sub (hXg_cont_glob ω)).norm))
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  have hcl : clampT s ∈ Set.Icc (0 : ℝ) T := hclampT_mem s
  have hXf : X_f s ω = X_f (clampT s) ω := by
    simp only [hX_f]; rw [hclampT_id (clampT s) hcl]
  have hXg : X_g s ω = X_g (clampT s) ω := by
    simp only [hX_g]; rw [hclampT_id (clampT s) hcl]
  rw [hXf, hXg]; exact hdom (clampT s) hcl ω

/-- **Cross-field bound**: the convolution-force difference of the two fields
along the second trajectory is bounded by `(max 1 L)` times the integrated
trajectory distance — established through the two marginal identities on the
common base `π₀`, never forming `wasserstein1 (f s) (g s)`. -/
private lemma dobrushinFlow_cross_field_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (T : ℝ) (clampT : ℝ → ℝ)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (π₀ : Measure Ω)
    (f g : ℝ → Measure (PhaseSpace d))
    (charX_f charV_f charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (proj_f proj_g : Ω → PhaseSpace d)
    (hproj_f : Measurable proj_f) (hproj_g : Measurable proj_g)
    (hpush_f : ∀ t ∈ Set.Icc (0 : ℝ) T,
      f t = Measure.map (fun z => (charX_f t z, charV_f t z)) (f 0))
    (haem_f : ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX_f s z, charV_f s z)) (f 0))
    (hpush_g : ∀ t ∈ Set.Icc (0 : ℝ) T,
      g t = Measure.map (fun z => (charX_g t z, charV_g t z)) (g 0))
    (haem_g : ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) (g 0))
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (g t))
    (hmarg_f : f 0 = Measure.map proj_f π₀)
    (hmarg_g : g 0 = Measure.map proj_g π₀)
    (h_int_f : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (f t)))
    (h_int_g : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (g t)))
    (hmeas_charf : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX_f s z, charV_f s z)))
    (hmeas_charg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)))
    (X_f X_g : ℝ → Ω → PhaseSpace d)
    (hX_f : X_f = fun s ω => (charX_f (clampT s) (proj_f ω), charV_f (clampT s) (proj_f ω)))
    (hX_g : X_g = fun s ω => (charX_g (clampT s) (proj_g ω), charV_g (clampT s) (proj_g ω)))
    (b_f b_g : ℝ → PhaseSpace d → PhaseSpace d)
    (hb_f_id : ∀ s ∈ Set.Icc (0 : ℝ) T,
      b_f s = vlasovVectorField gradW (fun s => spatialMarginal (f s)) s)
    (hb_g_id : ∀ s ∈ Set.Icc (0 : ℝ) T,
      b_g s = vlasovVectorField gradW (fun s => spatialMarginal (g s)) s)
    (hmeas_f : ∀ s, Measurable (X_f s)) (hmeas_g : ∀ s, Measurable (X_g s))
    (dom : Ω → ℝ) (hdom_int : Integrable dom π₀)
    (hdom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, ‖X_f s ω - X_g s ω‖ ≤ dom ω) :
    ∀ ω, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖b_f s (X_g s ω) - b_g s (X_g s ω)‖ ≤
        ((max 1 L : NNReal) : ℝ) * ∫ ω', ‖X_f s ω' - X_g s ω'‖ ∂π₀ := by
  intro ω s hs
  have : IsProbabilityMeasure (f s) := (hf_mom s hs).1
  have : IsProbabilityMeasure (g s) := (hg_mom s hs).1
  have hL_le_max : (L : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
    rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_right _ _
  set x : PhysSpace d := (X_g s ω).1 with hx_def
  have hb_f_s := hb_f_id s hs
  have hb_g_s := hb_g_id s hs
  have h_form : b_f s (X_g s ω) - b_g s (X_g s ω) =
      ((0 : PhysSpace d),
       convolveFunctionMeasure gradW (spatialMarginal (g s)) x
         - convolveFunctionMeasure gradW (spatialMarginal (f s)) x) := by
    rw [hb_f_s, hb_g_s]
    simp only [vlasovVectorField, Prod.mk_sub_mk, sub_self, hx_def]
    refine Prod.ext rfl ?_
    change -(convolveFunctionMeasure gradW (spatialMarginal (f s)) (X_g s ω).1)
          - -(convolveFunctionMeasure gradW (spatialMarginal (g s)) (X_g s ω).1)
        = convolveFunctionMeasure gradW (spatialMarginal (g s)) (X_g s ω).1
          - convolveFunctionMeasure gradW (spatialMarginal (f s)) (X_g s ω).1
    abel
  rw [h_form, Prod.norm_def]
  simp only [norm_zero]
  rw [max_eq_right (norm_nonneg _)]
  rw [dobrushinFlow_conv_pushforward gradW L hL T charX_g charV_g g (g 0)
        hpush_g haem_g s hs x,
      dobrushinFlow_conv_pushforward gradW L hL T charX_f charV_f f (f 0)
        hpush_f haem_f s hs x]
  have hmeas_charf_s : Measurable (fun z : PhaseSpace d => charX_f s z) :=
    measurable_fst.comp (hmeas_charf s hs)
  have hmeas_charg_s : Measurable (fun z : PhaseSpace d => charX_g s z) :=
    measurable_fst.comp (hmeas_charg s hs)
  have hmap_g : (∫ ω', gradW (x - charX_g s ω') ∂(g 0))
      = ∫ ω, gradW (x - charX_g s (proj_g ω)) ∂π₀ := by
    rw [hmarg_g]
    exact integral_map hproj_g.aemeasurable
      (((hL.continuous.comp (continuous_const.sub continuous_id)).measurable.comp
        hmeas_charg_s).aestronglyMeasurable)
  have hmap_f : (∫ ω', gradW (x - charX_f s ω') ∂(f 0))
      = ∫ ω, gradW (x - charX_f s (proj_f ω)) ∂π₀ := by
    rw [hmarg_f]
    exact integral_map hproj_f.aemeasurable
      (((hL.continuous.comp (continuous_const.sub continuous_id)).measurable.comp
        hmeas_charf_s).aestronglyMeasurable)
  rw [hmap_g, hmap_f]
  have hint_g_π : Integrable (fun ω => gradW (x - charX_g s (proj_g ω))) π₀ := by
    have hbase : Integrable (fun ω' => gradW (x - charX_g s ω')) (g 0) :=
      dobrushinFlow_gradW_int_pushforward gradW L hL T charX_g charV_g g (g 0)
        hpush_g haem_g h_int_g s hs x
    rw [hmarg_g] at hbase
    exact (integrable_map_measure
      (((hL.continuous.comp (continuous_const.sub continuous_id)).measurable.comp
        hmeas_charg_s).aestronglyMeasurable) hproj_g.aemeasurable).mp hbase
  have hint_f_π : Integrable (fun ω => gradW (x - charX_f s (proj_f ω))) π₀ := by
    have hbase : Integrable (fun ω' => gradW (x - charX_f s ω')) (f 0) :=
      dobrushinFlow_gradW_int_pushforward gradW L hL T charX_f charV_f f (f 0)
        hpush_f haem_f h_int_f s hs x
    rw [hmarg_f] at hbase
    exact (integrable_map_measure
      (((hL.continuous.comp (continuous_const.sub continuous_id)).measurable.comp
        hmeas_charf_s).aestronglyMeasurable) hproj_f.aemeasurable).mp hbase
  rw [← integral_sub hint_g_π hint_f_π]
  have h_pt : ∀ ω, ‖gradW (x - charX_g s (proj_g ω)) - gradW (x - charX_f s (proj_f ω))‖
      ≤ (L : ℝ) * ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖ := by
    intro ω
    have hd := hL.dist_le_mul (x - charX_g s (proj_g ω)) (x - charX_f s (proj_f ω))
    rw [dist_eq_norm, dist_eq_norm] at hd
    have hsub : (x - charX_g s (proj_g ω)) - (x - charX_f s (proj_f ω))
        = charX_f s (proj_f ω) - charX_g s (proj_g ω) := by abel
    rw [hsub] at hd; exact hd
  have hf_phase_int : Integrable
      (fun ω => ((charX_f s (proj_f ω), charV_f s (proj_f ω)) : PhaseSpace d)) π₀ := by
    have hbase : Integrable (fun ω' : PhaseSpace d => (charX_f s ω', charV_f s ω')) (f 0) :=
      dobrushinFlow_phase_int_pushforward T charX_f charV_f f (f 0)
        hpush_f haem_f (fun t ht => (hf_mom t ht).2) s hs
    rw [hmarg_f] at hbase
    exact (integrable_map_measure (hmeas_charf s hs).aestronglyMeasurable
      hproj_f.aemeasurable).mp hbase
  have hg_phase_int : Integrable
      (fun ω => ((charX_g s (proj_g ω), charV_g s (proj_g ω)) : PhaseSpace d)) π₀ := by
    have hbase : Integrable (fun ω' : PhaseSpace d => (charX_g s ω', charV_g s ω')) (g 0) :=
      dobrushinFlow_phase_int_pushforward T charX_g charV_g g (g 0)
        hpush_g haem_g (fun t ht => (hg_mom t ht).2) s hs
    rw [hmarg_g] at hbase
    exact (integrable_map_measure (hmeas_charg s hs).aestronglyMeasurable
      hproj_g.aemeasurable).mp hbase
  have hnorm_int_le :
      ‖∫ ω, (gradW (x - charX_g s (proj_g ω)) - gradW (x - charX_f s (proj_f ω))) ∂π₀‖
        ≤ ∫ ω, (L : ℝ) * ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖ ∂π₀ := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine integral_mono (hint_g_π.sub hint_f_π).norm ?_ h_pt
    have hdiff_int : Integrable
        (fun ω => charX_f s (proj_f ω) - charX_g s (proj_g ω)) π₀ :=
      (hf_phase_int.fst).sub (hg_phase_int.fst)
    exact (hdiff_int.norm.const_mul (L : ℝ))
  refine le_trans hnorm_int_le ?_
  rw [integral_const_mul]
  have hpt2 : ∀ ω, ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖ ≤ ‖X_f s ω - X_g s ω‖ := by
    intro ω
    have hXf : X_f s ω = (charX_f s (proj_f ω), charV_f s (proj_f ω)) := by
      simp only [hX_f, hclampT_id s hs]
    have hXg : X_g s ω = (charX_g s (proj_g ω), charV_g s (proj_g ω)) := by
      simp only [hX_g, hclampT_id s hs]
    rw [hXf, hXg]
    have hsplit : ((charX_f s (proj_f ω), charV_f s (proj_f ω)) : PhaseSpace d)
          - (charX_g s (proj_g ω), charV_g s (proj_g ω)) =
        ((charX_f s (proj_f ω) - charX_g s (proj_g ω)),
          (charV_f s (proj_f ω) - charV_g s (proj_g ω))) := by
      rw [Prod.mk_sub_mk]
    rw [hsplit, Prod.norm_def]; exact le_max_left _ _
  have hdiff_norm_int : Integrable
      (fun ω => ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖) π₀ :=
    ((hf_phase_int.fst).sub (hg_phase_int.fst)).norm
  have hXdiff_norm_int : Integrable (fun ω => ‖X_f s ω - X_g s ω‖) π₀ :=
    Integrable.mono' hdom_int
      ((hmeas_f s).sub (hmeas_g s)).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hdom s hs ω)
  have hQ_le : ∫ ω, ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖ ∂π₀
      ≤ ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀ :=
    integral_mono hdiff_norm_int hXdiff_norm_int hpt2
  calc (L : ℝ) * ∫ ω, ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖ ∂π₀
      ≤ (L : ℝ) * ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀ :=
        mul_le_mul_of_nonneg_left hQ_le L.coe_nonneg
    _ ≤ ((max 1 L : NNReal) : ℝ) * ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀ :=
        mul_le_mul_of_nonneg_right hL_le_max (integral_nonneg fun _ => norm_nonneg _)

/-- Conclusion transfer: rewrite the integrated-coupling core's bound and the
associated integrability from the clamped `X`-form into the conclusion's
`proj`-form, using the initial-identity of the flows at `t = 0`. -/
private lemma dobrushinFlow_conclusion_transfer
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (T : ℝ) (hT : 0 < T) (clampT : ℝ → ℝ)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (π₀ : Measure Ω) (L : NNReal)
    (charX_f charV_f charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (proj_f proj_g : Ω → PhaseSpace d)
    (hinit_f' : ∀ z : PhaseSpace d, (charX_f 0 z, charV_f 0 z) = z)
    (hinit_g' : ∀ z : PhaseSpace d, (charX_g 0 z, charV_g 0 z) = z)
    (X_f X_g : ℝ → Ω → PhaseSpace d)
    (hX_f : X_f = fun s ω => (charX_f (clampT s) (proj_f ω), charV_f (clampT s) (proj_f ω)))
    (hX_g : X_g = fun s ω => (charX_g (clampT s) (proj_g ω), charV_g (clampT s) (proj_g ω)))
    (hmeas_f : ∀ s, Measurable (X_f s)) (hmeas_g : ∀ s, Measurable (X_g s))
    (dom : Ω → ℝ) (hdom_int : Integrable dom π₀)
    (hdom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, ‖X_f s ω - X_g s ω‖ ≤ dom ω)
    (hcore : ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ ω, ‖X_f t ω - X_g t ω‖ ∂π₀) ≤
        (∫ ω, ‖X_f 0 ω - X_g 0 ω‖ ∂π₀) * Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun ω => ‖((charX_f t (proj_f ω), charV_f t (proj_f ω)) : PhaseSpace d)
              - (charX_g t (proj_g ω), charV_g t (proj_g ω))‖) π₀ ∧
      (∫ ω, ‖((charX_f t (proj_f ω), charV_f t (proj_f ω)) : PhaseSpace d)
              - (charX_g t (proj_g ω), charV_g t (proj_g ω))‖ ∂π₀)
        ≤ (∫ ω, ‖proj_f ω - proj_g ω‖ ∂π₀)
            * Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t) := by
  intro t ht
  have hbound := hcore t ht
  have hbase0 : (∫ ω, ‖X_f 0 ω - X_g 0 ω‖ ∂π₀) = ∫ ω, ‖proj_f ω - proj_g ω‖ ∂π₀ := by
    apply integral_congr_ae
    filter_upwards with ω
    have hXf0 : X_f 0 ω = proj_f ω := by
      simp only [hX_f, hclampT_id 0 ⟨le_refl 0, hT.le⟩]; exact hinit_f' (proj_f ω)
    have hXg0 : X_g 0 ω = proj_g ω := by
      simp only [hX_g, hclampT_id 0 ⟨le_refl 0, hT.le⟩]; exact hinit_g' (proj_g ω)
    rw [hXf0, hXg0]
  have hlhs : (∫ ω, ‖X_f t ω - X_g t ω‖ ∂π₀)
      = ∫ ω, ‖((charX_f t (proj_f ω), charV_f t (proj_f ω)) : PhaseSpace d)
             - (charX_g t (proj_g ω), charV_g t (proj_g ω))‖ ∂π₀ := by
    apply integral_congr_ae
    filter_upwards with ω
    have hXf : X_f t ω = (charX_f t (proj_f ω), charV_f t (proj_f ω)) := by
      simp only [hX_f, hclampT_id t ht]
    have hXg : X_g t ω = (charX_g t (proj_g ω), charV_g t (proj_g ω)) := by
      simp only [hX_g, hclampT_id t ht]
    rw [hXf, hXg]
  rw [hlhs, hbase0] at hbound
  refine ⟨?_, hbound⟩
  have hXfe : ∀ ω, X_f t ω = (charX_f t (proj_f ω), charV_f t (proj_f ω)) := fun ω => by
    simp only [hX_f, hclampT_id t ht]
  have hXge : ∀ ω, X_g t ω = (charX_g t (proj_g ω), charV_g t (proj_g ω)) := fun ω => by
    simp only [hX_g, hclampT_id t ht]
  have hint_t : Integrable (fun ω => ‖X_f t ω - X_g t ω‖) π₀ :=
    Integrable.mono' hdom_int
      ((hmeas_f t).sub (hmeas_g t)).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hdom t ht ω)
  simpa only [hXfe, hXge] using hint_t

/-- **Shared integrated-coupling core for the Dobrushin stability bound.**

Generalizes the body of `dobrushin_uniqueness_On` over an arbitrary base
coupling measure `π₀` on `Ω` with measurable projections
`proj_f, proj_g : Ω → PhaseSpace d` such that `f 0 = (proj_f)_# π₀` and
`g 0 = (proj_g)_# π₀`.  Trajectory families are `X_μ s ω := Φ_μ s (proj_μ ω)`.
Concludes the integrated trajectory-distance bound

  ∫ ω, ‖Φ_f t (proj_f ω) − Φ_g t (proj_g ω)‖ ∂π₀
    ≤ (∫ ω, ‖proj_f ω − proj_g ω‖ ∂π₀) · exp(2·(max 1 L)·t)

via `integrated_coupling_gronwall_bound` with the moment-free Lipschitz-in-`z`
dominator (`dom ω = e^{KT}(‖proj_f ω‖ + ‖proj_g ω‖) + (K_f + K_g)`, integrable
through the two marginal moments) and the force-estimate-free cross-field bound
(the convolution difference bounded pointwise by `gradW`-Lipschitz, integrated
against `π₀` through the two marginal identities — never forming
`wasserstein1 (f s) (g s)`).

Two consumers:
* `dobrushin_uniqueness_On` — `proj_f = proj_g = id`, `π₀ = f 0 = g 0`, so the
  RHS base integral is `0` and the conclusion collapses to `f t = g t`.
* the mean-field `dobrushin` — `proj_f = fst`, `proj_g = snd`, `π₀` an optimal
  coupling of `(f 0, g 0)`, so the RHS base integral is `W₁(f 0, g 0)` and the
  LHS dominates `W₁(f t, g t)` by the easy direction of Kantorovich–Rubinstein.

Base-generic: the only base-specific work is the two marginal identities
`hmarg_f`/`hmarg_g`; the flow regularity, dominator, and cross-field force bound
are established generically over `π₀`. -/
private theorem dobrushin_integrated_flow_bound_On
    {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (T : ℝ) (hT : 0 < T)
    (π₀ : Measure Ω) [IsProbabilityMeasure π₀]
    (proj_f proj_g : Ω → PhaseSpace d)
    (hproj_f : Measurable proj_f) (hproj_g : Measurable proj_g)
    (charX_f charV_f charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (hinit_f : ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        charX_f 0 z = z.1 ∧ charV_f 0 z = z.2)
    (hflow_f_x : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        HasDerivAt (fun s' => charX_f s' z) (charV_f s z) s)
    (hflow_f_v : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        HasDerivAt (fun s' => charV_f s' z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f s)) (charX_f s z))) s)
    (hpush_f : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f t = Measure.map (fun z => (charX_f t z, charV_f t z)) (f 0))
    (haem_f : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_f s z, charV_f s z)) (f 0))
    (hcontIcc_f : ∀ ω, ContinuousOn (fun s => (charX_f s ω, charV_f s ω)) (Set.Icc 0 T))
    (hinit_g : ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        charX_g 0 z = z.1 ∧ charV_g 0 z = z.2)
    (hflow_g_x : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        HasDerivAt (fun s' => charX_g s' z) (charV_g s z) s)
    (hflow_g_v : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        HasDerivAt (fun s' => charV_g s' z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (g s)) (charX_g s z))) s)
    (hpush_g : ∀ t ∈ Set.Icc (0 : ℝ) T,
        g t = Measure.map (fun z => (charX_g t z, charV_g t z)) (g 0))
    (haem_g : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) (g 0))
    (hcontIcc_g : ∀ ω, ContinuousOn (fun s => (charX_g s ω, charV_g s ω)) (Set.Icc 0 T))
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (g t))
    (hmarg_f : f 0 = Measure.map proj_f π₀)
    (hmarg_g : g 0 = Measure.map proj_g π₀) :
    (∀ s ∈ Set.Icc (0 : ℝ) T,
        Measurable (fun z : PhaseSpace d => (charX_f s z, charV_f s z))) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) T,
        Measurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z))) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun ω => ‖((charX_f t (proj_f ω), charV_f t (proj_f ω)) : PhaseSpace d)
              - (charX_g t (proj_g ω), charV_g t (proj_g ω))‖) π₀ ∧
      (∫ ω, ‖((charX_f t (proj_f ω), charV_f t (proj_f ω)) : PhaseSpace d)
              - (charX_g t (proj_g ω), charV_g t (proj_g ω))‖ ∂π₀)
        ≤ (∫ ω, ‖proj_f ω - proj_g ω‖ ∂π₀)
            * Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t) := by
  -- Probability instances.
  have hf_isProb : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (f t) :=
    fun t ht => (hf_mom t ht).1
  have hg_isProb : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (g t) :=
    fun t ht => (hg_mom t ht).1
  have hf0_prob : IsProbabilityMeasure (f 0) := (hf_mom 0 ⟨le_refl 0, hT.le⟩).1
  have hg0_prob : IsProbabilityMeasure (g 0) := (hg_mom 0 ⟨le_refl 0, hT.le⟩).1
  -- Clamp into [0, T].
  set clampT : ℝ → ℝ := (fun s => max 0 (min s T)) with hclampT_def
  have hclampT_mem : ∀ s, clampT s ∈ Set.Icc (0 : ℝ) T := by
    intro s; simp only [hclampT_def, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s := by
    intro s hs; simp only [hclampT_def, min_eq_left hs.2, max_eq_right hs.1]
  -- Clamped trajectory families over the base `Ω`, read through the projections.
  set X_f : ℝ → Ω → PhaseSpace d :=
    fun s ω => (charX_f (clampT s) (proj_f ω), charV_f (clampT s) (proj_f ω)) with hX_f_def
  set X_g : ℝ → Ω → PhaseSpace d :=
    fun s ω => (charX_g (clampT s) (proj_g ω), charV_g (clampT s) (proj_g ω)) with hX_g_def
  -- Clamped Vlasov vector fields.
  set b_f : ℝ → PhaseSpace d → PhaseSpace d :=
    fun s => vlasovVectorField gradW (fun s => spatialMarginal (f (clampT s))) s
    with hb_f_def
  set b_g : ℝ → PhaseSpace d → PhaseSpace d :=
    fun s => vlasovVectorField gradW (fun s => spatialMarginal (g (clampT s))) s
    with hb_g_def
  -- gradW-kernel integrability on the spatial marginals (window-generic over μ).
  have h_int_helper := dobrushinFlow_marginal_gradW_integrable gradW L hL T
  have h_int_f := h_int_helper f hf_mom
  have h_int_g := h_int_helper g hg_mom
  have hfc_int : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y)) (spatialMarginal (f (clampT s))) :=
    fun s x => h_int_f (clampT s) (hclampT_mem s) x
  have hgc_int : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y)) (spatialMarginal (g (clampT s))) :=
    fun s x => h_int_g (clampT s) (hclampT_mem s) x
  have hfc_isProb : ∀ s, IsProbabilityMeasure (spatialMarginal (f (clampT s))) := by
    intro s; have := hf_isProb (clampT s) (hclampT_mem s)
    exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  have hgc_isProb : ∀ s, IsProbabilityMeasure (spatialMarginal (g (clampT s))) := by
    intro s; have := hg_isProb (clampT s) (hclampT_mem s)
    exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  -- Universal (max 1 L)-Lipschitz of the clamped vector fields.
  have hL_f : ∀ s, LipschitzWith (max 1 L) (b_f s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL
      (fun s => spatialMarginal (f (clampT s))) hfc_int s
  have hL_g : ∀ s, LipschitzWith (max 1 L) (b_g s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL
      (fun s => spatialMarginal (g (clampT s))) hgc_int s
  -- On [0, T] the clamped field coincides with the genuine field.
  have hb_f_id := dobrushinFlow_clamped_field_id gradW T clampT hclampT_id f b_f hb_f_def
  have hb_g_id := dobrushinFlow_clamped_field_id gradW T clampT hclampT_id g b_g hb_g_def
  -- Open-window flow ODE in z (HasDerivWithinAt on `Ici s`, `s ∈ Ioo 0 T`).
  have hderiv_Ioo_f := dobrushinFlow_deriv_Ioo gradW T clampT hclampT_id f
    charX_f charV_f hflow_f_x hflow_f_v
  have hderiv_Ioo_g := dobrushinFlow_deriv_Ioo gradW T clampT hclampT_id g
    charX_g charV_g hflow_g_x hflow_g_v
  have hinit_f' : ∀ z : PhaseSpace d, (charX_f 0 z, charV_f 0 z) = z := by
    intro z; obtain ⟨hx, hv⟩ := hinit_f z (Set.mem_univ z); rw [hx, hv]
  have hinit_g' : ∀ z : PhaseSpace d, (charX_g 0 z, charV_g 0 z) = z := by
    intro z; obtain ⟨hx, hv⟩ := hinit_g z (Set.mem_univ z); rw [hx, hv]
  have hmeas_charf : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX_f s z, charV_f s z)) :=
    charFlow_measurable_via_gronwall_Ioo gradW L hL
      (fun s => spatialMarginal (f (clampT s))) hfc_int charX_f charV_f T hT.le
      hinit_f' hcontIcc_f hderiv_Ioo_f
  have hmeas_charg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) :=
    charFlow_measurable_via_gronwall_Ioo gradW L hL
      (fun s => spatialMarginal (g (clampT s))) hgc_int charX_g charV_g T hT.le
      hinit_g' hcontIcc_g hderiv_Ioo_g
  -- Universal-in-`s` measurability of the clamped flows (clampT s ∈ [0,T]),
  -- composed with the (measurable) projections to land on `Ω`.
  have hmeas_f : ∀ s, Measurable (X_f s) := by
    intro s
    simpa only [hX_f_def, Function.comp_def] using
      (hmeas_charf (clampT s) (hclampT_mem s)).comp hproj_f
  have hmeas_g : ∀ s, Measurable (X_g s) := by
    intro s
    simpa only [hX_g_def, Function.comp_def] using
      (hmeas_charg (clampT s) (hclampT_mem s)).comp hproj_g
  have hclampT_cont : Continuous clampT :=
    continuous_const.max (continuous_id.min continuous_const)
  -- Per-ω continuity of the clamped trajectories on [0, T].
  have hcont_f := dobrushinFlow_clamped_cont T clampT hclampT_cont hclampT_mem
    hclampT_id charX_f charV_f proj_f hcontIcc_f X_f hX_f_def
  have hcont_g := dobrushinFlow_clamped_cont T clampT hclampT_cont hclampT_mem
    hclampT_id charX_g charV_g proj_g hcontIcc_g X_g hX_g_def
  -- Per-ω ODE of the clamped trajectories on Ioo 0 T (HasDerivWithinAt Ioi).
  have hderiv_f := dobrushinFlow_clamped_deriv gradW T clampT hclampT_id f
    charX_f charV_f proj_f hflow_f_x hflow_f_v b_f hb_f_id X_f hX_f_def
  have hderiv_g := dobrushinFlow_clamped_deriv gradW T clampT hclampT_id g
    charX_g charV_g proj_g hflow_g_x hflow_g_v b_g hb_g_id X_g hX_g_def
  -- Moment-free dominator: `dom ω = e^{KT}(‖proj_f ω‖ + ‖proj_g ω‖) + (K_f + K_g)`.
  set K : NNReal := max 1 L with hK_def
  have hK_nn : (0 : ℝ) ≤ ((K : NNReal) : ℝ) := K.coe_nonneg
  set EKT : ℝ := Real.exp (((K : NNReal) : ℝ) * T) with hEKT_def
  have hlip_f : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX_f s z₁, charV_f s z₁) : PhaseSpace d) (charX_f s z₂, charV_f s z₂) ≤
      dist z₁ z₂ * Real.exp (((K : NNReal) : ℝ) * (s - 0)) :=
    charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL
      (fun s => spatialMarginal (f (clampT s))) hfc_int charX_f charV_f T hT.le
      hinit_f' hcontIcc_f hderiv_Ioo_f
  have hlip_g : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX_g s z₁, charV_g s z₁) : PhaseSpace d) (charX_g s z₂, charV_g s z₂) ≤
      dist z₁ z₂ * Real.exp (((K : NNReal) : ℝ) * (s - 0)) :=
    charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL
      (fun s => spatialMarginal (g (clampT s))) hgc_int charX_g charV_g T hT.le
      hinit_g' hcontIcc_g hderiv_Ioo_g
  obtain ⟨K_f, hK_f_nn, hK_f⟩ :=
    dobrushinFlow_origin_trajectory_bound T charX_f charV_f (hcontIcc_f 0)
  obtain ⟨K_g, hK_g_nn, hK_g⟩ :=
    dobrushinFlow_origin_trajectory_bound T charX_g charV_g (hcontIcc_g 0)
  have hfnorm : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω : PhaseSpace d,
      ‖(charX_f s ω, charV_f s ω)‖ ≤ EKT * ‖ω‖ + K_f := by
    rw [hEKT_def]
    exact dobrushinFlow_flow_norm_bound T K charX_f charV_f K_f hlip_f hK_f
  have hgnorm : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω : PhaseSpace d,
      ‖(charX_g s ω, charV_g s ω)‖ ≤ EKT * ‖ω‖ + K_g := by
    rw [hEKT_def]
    exact dobrushinFlow_flow_norm_bound T K charX_g charV_g K_g hlip_g hK_g
  set dom : Ω → ℝ := fun ω => EKT * ‖proj_f ω‖ + EKT * ‖proj_g ω‖ + (K_f + K_g) with hdom_def
  have hmom_f : Integrable (fun ω : Ω => ‖proj_f ω‖) π₀ :=
    dobrushinFlow_proj_moment π₀ proj_f hproj_f (f 0) hmarg_f
      (hf_mom 0 ⟨le_refl 0, hT.le⟩).2
  have hmom_g : Integrable (fun ω : Ω => ‖proj_g ω‖) π₀ :=
    dobrushinFlow_proj_moment π₀ proj_g hproj_g (g 0) hmarg_g
      (hg_mom 0 ⟨le_refl 0, hT.le⟩).2
  have hdom_int : Integrable dom π₀ := by
    simp only [hdom_def]
    exact ((hmom_f.const_mul EKT).add (hmom_g.const_mul EKT)).add (integrable_const _)
  have hdom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, ‖X_f s ω - X_g s ω‖ ≤ dom ω := by
    simp only [hdom_def]
    exact dobrushinFlow_dominator_bound T clampT hclampT_id charX_f charV_f
      charX_g charV_g proj_f proj_g EKT K_f K_g hfnorm hgnorm X_f X_g hX_f_def hX_g_def
  -- Cross-field bound ε and its self-reference to Q (over the base π₀).
  set Q : ℝ → ℝ := fun s => ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀ with hQ_def
  set ε : ℝ → ℝ := fun s => ((max 1 L : NNReal) : ℝ) * Q s with hε_def
  have hQ_cont : ContinuousOn Q (Set.Icc 0 T) := by
    have hQglob : Continuous Q := by
      simp only [hQ_def]
      exact dobrushinFlow_Q_continuous T clampT hclampT_cont hclampT_mem hclampT_id
        π₀ charX_f charV_f charX_g charV_g proj_f proj_g hcontIcc_f hcontIcc_g
        X_f X_g hX_f_def hX_g_def hmeas_f hmeas_g dom hdom_int hdom
    exact hQglob.continuousOn
  have hε_int : IntervalIntegrable ε MeasureTheory.volume 0 T := by
    have hεcont : ContinuousOn ε (Set.Icc 0 T) := by
      simp only [hε_def]; exact continuousOn_const.mul hQ_cont
    exact hεcont.intervalIntegrable_of_Icc hT.le
  have hε_nn : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ ε s := by
    intro s _; simp only [hε_def]
    exact mul_nonneg (le_trans zero_le_one
      (by rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_left _ _))
      (integral_nonneg (fun ω => norm_nonneg _))
  have h_self : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ε s ≤ ((max 1 L : NNReal) : ℝ) * ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀ := by
    intro s _; exact le_refl _
  have hint : ∀ ω, IntervalIntegrable
      (fun s => b_f s (X_f s ω) - b_g s (X_g s ω)) MeasureTheory.volume 0 T := by
    intro ω
    have hcf : Continuous (fun s => b_f s (X_f s ω)) := by
      have h := dobrushinFlow_field_continuous gradW L hL T K clampT hclampT_mem
        charX_f charV_f f (f 0) K_f b_f
        (fun s z => (charX_f (clampT s) z, charV_f (clampT s) z)) hb_f_def rfl
        (fun z => (hcontIcc_f z).comp_continuous hclampT_cont (fun s => hclampT_mem s))
        hpush_f haem_f hf0_prob (hf_mom 0 ⟨le_refl 0, hT.le⟩).2 hK_f hlip_f (proj_f ω)
      simpa only [hX_f_def] using h
    have hcg : Continuous (fun s => b_g s (X_g s ω)) := by
      have h := dobrushinFlow_field_continuous gradW L hL T K clampT hclampT_mem
        charX_g charV_g g (g 0) K_g b_g
        (fun s z => (charX_g (clampT s) z, charV_g (clampT s) z)) hb_g_def rfl
        (fun z => (hcontIcc_g z).comp_continuous hclampT_cont (fun s => hclampT_mem s))
        hpush_g haem_g hg0_prob (hg_mom 0 ⟨le_refl 0, hT.le⟩).2 hK_g hlip_g (proj_g ω)
      simpa only [hX_g_def] using h
    exact ((hcf.sub hcg).continuousOn).intervalIntegrable_of_Icc hT.le
  -- Cross-field bound: convolution difference bounded pointwise by the coupled
  -- trajectory distance, integrated against `π₀` through the two marginals.
  have h_diff : ∀ ω, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖b_f s (X_g s ω) - b_g s (X_g s ω)‖ ≤ ε s := by
    simp only [hε_def, hQ_def]
    exact dobrushinFlow_cross_field_bound gradW L hL T clampT hclampT_id π₀ f g
      charX_f charV_f charX_g charV_g proj_f proj_g hproj_f hproj_g
      hpush_f haem_f hpush_g haem_g hf_mom hg_mom hmarg_f hmarg_g
      h_int_f h_int_g hmeas_charf hmeas_charg X_f X_g hX_f_def hX_g_def
      b_f b_g hb_f_id hb_g_id hmeas_f hmeas_g dom hdom_int hdom
  -- Apply the integrated collapse core.
  have hcore := integrated_coupling_gronwall_bound π₀ X_f X_g b_f b_g
    (max 1 L) T hT.le hL_f hcont_f hcont_g hderiv_f hderiv_g hint
    hmeas_f hmeas_g dom hdom_int hdom ε hε_int hε_nn h_diff h_self
  refine ⟨hmeas_charf, hmeas_charg, ?_⟩
  exact dobrushinFlow_conclusion_transfer T hT clampT hclampT_id π₀ L
    charX_f charV_f charX_g charV_g proj_f proj_g hinit_f' hinit_g'
    X_f X_g hX_f_def hX_g_def hmeas_f hmeas_g dom hdom_int hdom hcore

/-- **Localized Dobrushin uniqueness on `[0, T]`** for two
`IsLagrangianVlasovSolutionOn` solutions with the same initial data and
finite first moments.

**Why the Lagrangian class**: the weak `IsVlasovSolutionOn` class cannot
soundly carry this conclusion:
the Gronwall step (`wassersteinGronwallCoupling_gronwall_le`) demands
`ContinuousOn (Icc 0 T)` of `t ↦ (W₁ (f t) (g t)).toReal` — *closed* interval
— but `IsVlasovSolutionOn` constrains the weak PDE only on the *open*
`Ioo 0 T`, leaving the endpoint values `f T`, `g T` free (a weak solution may
jump at `t = T`).  So closed-window W₁-continuity is not a consequence of the
weak class.  Realigning to `IsLagrangianVlasovSolutionOn` fixes this: the
flow witness supplies `f t = (charX t)_# (f 0)` on the closed `Icc 0 T` plus
boundary flow regularity, pinning the endpoints.  (Uniqueness over the weak
class would need the DiPerna-Lions superposition principle, out of scope.)
The caller `vlasovWellPosedness_uniqueness` already holds the Lagrangian
witness, so this is zero-cost upstream.

**Closure path (via the integrated-coupling core)**:
the proof wires through `integrated_coupling_gronwall_bound` instead of the
W₁-continuity + right-derivative-liminf + Gronwall chain.  Set
`μ₀ := f 0 = g 0` and let `Φ_f, Φ_g` be the (clamped)
characteristic flows.  The core bounds the integrated trajectory distance
`Q t := ∫ ω, ‖Φ_f t ω − Φ_g t ω‖ ∂μ₀` by `Q 0 · exp(2 (max 1 L) t)`; since the
flows start at the identity, `Q 0 = 0`, so `Q t ≤ 0`.  Hence `Φ_f t = Φ_g t`
μ₀-a.e., and `f t = (Φ_f t)_# μ₀ = (Φ_g t)_# μ₀ = g t` by `Measure.map_congr`.

The crux input is the cross-field bound `h_diff`, established directly from the
pushforward identity `spatialMarginal (f s) = (charX_f s)_# μ₀` + `gradW`
Lipschitz under the integral (two `integral_map` steps) — it never forms
`wasserstein1 (f s) (g s)`.

The measurability and the dominator route through the *open-interval* helpers
(`charFlow_measurable_via_gronwall_Ioo` /
`charFlow_lipschitzInZ_via_gronwall_Ioo`), which consume only the witness ODE
on `Ioo 0 T`:
* the `s = 0` right-derivatives (`hderivIco_f`/`hderivIco_g`) are no longer
  needed — the `Ioo`-only flow ODE (`hderiv_Ioo_f`/`hderiv_Ioo_g`) suffices;
* the uniform-in-`s` first-moment envelope (`Mf`/`Mg`) and
  `flow_distance_growth_bound_on` are replaced by a moment-free dominator
  `dom ω = 2 e^{KT} ‖ω‖ + (K_f + K_g)` built from the flow's Lipschitz-in-`z`
  bound + compactness of the origin trajectory on `[0, T]`; it uses ONLY
  `f 0`'s initial first moment;
* the per-`ω` interval-integrability (`hint`) is closed by global continuity in
  `s` of each clamped field (velocity slot continuous; force slot a
  pushforward integral, continuous via moment-free DCT). -/
private theorem dobrushin_uniqueness_On
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (T : ℝ) (hT : 0 < T)
    (hf : IsLagrangianVlasovSolutionOn gradW f T)
    (hg : IsLagrangianVlasovSolutionOn gradW g T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (g t))
    (hfg0 : f 0 = g 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, f t = g t := by
  -- Routed through the shared `dobrushin_integrated_flow_bound_On` core with
  -- the **diagonal** coupling `π₀ = f 0` and `proj_f = proj_g = id`.
  -- Then the RHS base integral `∫ ‖id ω − id ω‖ = 0`, so the integrated bound
  -- forces `Φ_f t = Φ_g t` `f 0`-a.e., hence
  -- `f t = (Φ_f t)_# (f 0) = (Φ_g t)_# (f 0) = g t`.
  have hf0_prob : IsProbabilityMeasure (f 0) := (hf_mom 0 ⟨le_refl 0, hT.le⟩).1
  obtain ⟨_, charX_f, charV_f, hflow_f, hpush_f, haem_f, hcontIcc_f⟩ := hf
  obtain ⟨_, charX_g, charV_g, hflow_g, hpush_g, haem_g, hcontIcc_g⟩ := hg
  obtain ⟨hinit_f, hflow_f_x, hflow_f_v⟩ := hflow_f
  obtain ⟨hinit_g, hflow_g_x, hflow_g_v⟩ := hflow_g
  have hmarg_f : f 0 = Measure.map id (f 0) := by rw [Measure.map_id]
  have hmarg_g : g 0 = Measure.map id (f 0) := by rw [Measure.map_id, hfg0]
  have hcore := dobrushin_integrated_flow_bound_On gradW L hL f g T hT
    (f 0) id id measurable_id measurable_id
    charX_f charV_f charX_g charV_g
    hinit_f hflow_f_x hflow_f_v hpush_f haem_f hcontIcc_f
    hinit_g hflow_g_x hflow_g_v hpush_g haem_g hcontIcc_g
    hf_mom hg_mom hmarg_f hmarg_g
  obtain ⟨_, _, hmain⟩ := hcore
  intro t ht
  obtain ⟨hint_t, hbound⟩ := hmain t ht
  have hrhs0 : (∫ ω, ‖(id ω : PhaseSpace d) - id ω‖ ∂(f 0)) = 0 := by
    simp only [id_eq, sub_self, norm_zero, integral_zero]
  rw [hrhs0, zero_mul] at hbound
  simp only [id_eq] at hint_t hbound
  have hnn : 0 ≤ ∫ ω, ‖((charX_f t ω, charV_f t ω) : PhaseSpace d)
      - (charX_g t ω, charV_g t ω)‖ ∂(f 0) :=
    integral_nonneg (fun ω => norm_nonneg _)
  have hz : (∫ ω, ‖((charX_f t ω, charV_f t ω) : PhaseSpace d)
      - (charX_g t ω, charV_g t ω)‖ ∂(f 0)) = 0 := le_antisymm hbound hnn
  have hae_zero : (fun ω => ‖((charX_f t ω, charV_f t ω) : PhaseSpace d)
      - (charX_g t ω, charV_g t ω)‖) =ᵐ[f 0] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => norm_nonneg _) hint_t).mp hz
  have hflow_ae : (fun ω => ((charX_f t ω, charV_f t ω) : PhaseSpace d))
      =ᵐ[f 0] (fun ω => (charX_g t ω, charV_g t ω)) := by
    filter_upwards [hae_zero] with ω hω
    have hnz : ‖((charX_f t ω, charV_f t ω) : PhaseSpace d)
        - (charX_g t ω, charV_g t ω)‖ = 0 := hω
    exact sub_eq_zero.mp (norm_eq_zero.mp hnz)
  have hpush_g' : g t = Measure.map (fun z => (charX_g t z, charV_g t z)) (f 0) := by
    rw [hpush_g t ht, hfg0]
  rw [hpush_f t ht, hpush_g']
  exact Measure.map_congr hflow_ae

/-- **Mean-field Dobrushin stability on the window `[0, T]`**, in the *primal
coupling* metric.

Concludes `W₁(f t, g t) ≤ exp(2·(max 1 L)·t) · wasserstein1Coupling (f 0, g 0)`
— the dual `W₁` on the LHS, the *coupling-inf* metric on the RHS (= Dobrushin's
metric ρbar).  Proved **without Foundation B**: for *every* coupling `π` of
`(f 0, g 0)` the shared `dobrushin_integrated_flow_bound_On` core (coupling-
generic in `(π, proj_f, proj_g)`) gives
  `W₁(f t, g t) ≤ ∫⁻ edist d(pushforward π) ≤ exp(…) · ∫⁻ edist z.1 z.2 ∂π`,
the first step by the easy direction of Kantorovich–Rubinstein
(`wasserstein1_pushforward_le_iInf`).  Taking `le_iInf` over couplings (the
constant `exp(…) ∈ (0,∞)` pulled through via `ENNReal.div_le_iff_le_mul`) yields
the coupling-metric RHS — **no optimal coupling / attainment needed** (cf.
Dobrushin 1979, eq. 6.8, ε-optimal couplings).  The all-dual form is recovered
downstream (`dobrushin`) via the single labelled `wasserstein1_eq_coupling`
duality bridge — the project's lone Foundation-B use.

Force-estimate-free: never forms a force estimate, never touches the
`W₁`-continuity / right-derivative route. -/
private theorem dobrushin_meanfield_On
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (T : ℝ) (hT : 0 < T)
    (hf : IsLagrangianVlasovSolutionOn gradW f T)
    (hg : IsLagrangianVlasovSolutionOn gradW g T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (g t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      wasserstein1 (f t) (g t)
        ≤ ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t))
            * wasserstein1Coupling (f 0) (g 0) := by
  have hf0_prob : IsProbabilityMeasure (f 0) := (hf_mom 0 ⟨le_refl 0, hT.le⟩).1
  have hg0_prob : IsProbabilityMeasure (g 0) := (hg_mom 0 ⟨le_refl 0, hT.le⟩).1
  obtain ⟨_, charX_f, charV_f, hflow_f, hpush_f, haem_f, hcontIcc_f⟩ := hf
  obtain ⟨_, charX_g, charV_g, hflow_g, hpush_g, haem_g, hcontIcc_g⟩ := hg
  obtain ⟨hinit_f, hflow_f_x, hflow_f_v⟩ := hflow_f
  obtain ⟨hinit_g, hflow_g_x, hflow_g_v⟩ := hflow_g
  intro t ht
  have hft_prob : IsProbabilityMeasure (f t) := (hf_mom t ht).1
  have hgt_prob : IsProbabilityMeasure (g t) := (hg_mom t ht).1
  have hft : Measure.map (fun z => (charX_f t z, charV_f t z)) (f 0) = f t :=
    (hpush_f t ht).symm
  have hgt : Measure.map (fun z => (charX_g t z, charV_g t z)) (g 0) = g t :=
    (hpush_g t ht).symm
  have hft_fm : Integrable (fun y => dist y (0 : PhaseSpace d)) (f t) := by
    simpa only [dist_zero_right] using (hf_mom t ht).2
  have hgt_fm : Integrable (fun y => dist y (0 : PhaseSpace d)) (g t) := by
    simpa only [dist_zero_right] using (hg_mom t ht).2
  have hc_ne0 :
      ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hc_neTop :
      ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have h_per : ∀ (π : Measure (PhaseSpace d × PhaseSpace d)),
      IsCoupling π (f 0) (g 0) →
      wasserstein1 (f t) (g t)
        ≤ ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t))
            * ∫⁻ z, edist z.1 z.2 ∂π := by
    intro π hπ
    have hπ_prob : IsProbabilityMeasure π := by
      constructor
      have hmap : (Measure.map Prod.fst π) Set.univ = (1 : ENNReal) := by
        rw [hπ.1, measure_univ]
      rwa [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at hmap
    have hmarg_f : f 0 = Measure.map Prod.fst π := hπ.1.symm
    have hmarg_g : g 0 = Measure.map Prod.snd π := hπ.2.symm
    obtain ⟨hmeas_charf, hmeas_charg, hmain⟩ :=
      dobrushin_integrated_flow_bound_On gradW L hL f g T hT
        π Prod.fst Prod.snd measurable_fst measurable_snd
        charX_f charV_f charX_g charV_g
        hinit_f hflow_f_x hflow_f_v hpush_f haem_f hcontIcc_f
        hinit_g hflow_g_x hflow_g_v hpush_g haem_g hcontIcc_g
        hf_mom hg_mom hmarg_f hmarg_g
    obtain ⟨hint_t, hbound⟩ := hmain t ht
    have hmom_fst : Integrable (fun ω : PhaseSpace d × PhaseSpace d => ‖ω.1‖) π := by
      have hm : Integrable (fun z : PhaseSpace d => ‖z‖) (Measure.map Prod.fst π) := by
        rw [← hmarg_f]; exact (hf_mom 0 ⟨le_refl 0, hT.le⟩).2
      exact (integrable_map_measure continuous_norm.aestronglyMeasurable
        measurable_fst.aemeasurable).mp hm
    have hmom_snd : Integrable (fun ω : PhaseSpace d × PhaseSpace d => ‖ω.2‖) π := by
      have hm : Integrable (fun z : PhaseSpace d => ‖z‖) (Measure.map Prod.snd π) := by
        rw [← hmarg_g]; exact (hg_mom 0 ⟨le_refl 0, hT.le⟩).2
      exact (integrable_map_measure continuous_norm.aestronglyMeasurable
        measurable_snd.aemeasurable).mp hm
    have hbase_int : Integrable (fun ω : PhaseSpace d × PhaseSpace d => ‖ω.1 - ω.2‖) π :=
      Integrable.mono' (hmom_fst.add hmom_snd)
        ((measurable_fst.sub measurable_snd).norm.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_sub_le _ _)
    have h_push := wasserstein1_pushforward_le_iInf
      (fun z => (charX_f t z, charV_f t z)) (fun z => (charX_g t z, charV_g t z))
      (hmeas_charf t ht) (hmeas_charg t ht) (f 0) (g 0) 0
      (by rw [hft]; infer_instance) (by rw [hgt]; infer_instance)
      (by rw [hft]; exact hft_fm) (by rw [hgt]; exact hgt_fm)
    rw [hft, hgt] at h_push
    have h_iInf_le :
        (⨅ (π' : Measure (PhaseSpace d × PhaseSpace d)) (_ : IsCoupling π' (f 0) (g 0)),
          ∫⁻ z, edist (charX_f t z.1, charV_f t z.1) (charX_g t z.2, charV_g t z.2) ∂π')
          ≤ ∫⁻ z, edist (charX_f t z.1, charV_f t z.1) (charX_g t z.2, charV_g t z.2) ∂π :=
      iInf_le_of_le π (iInf_le _ hπ)
    have hWt_lint : wasserstein1 (f t) (g t)
        ≤ ∫⁻ z, edist (charX_f t z.1, charV_f t z.1) (charX_g t z.2, charV_g t z.2) ∂π :=
      le_trans h_push h_iInf_le
    have hlint_eq :
        (∫⁻ z, edist (charX_f t z.1, charV_f t z.1) (charX_g t z.2, charV_g t z.2) ∂π)
          = ENNReal.ofReal (∫ ω, ‖((charX_f t ω.1, charV_f t ω.1) : PhaseSpace d)
              - (charX_g t ω.2, charV_g t ω.2)‖ ∂π) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint_t
        (Filter.Eventually.of_forall fun ω => norm_nonneg _)]
      refine lintegral_congr fun z => ?_
      rw [edist_dist, dist_eq_norm]
    rw [hlint_eq] at hWt_lint
    refine le_trans hWt_lint ?_
    calc ENNReal.ofReal (∫ ω, ‖((charX_f t ω.1, charV_f t ω.1) : PhaseSpace d)
              - (charX_g t ω.2, charV_g t ω.2)‖ ∂π)
        ≤ ENNReal.ofReal ((∫ ω, ‖ω.1 - ω.2‖ ∂π)
            * Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) :=
          ENNReal.ofReal_le_ofReal hbound
      _ = ENNReal.ofReal (∫ ω, ‖ω.1 - ω.2‖ ∂π)
            * ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) :=
          ENNReal.ofReal_mul (integral_nonneg fun _ => norm_nonneg _)
      _ = ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t))
            * ENNReal.ofReal (∫ ω, ‖ω.1 - ω.2‖ ∂π) := mul_comm _ _
      _ = ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t))
            * ∫⁻ z, edist z.1 z.2 ∂π := by
          rw [ofReal_integral_eq_lintegral_ofReal hbase_int
            (Filter.Eventually.of_forall fun ω => norm_nonneg _)]
          refine congrArg
            (fun w => ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) * w) ?_
          refine lintegral_congr fun z => ?_
          rw [edist_dist, dist_eq_norm]
  -- Take the iInf over couplings of (f 0, g 0).
  rw [show wasserstein1Coupling (f 0) (g 0)
        = ⨅ (π : Measure (PhaseSpace d × PhaseSpace d)) (_ : IsCoupling π (f 0) (g 0)),
            ∫⁻ z, edist z.1 z.2 ∂π from rfl, mul_comm,
    ← ENNReal.div_le_iff_le_mul (Or.inl hc_ne0) (Or.inl hc_neTop)]
  refine le_iInf fun π => le_iInf fun hπ => ?_
  rw [ENNReal.div_le_iff_le_mul (Or.inl hc_ne0) (Or.inl hc_neTop), mul_comm]
  exact h_per π hπ

/-- **Uniqueness on the local window**.

Two `IsLagrangianVlasovSolutionOn`s with the same initial data agree on
`[0, T_target]`.

**Proof** (closed via Dobrushin uniqueness composition):

1. Extract `IsVlasovSolutionOn` from each `IsLagrangianVlasovSolutionOn`.
2. Note `f 0 = f₀ = g 0` from the init hypotheses.
3. Apply `dobrushin_uniqueness_On` (localized Dobrushin uniqueness, the
   private helper above) to conclude `f t = g t`. -/
theorem vlasovWellPosedness_uniqueness
    {d : ℕ}
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d))
    (_hf₀ : HasFiniteFirstMoment f₀)
    {T_target : ℝ} (hT_target : 0 < T_target)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf_init : f 0 = f₀) (hg_init : g 0 = f₀)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T_target, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T_target, HasFiniteFirstMoment (g t))
    (hf_lag : IsLagrangianVlasovSolutionOn gradW f T_target)
    (hg_lag : IsLagrangianVlasovSolutionOn gradW g T_target) :
    ∀ t ∈ Set.Icc (0 : ℝ) T_target, f t = g t := by
  -- The two solutions share the same initial datum f₀
  have hfg0 : f 0 = g 0 := hf_init.trans hg_init.symm
  -- Apply the localized Dobrushin uniqueness (Helper above).  Pass the full
  -- Lagrangian witness directly (post-realignment, item 3 is over the
  -- Lagrangian-On class for soundness — see its docstring).
  exact dobrushin_uniqueness_On gradW L hL f g T_target hT_target
    hf_lag hg_lag hf_mom hg_mom hfg0

/-! ## Universal-in-`t` bridge to `IsLagrangianVlasovSolution` -/
-- Combines `vlasovWellPosedness_forward` (forward iteration) +
-- `vlasovWellPosedness_uniqueness` into a single universal-in-`t`
-- existence theorem.  The universal `f` is constructed as the colimit of
-- the per-`T_target` solutions, well-defined by the uniqueness agreement on
-- overlaps.

/-- `IsLagrangianVlasovSolutionOn` is antitone in the window length: a Lagrangian
solution on `[0, T]` restricts to one on any `[0, T'] ⊆ [0, T]`. -/
lemma IsLagrangianVlasovSolutionOn.mono_window
    {d : ℕ}
    {gradW : PhysSpace d → PhysSpace d} {g : ℝ → Measure (PhaseSpace d)}
    {T T' : ℝ} (h : IsLagrangianVlasovSolutionOn gradW g T) (hTT' : T' ≤ T) :
    IsLagrangianVlasovSolutionOn gradW g T' := by
  obtain ⟨h_sol, charX, charV, h_flow, h_push, h_aemeas, h_cont⟩ := h
  refine ⟨?_, charX, charV, ?_, ?_, ?_⟩
  · intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ s hs
    exact h_sol φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ s
      ⟨hs.1, lt_of_lt_of_le hs.2 hTT'⟩
  · exact h_flow.mono (Set.Ioo_subset_Ioo le_rfl hTT') Set.Subset.rfl
  · intro s hs; exact h_push s ⟨hs.1, le_trans hs.2 hTT'⟩
  · refine ⟨?_, ?_⟩
    · intro s hs; exact h_aemeas s ⟨hs.1, le_trans hs.2 hTT'⟩
    · intro z; exact (h_cont z).mono (fun u hu => ⟨hu.1, le_trans hu.2 hTT'⟩)

/-- Continuity (within a window, at a point) of `t ↦ ∫ g d(fcur t)` for a curve
represented on the window as a flow pushforward: dominated convergence against
the fixed `f₀`, then transfer along the representation. -/
lemma integral_continuousWithinAt_of_flow_rep
    {d : ℕ}
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (fcur : ℝ → Measure (PhaseSpace d))
    (Φ : ℝ → PhaseSpace d → PhaseSpace d)
    (g : PhaseSpace d → ℝ) (hg_cont : Continuous g) (C : ℝ)
    (hgC : ∀ z : PhaseSpace d, ‖g z‖ ≤ C)
    (B t₀ : ℝ) (ht₀B : t₀ ∈ Set.Icc (0 : ℝ) B)
    (h_integral_eq : ∀ t ∈ Set.Icc (0 : ℝ) B,
      ∫ z, g z ∂(fcur t) = ∫ z, g (Φ t z) ∂f₀)
    (h_aesm : ∀ t ∈ Set.Icc (0 : ℝ) B,
      MeasureTheory.AEStronglyMeasurable (fun z => g (Φ t z)) f₀)
    (h_ptcont : ∀ z, ContinuousWithinAt (fun t => Φ t z) (Set.Icc (0 : ℝ) B) t₀) :
    ContinuousWithinAt (fun t => ∫ z, g z ∂(fcur t)) (Set.Icc (0 : ℝ) B) t₀ := by
  have h_cont_flow : ContinuousWithinAt
      (fun t => ∫ z, g (Φ t z) ∂f₀) (Set.Icc (0 : ℝ) B) t₀ := by
    apply continuousWithinAt_of_dominated (μ := f₀) (bound := fun _ => C)
    · exact Filter.Eventually.mono self_mem_nhdsWithin fun t ht => h_aesm t ht
    · apply Filter.Eventually.mono self_mem_nhdsWithin; intro t _
      exact Filter.Eventually.of_forall fun z => hgC _
    · exact MeasureTheory.integrable_const C
    · exact Filter.Eventually.of_forall fun z =>
        hg_cont.continuousAt.comp_continuousWithinAt (h_ptcont z)
  exact h_cont_flow.congr_of_eventuallyEq
    (Filter.Eventually.mono self_mem_nhdsWithin fun t ht => h_integral_eq t ht)
    (h_integral_eq t₀ ht₀B)

/-- **Universal-in-`t` (forward) existence — bridge to the marquee form**.

For any Lipschitz constant `L > 0`, produces a single `f : ℝ → Measure
(PhaseSpace d)` satisfying `IsLagrangianVlasovSolutionOn` for every
`T_target > 0`, with finite first moment and narrow continuity on `Ici 0`.
Composes `vlasovWellPosedness_forward` (forward iteration) +
`vlasovWellPosedness_uniqueness` (agreement on overlaps).

**Proof strategy**:

1. Apply `vlasovWellPosedness_forward` with `T_target := n` for each
   `n : ℕ`, getting per-`n` solutions `f_n : ℝ → Measure (PhaseSpace d)`.

2. By `vlasovWellPosedness_uniqueness`, `f_n` and `f_m` agree
   on `Icc 0 (min n m)`.

3. Define `f t := f_{⌈t⌉ + 1} t` for `t ≥ 0`.  By step 2, this is
   well-defined on `t ≥ 0`.

4. `IsLagrangianVlasovSolutionOn gradW f T_target` for each `T_target`:
   composes from the per-window solutions.

5. Narrow continuity on `Ici 0`: standard DCT using moment bound + flow
   growth.

The problem is a forward Cauchy problem; backward time is not on the
critical path. -/
theorem vlasovWellPosedness_universal_existence
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (hL_pos : (0 : ℝ) < L)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀) :
    ∃ f : ℝ → Measure (PhaseSpace d),
      f 0 = f₀ ∧
      -- Forward-only conjuncts: the universal-in-t Vlasov well-posedness is
      -- a forward Cauchy problem; backward time is not on the critical path.
      (∀ t ∈ Set.Ici (0 : ℝ), HasFiniteFirstMoment (f t)) ∧
      (∀ T_target : ℝ, 0 < T_target →
        IsLagrangianVlasovSolutionOn gradW f T_target) ∧
      (∀ (g : PhaseSpace d → ℝ), Continuous g → Bornology.IsBounded (Set.range g) →
        ContinuousOn (fun t => ∫ z, g z ∂f t) (Set.Ici 0)) := by
  -- Step 1. For each n : ℕ, choose a solution on [0, n+1] via forward iteration.
  -- h_fwd_exists n gives ∃ g, g 0 = f₀ ∧ (moment on [0,n+1]) ∧ IsLagrangianVlasovSolutionOn n+1
  have h_fwd_exists : ∀ n : ℕ,
      ∃ g : ℝ → Measure (PhaseSpace d),
        g 0 = f₀ ∧
        (∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1), HasFiniteFirstMoment (g t)) ∧
        IsLagrangianVlasovSolutionOn gradW g ((n : ℝ) + 1) := by
    intro n
    exact vlasovWellPosedness_forward W gradW hgradW L hL hL_pos f₀ hf₀
      (by positivity : (0 : ℝ) < (n : ℝ) + 1)
  -- Step 2. Pick canonical per-n solutions via Classical.choice.
  let sol : ℕ → ℝ → Measure (PhaseSpace d) :=
    fun n => Classical.choose (h_fwd_exists n)
  have h_sol_init : ∀ n : ℕ, sol n 0 = f₀ :=
    fun n => (Classical.choose_spec (h_fwd_exists n)).1
  have h_sol_mom : ∀ n : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1),
      HasFiniteFirstMoment (sol n t) :=
    fun n => (Classical.choose_spec (h_fwd_exists n)).2.1
  have h_sol_lag : ∀ n : ℕ, IsLagrangianVlasovSolutionOn gradW (sol n) ((n : ℝ) + 1) :=
    fun n => (Classical.choose_spec (h_fwd_exists n)).2.2
  -- Step 3. Agreement on overlaps via uniqueness.
  -- Any two per-n solutions agree on [0, n+1]: restrict sol m from [0, m+1]
  -- to [0, n+1] via inline monotonicity, then apply vlasovWellPosedness_uniqueness.
  have h_agree : ∀ n m : ℕ, n ≤ m →
      ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1), sol n t = sol m t := by
    intro n m hnm t ht
    -- Cast inequality: (n : ℝ) + 1 ≤ (m : ℝ) + 1
    have hnm_cast : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
      linarith
    -- Restrict sol m from [0, m+1] to [0, n+1] via window monotonicity
    have h_sol_m_on_n : IsLagrangianVlasovSolutionOn gradW (sol m) ((n : ℝ) + 1) :=
      (h_sol_lag m).mono_window hnm_cast
    -- Apply vlasovWellPosedness_uniqueness on window [0, n+1]
    exact vlasovWellPosedness_uniqueness W gradW hgradW L hL f₀ hf₀
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : (0 : ℝ) < (n : ℝ) + 1)
      (sol n) (sol m) (h_sol_init n) (h_sol_init m)
      (h_sol_mom n)
      (fun s hs => h_sol_mom m s ⟨hs.1, le_trans hs.2 hnm_cast⟩)
      (h_sol_lag n) h_sol_m_on_n
      t ht
  -- Step 4. Define the universal-in-forward-time solution.
  -- For t ≥ 0: use sol ⌈t⌉₊ at t.  For t < 0: f₀ (unconstrained by the
  -- forward-only statement; the claims below only quantify over t ≥ 0).
  let f : ℝ → Measure (PhaseSpace d) :=
    fun t => if 0 ≤ t then sol (⌈t⌉₊) t else f₀
  -- Step 5. Prove the four conjuncts.
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  -- Conjunct 1: f 0 = f₀
  · change (if (0 : ℝ) ≤ 0 then sol ⌈(0 : ℝ)⌉₊ 0 else f₀) = f₀
    simp [h_sol_init 0]
  -- Conjunct 2: ∀ t ∈ Ici 0, HasFiniteFirstMoment (f t)
  · intro t ht
    have ht_nn : (0 : ℝ) ≤ t := ht
    change HasFiniteFirstMoment (if 0 ≤ t then sol ⌈t⌉₊ t else f₀)
    simp only [ht_nn, ↓reduceIte]
    apply h_sol_mom (⌈t⌉₊) t
    refine ⟨ht_nn, ?_⟩
    exact le_trans (Nat.le_ceil t) (by linarith)
  -- Conjunct 3: ∀ T_target > 0, IsLagrangianVlasovSolutionOn gradW f T_target
  · -- For T_target > 0, let N = ⌈T_target⌉₊.  The solution sol N exists on [0, N+1]
    -- with N+1 ≥ T_target.  Agreement h_agree gives f t = sol N t on [0, T_target].
    -- Restrict sol N's IsLagrangianVlasovSolutionOn to [0, T_target] and convert to f.
    intro T_target hT_target_pos
    set N := ⌈T_target⌉₊ with hN_def
    have hT_le_N : T_target ≤ (N : ℝ) := Nat.le_ceil T_target
    -- Agreement: f t = sol N t for t ∈ [0, T_target]
    have h_agree_fN : ∀ t ∈ Set.Icc (0 : ℝ) T_target, f t = sol N t := by
      intro t ht
      have ht_nn : (0 : ℝ) ≤ t := ht.1
      change (if 0 ≤ t then sol ⌈t⌉₊ t else f₀) = sol N t
      simp only [ht_nn, ↓reduceIte]
      exact h_agree ⌈t⌉₊ N (Nat.ceil_mono ht.2) t
        ⟨ht.1, le_trans (Nat.le_ceil t) (by linarith)⟩
    -- Extract components from h_sol_lag N
    obtain ⟨h_pde_N, charX_N, charV_N, h_flow_N, h_push_N, h_aemeas_N, h_boundary_N⟩ :=
      h_sol_lag N
    -- Compute f 0 = sol N 0
    have h_f0_solN : f 0 = sol N 0 :=
      h_agree_fN 0 ⟨le_refl 0, hT_target_pos.le⟩
    refine ⟨?_, charX_N, charV_N, ?_, ?_, ?_⟩
    · -- IsVlasovSolutionOn gradW f T_target: for each t ∈ Ioo 0 T_target,
      -- f and sol N agree near t, so HasDerivAt transfers via EventuallyEq.
      intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t ht
      have ht_lt_N1 : t < (N : ℝ) + 1 := lt_of_lt_of_le ht.2 (by linarith)
      have h_from_N := h_pde_N φ hφ_smooth hφ_compact gradXφ gradVφ
        hgradXφ hgradVφ t ⟨ht.1, ht_lt_N1⟩
      -- The functions fun s => ∫ φ ∂(f s) and fun s => ∫ φ ∂(sol N s) agree near t
      have h_eq : (fun s => ∫ z, φ z ∂(f s)) =ᶠ[nhds t] (fun s => ∫ z, φ z ∂(sol N s)) := by
        apply Filter.Eventually.mono (Ioo_mem_nhds ht.1 ht.2)
        intro s hs
        change ∫ z, φ z ∂f s = ∫ z, φ z ∂sol N s
        congr 1
        exact h_agree_fN s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      -- After congr_of_eventuallyEq, the derivative body still refers to sol N t.
      -- Rewrite the goal: f t = sol N t (h_agree_fN) so the derivative bodies match.
      have h_result := h_from_N.congr_of_eventuallyEq h_eq
      simp only [h_agree_fN t ⟨le_of_lt ht.1, ht.2.le⟩]
      exact h_result
    · -- IsCharacteristicFlowOn on Ioo 0 T_target.
      -- h_flow_N uses ρ = spatialMarginal ∘ sol N; we need ρ = spatialMarginal ∘ f.
      -- On Ioo 0 T_target, f t = sol N t (from h_agree_fN), so spatialMarginals agree.
      refine ⟨h_flow_N.1, ?_, ?_⟩
      · intro t ht z _
        exact h_flow_N.2.1 t (Set.Ioo_subset_Ioo le_rfl (by linarith) ht) z (Set.mem_univ z)
      · intro t ht z _
        simp only [h_agree_fN t ⟨le_of_lt ht.1, ht.2.le⟩]
        exact h_flow_N.2.2 t (Set.Ioo_subset_Ioo le_rfl (by linarith) ht) z (Set.mem_univ z)
    · -- Pushforward: f t = Measure.map (charX_N t, charV_N t) (f 0) for t ∈ Icc 0 T_target
      intro t ht
      rw [h_agree_fN t ht, h_f0_solN]
      exact h_push_N t ⟨ht.1, le_trans ht.2 (by linarith)⟩
    · -- AEMeasurable ∧ boundary ContinuousOn on Icc 0 T_target.
      refine ⟨?_, ?_⟩
      · intro s hs
        rw [h_f0_solN]
        exact h_aemeas_N s ⟨hs.1, le_trans hs.2 (by linarith)⟩
      · -- Boundary ContinuousOn: `sol N`'s boundary conjunct, same flow
        -- `charX_N/charV_N`, restricted from `Icc 0 (N+1)` to `Icc 0 T_target`.
        intro z
        exact (h_boundary_N z).mono (Set.Icc_subset_Icc le_rfl (by linarith))
  -- Conjunct 4: narrow continuity on Ici 0
  · -- Strategy: ContinuousOn (Ici 0) = ∀ t₀ ≥ 0, ContinuousWithinAt at t₀.
    -- For t₀ > 0: use flow continuity from HasDerivAt (interior) + integral_map + DCT.
    -- For t₀ = 0: right-continuity via DCT using the boundary regularity bundle.
    intro g hg_cont hg_bdd
    -- Extract probability measure structure from hf₀
    obtain ⟨hf₀_prob, hf₀_int⟩ := hf₀
    have hf₀_prob_inst : IsProbabilityMeasure f₀ := hf₀_prob
    -- Extract a uniform bound C for g from the bounded-range hypothesis
    obtain ⟨C, hg_range⟩ := hg_bdd.subset_closedBall (0 : ℝ)
    -- C is a non-negative bound: ∀ z, ‖g z‖ ≤ C
    have hgC : ∀ z : PhaseSpace d, ‖g z‖ ≤ C := fun z => by
      have h := Metric.mem_closedBall.mp (hg_range (Set.mem_range_self z))
      simp only [Real.dist_eq, sub_zero] at h
      rwa [Real.norm_eq_abs]
    -- Show ContinuousOn by checking ContinuousWithinAt at each point
    intro t₀ ht₀
    have ht₀_nn := Set.mem_Ici.mp ht₀
    rcases ht₀_nn.eq_or_lt with h_eq | ht₀_pos
    · -- t₀ = 0: right-continuity via DCT.  The endpoint analog of the interior
      -- case: pointwise continuity of `t ↦ (charX_N t z, charV_N t z)` at 0 is
      -- supplied by `sol N`'s boundary `ContinuousOn` conjunct, replacing the
      -- interior case's two-sided `HasDerivAt` (unavailable at the left endpoint).
      rw [← h_eq]
      set N : ℕ := 1 with hN_def
      have hN_cast_pos : (0 : ℝ) < (N : ℝ) := by norm_num [hN_def]
      have h_agree_fN : ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ), f t = sol N t := by
        intro t ht
        have ht_nn := ht.1
        change (if 0 ≤ t then sol ⌈t⌉₊ t else f₀) = sol N t
        simp only [ht_nn, ↓reduceIte]
        exact h_agree ⌈t⌉₊ N ((Nat.ceil_mono ht.2).trans_eq (Nat.ceil_natCast N))
          t ⟨ht.1, le_trans (Nat.le_ceil t) (by linarith)⟩
      obtain ⟨_h_pde, charX_N, charV_N, h_flow_N, h_push_N, h_aemeas_N, h_boundary_N⟩ :=
        h_sol_lag N
      have h_integral_eq : ∀ t ∈ Set.Icc 0 (N : ℝ),
          ∫ z, g z ∂(f t) = ∫ z, g (charX_N t z, charV_N t z) ∂f₀ := by
        intro t ht_Icc
        rw [h_agree_fN t ht_Icc]
        have ht_ext : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) + 1) :=
          ⟨ht_Icc.1, le_trans ht_Icc.2 (le_add_of_nonneg_right one_pos.le)⟩
        rw [h_push_N t ht_ext, ← h_sol_init N]
        exact integral_map (h_aemeas_N t ht_ext) hg_cont.measurable.aestronglyMeasurable
      have hIcc_mem : Set.Icc 0 (N : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) :=
        Icc_mem_nhdsGE hN_cast_pos
      refine (integral_continuousWithinAt_of_flow_rep f₀ f
        (fun t z => (charX_N t z, charV_N t z)) g hg_cont C hgC (N : ℝ) 0
        ⟨le_refl 0, hN_cast_pos.le⟩ h_integral_eq ?_ ?_).mono_of_mem_nhdsWithin hIcc_mem
      · intro t ht_mem
        exact (hg_cont.measurable.comp_aemeasurable
          (h_sol_init N ▸ h_aemeas_N t ⟨ht_mem.1, le_trans ht_mem.2
            (le_add_of_nonneg_right one_pos.le)⟩)).aestronglyMeasurable
      · intro z
        exact ((h_boundary_N z).continuousWithinAt
          ⟨le_refl 0, by linarith⟩).mono
          (Set.Icc_subset_Icc le_rfl (by linarith))
    · -- t₀ > 0: t₀ ∈ Ioi 0.  Use the interior flow continuity.
      -- Choose N so that t₀ is in the interior of [0, N].
      set N := ⌈t₀⌉₊ + 1 with hN_def
      have hN_cast_pos : (0 : ℝ) < (N : ℝ) := by positivity
      have ht₀_lt_N : t₀ < (N : ℝ) := by
        push_cast [hN_def]
        exact lt_add_of_le_of_pos (Nat.le_ceil t₀) one_pos
      -- Agreement: f t = sol N t for t ∈ [0, N]
      have h_agree_fN : ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ), f t = sol N t := by
        intro t ht
        have ht_nn := ht.1
        change (if 0 ≤ t then sol ⌈t⌉₊ t else f₀) = sol N t
        simp only [ht_nn, ↓reduceIte]
        exact h_agree ⌈t⌉₊ N ((Nat.ceil_mono ht.2).trans_eq (Nat.ceil_natCast N))
          t ⟨ht.1, le_trans (Nat.le_ceil t) (by linarith)⟩
      -- Extract flow witnesses from h_sol_lag N
      obtain ⟨_h_pde, charX_N, charV_N, h_flow_N, h_push_N, h_aemeas_N, _⟩ := h_sol_lag N
      -- The integral ∫ g ∂(f t) = ∫ z, g (charX_N t z, charV_N t z) ∂f₀
      -- for all t ∈ Icc 0 N (via pushforward formula + h_agree).
      have h_integral_eq : ∀ t ∈ Set.Icc 0 (N : ℝ),
          ∫ z, g z ∂(f t) = ∫ z, g (charX_N t z, charV_N t z) ∂f₀ := by
        intro t ht_Icc
        rw [h_agree_fN t ht_Icc]
        have ht_ext : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) + 1) :=
          ⟨ht_Icc.1, le_trans ht_Icc.2 (le_add_of_nonneg_right one_pos.le)⟩
        rw [h_push_N t ht_ext, ← h_sol_init N]
        exact integral_map (h_aemeas_N t ht_ext) hg_cont.measurable.aestronglyMeasurable
      -- The set Icc 0 N is a neighborhood of t₀ within Ici 0 (since 0 < t₀ < N).
      have hIcc_mem : Set.Icc 0 (N : ℝ) ∈ nhdsWithin t₀ (Set.Ici 0) := by
        apply nhdsWithin_le_nhds; exact Icc_mem_nhds ht₀_pos ht₀_lt_N
      refine (integral_continuousWithinAt_of_flow_rep f₀ f
        (fun t z => (charX_N t z, charV_N t z)) g hg_cont C hgC (N : ℝ) t₀
        ⟨ht₀_pos.le, ht₀_lt_N.le⟩ h_integral_eq ?_ ?_).mono_of_mem_nhdsWithin hIcc_mem
      · intro t ht_mem
        exact (hg_cont.measurable.comp_aemeasurable
          (h_sol_init N ▸ h_aemeas_N t ⟨ht_mem.1, le_trans ht_mem.2
            (le_add_of_nonneg_right one_pos.le)⟩)).aestronglyMeasurable
      · intro z
        have ht₀_in_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) ((N : ℝ) + 1) :=
          ⟨ht₀_pos, by push_cast [hN_def]; linarith [Nat.le_ceil t₀]⟩
        have hX_deriv := h_flow_N.2.1 t₀ ht₀_in_Ioo z (Set.mem_univ z)
        have hV_deriv := h_flow_N.2.2 t₀ ht₀_in_Ioo z (Set.mem_univ z)
        exact (hX_deriv.continuousAt.prodMk hV_deriv.continuousAt).continuousWithinAt

/-! ## §10  Marquee theorem (tex: thm:vlasov-wp) -/

/-- The `L = 0` (zero-force) branch of `vlasovWellPosedness`: the explicit
affine flow `(x, v) ↦ (x + t·v, v)` pushes `f₀` to a per-window Lagrangian
solution.  Every force-side obligation is trivial since `gradW ≡ 0`; the
moment/continuity threads come from the affine growth `‖x + t·v‖ ≤ (1+|t|)‖z‖`.
`f_sol` is threaded by its defining equation (let-bound caller supplies
`rfl`). -/
private lemma vlasovWellPosedness_zeroForce_solutionOn {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW_zero : ∀ x, gradW x = 0)
    (f₀ : Measure (PhaseSpace d)) (hf₀ : HasFiniteFirstMoment f₀)
    (f_sol : ℝ → Measure (PhaseSpace d))
    (hf_sol : f_sol = fun t => Measure.map
      (fun z : PhaseSpace d => (z.1 + t • z.2, z.2)) f₀)
    (T : ℝ) (hT : 0 < T) :
    IsLagrangianVlasovSolutionOn gradW f_sol T := by
  subst hf_sol
  have := hf₀.1
  let charX : ℝ → PhaseSpace d → PhysSpace d := fun t z => z.1 + t • z.2
  let charV : ℝ → PhaseSpace d → PhysSpace d := fun _ z => z.2
  have hconv_zero : ∀ (ρ : Measure (PhysSpace d)) (x : PhysSpace d),
      convolveFunctionMeasure gradW ρ x = 0 := by
    intros ρ x
    simp only [convolveFunctionMeasure]
    have : (fun y => gradW (x - y)) = fun _ => (0 : PhysSpace d) := by
      funext y; exact hgradW_zero (x - y)
    rw [this, integral_zero]
  have hL_zero : LipschitzWith 0 gradW := by
    rw [show gradW = fun _ => 0 from funext hgradW_zero]
    exact LipschitzWith.const' 0
  have hflow_univ : IsCharacteristicFlow gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV := by
    refine ⟨?_, ?_, ?_⟩
    · intro z; simp [charX, charV]
    · intro t z
      have h1 : HasDerivAt (fun s => z.1 + s • z.2) z.2 t := by
        have h1' : HasDerivAt (fun _ : ℝ => z.1) 0 t := hasDerivAt_const t z.1
        have h2' : HasDerivAt (fun s : ℝ => s • z.2) ((1 : ℝ) • z.2) t :=
          (hasDerivAt_id (𝕜 := ℝ) t).smul_const z.2
        have := h1'.add h2'; simp only [zero_add, one_smul] at this; exact this
      exact h1
    · intro t z
      simp only [vlasovSolutionViaPushforward, charX, charV]
      rw [hconv_zero, neg_zero]
      exact hasDerivAt_const t z.2
  have hself : IsCharacteristicFlowSelfConsistent charX f₀
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) := by
    intro t
    simp only [vlasovSolutionViaPushforward, spatialMarginal, charX, charV]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
  have h_flow_meas : ∀ s, AEMeasurable
      (fun z : PhaseSpace d => (charX s z, charV s z)) f₀ := by
    intro s; fun_prop
  have hgradW_cont : Continuous gradW := by
    have hz : gradW = fun _ => 0 := funext hgradW_zero
    rw [hz]; exact continuous_const
  have hconv_cont : ∀ s, Continuous (fun x =>
      convolveFunctionMeasure gradW
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x) := by
    intro s
    have hz : (fun x => convolveFunctionMeasure gradW
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x) =
        fun _ => 0 := funext (hconv_zero _)
    rw [hz]; exact continuous_const
  have h_int_conv : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y))
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    intro s x
    have h_zero : (fun y : PhysSpace d => gradW (x - y)) = fun _ => (0 : PhysSpace d) := by
      funext y; exact hgradW_zero (x - y)
    rw [h_zero]; exact integrable_zero _ _ _
  have hspatial_prob : ∀ s, IsProbabilityMeasure
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    intro s
    unfold spatialMarginal vlasovSolutionViaPushforward
    have _hpair : AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀ :=
      h_flow_meas s
    have _h_prob_inner : IsProbabilityMeasure
        (Measure.map (fun z : PhaseSpace d => (charX s z, charV s z)) f₀) :=
      (Measure.isProbabilityMeasure_map_iff _hpair).mpr inferInstance
    exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  have h_init0 : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := by
    intro z; simp [charX, charV]
  have hnorm_bound : ∀ (s : ℝ) (z : PhaseSpace d), ‖charX s z‖ ≤ (1 + |s|) * ‖z‖ := by
    intro s z
    simp only [charX]
    have hle2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
    have htabs : 0 ≤ |s| := abs_nonneg s
    have hsmul : ‖s • z.2‖ = |s| * ‖z.2‖ := by rw [norm_smul, Real.norm_eq_abs]
    have htri := norm_add_le z.1 (s • z.2)
    have hle1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
    have := mul_le_mul_of_nonneg_left hle2 htabs; rw [hsmul] at htri; nlinarith
  have hflow_on : IsCharacteristicFlowOn gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV (Set.Ioo 0 T) Set.univ :=
    ⟨fun z _ => hflow_univ.1 z, fun t _ z _ => hflow_univ.2.1 t z,
     fun t _ z _ => hflow_univ.2.2 t z⟩
  have h_cont_Icc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T) := by
    intro z; simp only [charX, charV]; fun_prop
  have h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW
          (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) s
          (charX s z, charV s z))
        (Set.Ici s) s := by
    intro z s _
    have hpair : HasDerivAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW
          (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) s
          (charX s z, charV s z)) s := by
      simp only [vlasovVectorField]
      exact (hflow_univ.2.1 s z).prodMk (hflow_univ.2.2 s z)
    exact hpair.hasDerivWithinAt
  have hmom_int : ∀ s,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))
        = ∫ z, ‖charX s z‖ ∂f₀ := by
    intro s
    have hs_eq : spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)
        = Measure.map (fun z => charX s z) f₀ := hself s
    rw [hs_eq]; exact integral_map (by fun_prop) (by fun_prop)
  have h_y_int : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    intro s _
    have hs_eq : spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)
        = Measure.map (fun z => charX s z) f₀ := hself s
    rw [hs_eq, integrable_map_measure (by fun_prop) (by fun_prop)]
    apply Integrable.mono' (hf₀.2.const_mul (1 + |s|))
    · fun_prop
    · apply Filter.Eventually.of_forall; intro z
      rw [Function.comp_apply, Real.norm_of_nonneg (norm_nonneg _)]
      exact hnorm_bound s z
  have hM_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))
        ≤ (1 + T) * ∫ z, ‖z‖ ∂f₀ := by
    intro s hs
    rw [hmom_int s]
    have hbound_s : ∀ z : PhaseSpace d, ‖charX s z‖ ≤ (1 + T) * ‖z‖ := by
      intro z
      have h2 : (1 + |s|) ≤ (1 + T) := by
        have hss : |s| = s := abs_of_nonneg hs.1
        rw [hss]; linarith [hs.2]
      calc ‖charX s z‖ ≤ (1 + |s|) * ‖z‖ := hnorm_bound s z
        _ ≤ (1 + T) * ‖z‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    calc ∫ z, ‖charX s z‖ ∂f₀
        ≤ ∫ z, (1 + T) * ‖z‖ ∂f₀ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => norm_nonneg _))
            (hf₀.2.const_mul (1 + T)) (Filter.Eventually.of_forall hbound_s)
      _ = (1 + T) * ∫ z, ‖z‖ ∂f₀ := by rw [integral_const_mul]
  have hM_ρ_nn : 0 ≤ (1 + T) * ∫ z, ‖z‖ ∂f₀ :=
    mul_nonneg (by linarith [hT]) (integral_nonneg (fun z => norm_nonneg _))
  exact vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn
    gradW 0 hL_zero charX charV f₀ hf₀.2 hT
    hflow_on h_init0 h_cont_Icc h_deriv_Ico
    ((1 + T) * ∫ z, ‖z‖ ∂f₀) hM_ρ_nn hM_ρ h_y_int h_int_conv
    hself h_flow_meas hgradW_cont hconv_cont


/-- (tex: thm:vlasov-wp)
Forward-in-time existence for the Vlasov equation.

Let f_0 ∈ 𝒫_1(ℝ^d × ℝ^d) be a probability measure with finite first moment.
Under Assumption ass:W, for an arbitrary Lipschitz constant of `gradW`, there
exists a narrowly continuous curve `t ↦ f_t ∈ 𝒫_1(ℝ^d × ℝ^d)` on `[0, ∞)`,
with `f_{t=0} = f_0`, solving eq:vlasov in the Lagrangian sense on every forward
window `[0, T_target]`.

Per-window uniqueness over the Lagrangian class is provided separately by
`vlasovWellPosedness_uniqueness`.  The proof case-splits on `L = 0` (constant
force, explicit solution) vs `0 < L` (the substantive forward-iteration path),
and holds for every `L` (no smallness restriction). -/
theorem vlasovWellPosedness
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    -- Lipschitz constant of gradW (arbitrary; no smallness restriction).
    -- External callers extract `L` from `[AssW W]`'s `lipschitzGrad` existential.
    (L : NNReal) (hL_gradW : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀) :
    -- Vlasov well-posedness is a forward-in-time Cauchy problem.  The forward-only
    -- `∃` is the mathematically accurate statement; per-window uniqueness is
    -- provided by `vlasovWellPosedness_uniqueness` as a separate interface.
    ∃ f : ℝ → Measure (PhaseSpace d),
      -- initial condition
      f 0 = f₀ ∧
      -- each f_t has finite first moment, for t ≥ 0.
      (∀ t ∈ Set.Ici (0 : ℝ), HasFiniteFirstMoment (f t)) ∧
      -- f solves the Vlasov equation IN THE LAGRANGIAN SENSE on every forward
      -- window [0, T_target].  Per-T_target `IsLagrangianVlasovSolutionOn` is the
      -- forward-only analog of the universal `IsLagrangianVlasovSolution`; the
      -- latter would require backward-time machinery which is not on the critical
      -- path for the well-posedness theorem.
      (∀ T_target : ℝ, 0 < T_target →
        IsLagrangianVlasovSolutionOn gradW f T_target) ∧
      -- f is narrowly continuous: t ↦ ∫ g df_t is continuous on the forward
      -- time domain `Set.Ici 0`, for every bounded continuous g.
      (∀ (g : PhaseSpace d → ℝ), Continuous g → Bornology.IsBounded (Set.range g) →
        ContinuousOn (fun t => ∫ z, g z ∂f t) (Set.Ici 0)) := by
  -- Step 1: Case split on whether L = 0 (constant force) or 0 < L.  Both
  -- branches are proved; the theorem holds for every Lipschitz constant.
  by_cases hL_pos : (0 : ℝ) < L
  · -- Case: 0 < L — the substantive path via forward iteration.
    -- `vlasovWellPosedness_universal_existence` produces per-T_target
    -- `IsLagrangianVlasovSolutionOn` (forward-only); the marquee bundles that
    -- shape directly as the existence claim.  Per-window uniqueness is
    -- available via `vlasovWellPosedness_uniqueness` as a separate interface.
    exact vlasovWellPosedness_universal_existence W gradW hgradW L hL_gradW
      hL_pos f₀ hf₀
  · -- Case: L = 0 (gradW is constant; explicit constant-force solution).
    -- Step L0-1: L = 0 as an NNReal.
    have hL_zero : L = 0 := by
      apply NNReal.coe_eq_zero.mp
      exact le_antisymm (not_lt.mp hL_pos) (NNReal.coe_nonneg L)
    -- Step L0-2: gradW ≡ 0 everywhere (LipschitzWith 0 means constant;
    -- gradient_zero_of_even gives gradW 0 = 0; so gradW ≡ 0).
    have hgradW_zero : ∀ x, gradW x = 0 := by
      intro x
      have hconst : ∀ a b, gradW a = gradW b := by
        rw [hL_zero] at hL_gradW
        exact (LipschitzWith.zero_iff gradW).mp hL_gradW
      have h0 : gradW 0 = 0 := by
        rw [hgradW 0]; exact gradient_zero_of_even W
      calc gradW x = gradW 0 := hconst x 0
        _ = 0 := h0
    -- Step L0-4: Define the explicit affine solution.
    let charX : ℝ → PhaseSpace d → PhysSpace d := fun t z => z.1 + t • z.2
    let charV : ℝ → PhaseSpace d → PhysSpace d := fun _ z => z.2
    let f_sol : ℝ → Measure (PhaseSpace d) :=
      fun t => Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) f₀
    -- Step L0-5: f_sol 0 = f₀.
    have hf_init : f_sol 0 = f₀ := by
      simp only [f_sol, charX, charV]
      have : (fun z : PhaseSpace d => (z.1 + (0 : ℝ) • z.2, z.2)) = id := by
        funext z; simp
      rw [this, Measure.map_id]
    -- Step L0-6: Each f_sol t has finite first moment.
    have hf_mom : ∀ t, HasFiniteFirstMoment (f_sol t) := by
      intro t
      constructor
      · -- IsProbabilityMeasure: pushforward of a probability measure under measurable map.
        have := hf₀.1
        exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
      · -- Integrable ‖·‖: reduce to f₀ via integral_map, then bound by (1+|t|)·‖z‖.
        have := hf₀.1
        rw [integrable_map_measure (by fun_prop) (by fun_prop)]
        apply Integrable.mono' (hf₀.2.const_mul (1 + |t|))
        · fun_prop
        · apply Filter.Eventually.of_forall; intro z
          simp only [Function.comp_apply, charX, charV]
          -- Goal: ‖‖(z.1+t•z.2, z.2)‖‖ ≤ (1+|t|) * ‖z‖
          rw [Real.norm_of_nonneg (norm_nonneg _)]
          -- Goal: ‖(z.1+t•z.2, z.2)‖ ≤ (1+|t|) * ‖z‖
          have hle1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
          have hle2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
          have htabs : 0 ≤ |t| := abs_nonneg t
          have hsmul : ‖t • z.2‖ = |t| * ‖z.2‖ := by rw [norm_smul, Real.norm_eq_abs]
          have htri := norm_add_le z.1 (t • z.2)
          have hn : 0 ≤ ‖z‖ := norm_nonneg _
          have h1 : ‖z.1 + t • z.2‖ ≤ (1 + |t|) * ‖z‖ := by
            have := mul_le_mul_of_nonneg_left hle2 htabs; rw [hsmul] at htri; nlinarith
          have h2 : ‖z.2‖ ≤ (1 + |t|) * ‖z‖ := by nlinarith
          rw [Prod.norm_def]
          exact max_le_iff.mpr ⟨h1, h2⟩
    -- Step L0-8: Narrow continuity.
    have hf_cont : ∀ (g : PhaseSpace d → ℝ), Continuous g → Bornology.IsBounded (Set.range g) →
        Continuous (fun t => ∫ z, g z ∂f_sol t) := by
      intro g hg_cont hg_bdd
      -- Extract uniform bound C: ∀ x, ‖g x‖ ≤ C.
      obtain ⟨C, hC⟩ := hg_bdd.exists_norm_le
      have hC_range : ∀ x : PhaseSpace d, ‖g x‖ ≤ C :=
        fun x => hC (g x) (Set.mem_range_self x)
      -- Rewrite via integral_map: ∫ g df_sol(t) = ∫ z, g(z.1+t•z.2, z.2) df₀.
      have h_rw : ∀ t, ∫ z, g z ∂f_sol t = ∫ z, g (z.1 + t • z.2, z.2) ∂f₀ := by
        intro t
        simp only [f_sol, charX, charV]
        rw [integral_map (by fun_prop) (by fun_prop)]
      simp_rw [h_rw]
      -- Apply continuous_of_dominated.
      have := hf₀.1
      apply continuous_of_dominated
      · intro t; exact (hg_cont.comp (by fun_prop)).aestronglyMeasurable
      · intro t; apply Filter.Eventually.of_forall; intro z
        exact hC_range _
      · exact integrable_const C
      · apply Filter.Eventually.of_forall; intro z
        exact hg_cont.comp (by fun_prop)
    -- Assemble ∃ (post-refactor: forward-only existence, no uniqueness clause).
    refine ⟨f_sol, hf_init, ?_, ?_, ?_⟩
    · -- Moment bound on Ici 0 — discard t < 0.
      intro t _
      exact hf_mom t
    · -- Per-T_target `IsLagrangianVlasovSolutionOn` — the zero-force branch,
      -- extracted as `vlasovWellPosedness_zeroForce_solutionOn`.
      intro T hT
      exact vlasovWellPosedness_zeroForce_solutionOn gradW hgradW_zero f₀ hf₀
        f_sol rfl T hT
    · -- Narrow continuity restricted to Ici 0.
      intro g hg_cont hg_bdd
      exact (hf_cont g hg_cont hg_bdd).continuousOn

/-! ## §10  Dobrushin stability chain -/
--
-- These declarations live here (rather than in `Basic.lean`) because their
-- substantive close needs `convolveFunctionMeasure_lipschitz_in_x`, defined in
-- this file: a `Basic.lean`-resident declaration cannot call a
-- `CharacteristicFlow.lean` declaration (import direction).  The pure-FA
-- placeholders, the helpers that don't depend on the force-Lipschitz estimate,
-- and the marquee `meanFieldLimit` (which takes the Dobrushin estimate as a
-- hypothesis) remain in `Basic.lean`.


/-- Package the bound and positivity of C into the existential conclusion of dobrushin:
∃ C > 0, ∀ t ≥ 0, W₁(f_t, g_t) ≤ exp(C·t) · W₁(f_0, g_0).
Depends on dobrushin_C_choice (in Basic.lean) and dobrushin_ennreal_bound. -/
lemma dobrushin_package_exists
    {d : ℕ}
    (W : PhysSpace d → ℝ) [_hW : AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsLagrangianVlasovSolution gradW f)
    (hg : IsLagrangianVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 0 ≤ t →
        wasserstein1 (f t) (g t) ≤
          ENNReal.ofReal (Real.exp (C * t)) * wasserstein1Coupling (f 0) (g 0) := by
  -- Routed through the integrated-coupling core via `dobrushin_meanfield_On`:
  -- pick C = 2·(max 1 L) and window each `t ≥ 0` at `T = t + 1` (uniform in
  -- `t`, including `t = 0`) via `.toOn`.  This bypasses the Gronwall-coupling
  -- W₁-continuity / right-derivative analytic route entirely.
  refine ⟨2 * ((max 1 L : NNReal) : ℝ), ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
      rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_left _ _
    linarith
  · intro t ht
    exact dobrushin_meanfield_On gradW L hL f g (t + 1) (by linarith)
      (hf.toOn (t + 1)) (hg.toOn (t + 1))
      (fun s _ => hf_prob s) (fun s _ => hg_prob s) t ⟨ht, by linarith⟩

/-- (tex: thm:dobrushin)
Dobrushin's stability theorem (1979).

Under Assumption ass:W, there exists a constant C = C(L) > 0 such that for any
two measure-valued solutions f_t, g_t ∈ 𝒫_1(ℝ^d × ℝ^d) of the Vlasov equation
eq:vlasov,

  W_1(f_t, g_t) ≤ e^{C·t} · W_1(f_0, g_0),   for all t ≥ 0,

where W_1 is the Wasserstein-1 distance.
The proof uses a coupling via the characteristic flows eq:char and a Gronwall
inequality; the key estimate is |∇W * ρ − ∇W * σ|_∞ ≤ L · W_1(ρ, σ).

The `[AssW W]` instance and `hgradW` record the standing setup ass:W (∇W the
gradient of an even C^{1,1} potential); the inequality itself consumes only
the Lipschitz bound `hL` — see `dobrushin_on` below for the minimal-hypothesis
window form with the explicit constant `C = 2 · max 1 L`. -/
theorem dobrushin
    {d : ℕ}
    (W : PhysSpace d → ℝ) [hW : AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    -- L is the Lipschitz constant of ∇W from Assumption ass:W
    (L : NNReal) (hL : LipschitzWith L gradW)
    -- f and g are two Lagrangian Vlasov solutions (carrying characteristic
    -- flow witnesses).
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsLagrangianVlasovSolution gradW f)
    (hg : IsLagrangianVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 0 ≤ t →
        wasserstein1 (f t) (g t) ≤
          ENNReal.ofReal (Real.exp (C * t)) * wasserstein1 (f 0) (g 0) := by
  -- close via dobrushin_package_exists (B-free coupling core), then convert the
  -- primal-coupling RHS `wasserstein1Coupling (f 0) (g 0)` to the dual RHS
  -- `wasserstein1 (f 0) (g 0)` via the KR duality bridge `wasserstein1_eq_coupling`
  -- (the sole Foundation-B use in this corollary).
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    dobrushin_package_exists W gradW hgradW L hL f g hf hg hf_prob hg_prob
  refine ⟨C, hC_pos, fun t ht => ?_⟩
  have : IsProbabilityMeasure (f 0) := (hf_prob 0).1
  have : IsProbabilityMeasure (g 0) := (hg_prob 0).1
  have hfm0 : Integrable (fun y => dist y (0 : PhaseSpace d)) (f 0) := by
    simpa only [dist_zero_right] using (hf_prob 0).2
  have hgm0 : Integrable (fun y => dist y (0 : PhaseSpace d)) (g 0) := by
    simpa only [dist_zero_right] using (hg_prob 0).2
  rw [wasserstein1_eq_coupling (f 0) (g 0) 0 hfm0 hgm0]
  exact hC_bound t ht

/-- **Dobrushin stability on the window `[0, T]`** — the public form of the
uniform-constant estimate, with the dual `W₁` metric on both sides.

Unlike the marquee `dobrushin` (global two-sided solutions, existential
constant), this form (i) consumes exactly what `vlasovWellPosedness` emits —
per-window `IsLagrangianVlasovSolutionOn` plus window moments — and (ii)
exposes the **explicit constant** `C = 2 · max 1 L`, which depends only on
the force's Lipschitz bound, not on the solution pair.  That uniformity is
what a mean-field argument quantifying over a family of solutions (e.g.
empirical curves, once their flow witnesses are formalized) needs. -/
theorem dobrushin_on
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (T : ℝ) (hT : 0 < T)
    (hf : IsLagrangianVlasovSolutionOn gradW f T)
    (hg : IsLagrangianVlasovSolutionOn gradW g T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (g t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      wasserstein1 (f t) (g t) ≤
        ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) *
          wasserstein1 (f 0) (g 0) := by
  intro t ht
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hT.le⟩
  have : IsProbabilityMeasure (f 0) := (hf_mom 0 h0).1
  have : IsProbabilityMeasure (g 0) := (hg_mom 0 h0).1
  have hfm0 : Integrable (fun y => dist y (0 : PhaseSpace d)) (f 0) := by
    simpa only [dist_zero_right] using (hf_mom 0 h0).2
  have hgm0 : Integrable (fun y => dist y (0 : PhaseSpace d)) (g 0) := by
    simpa only [dist_zero_right] using (hg_mom 0 h0).2
  rw [wasserstein1_eq_coupling (f 0) (g 0) 0 hfm0 hgm0]
  exact dobrushin_meanfield_On gradW L hL f g T hT hf hg hf_mom hg_mom t ht

/-- **Forward-global Dobrushin stability with the explicit uniform constant.**

Stability for the solution class `vlasovWellPosedness` constructs: the
hypotheses are verbatim the existence theorem's conclusion clauses (the
per-window `IsLagrangianVlasovSolutionOn` family on every horizon, moments on
`Set.Ici 0`), and the estimate holds for all `t ≥ 0` with the
pair-independent constant `C = 2 · max 1 L`.  This is the arrow that lets the
existence output feed a Dobrushin-type stability input; see
`vlasovWellPosedness_stability` for the packaged composition. -/
theorem dobrushin_forward
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : ∀ T : ℝ, 0 < T → IsLagrangianVlasovSolutionOn gradW f T)
    (hg : ∀ T : ℝ, 0 < T → IsLagrangianVlasovSolutionOn gradW g T)
    (hf_mom : ∀ t ∈ Set.Ici (0 : ℝ), HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Ici (0 : ℝ), HasFiniteFirstMoment (g t)) :
    ∀ t : ℝ, 0 ≤ t →
      wasserstein1 (f t) (g t) ≤
        ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) *
          wasserstein1 (f 0) (g 0) := by
  intro t ht
  exact dobrushin_on gradW L hL f g (t + 1) (by linarith)
    (hf (t + 1) (by linarith)) (hg (t + 1) (by linarith))
    (fun s hs => hf_mom s hs.1) (fun s hs => hg_mom s hs.1) t ⟨ht, by linarith⟩

/-- **Well-posedness package: existence + stability, chained.**

For any two initial data `f₀, g₀ ∈ 𝒫₁`, the curves produced by
`vlasovWellPosedness` satisfy the Dobrushin estimate with the explicit
constant `C = 2 · max 1 L` at every `t ≥ 0` — the composition of the two
headline theorems, recorded so that the existence output demonstrably feeds
the stability input (`dobrushin_forward`). -/
theorem vlasovWellPosedness_stability
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ g₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀) (hg₀ : HasFiniteFirstMoment g₀) :
    ∃ f g : ℝ → Measure (PhaseSpace d),
      f 0 = f₀ ∧ g 0 = g₀ ∧
      (∀ T : ℝ, 0 < T → IsLagrangianVlasovSolutionOn gradW f T) ∧
      (∀ T : ℝ, 0 < T → IsLagrangianVlasovSolutionOn gradW g T) ∧
      ∀ t : ℝ, 0 ≤ t →
        wasserstein1 (f t) (g t) ≤
          ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) *
            wasserstein1 f₀ g₀ := by
  obtain ⟨f, hf_init, hf_mom, hf_lag, _⟩ :=
    vlasovWellPosedness W gradW hgradW L hL f₀ hf₀
  obtain ⟨g, hg_init, hg_mom, hg_lag, _⟩ :=
    vlasovWellPosedness W gradW hgradW L hL g₀ hg₀
  refine ⟨f, g, hf_init, hg_init, hf_lag, hg_lag, ?_⟩
  have h := dobrushin_forward gradW L hL f g hf_lag hg_lag hf_mom hg_mom
  simpa only [hf_init, hg_init] using h

/-- **Coupling-metric Dobrushin stability estimate** — the `wasserstein1Coupling`
(primal) analogue of `DobrushinStabilityEstimate` (Basic).  LHS is the genuine
dual `W₁` metric; the RHS base is the primal coupling-inf metric
`wasserstein1Coupling`.  This is the form the **B-free** core
(`dobrushin_package_exists`) produces. -/
def DobrushinStabilityEstimateCoupling {d : ℕ}
    (f g : ℝ → Measure (PhaseSpace d)) (C : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    wasserstein1 (f t) (g t) ≤
      ENNReal.ofReal (Real.exp (C * t)) * wasserstein1Coupling (f 0) (g 0)

/-- **Mean-field limit — B-free coupling form.**

The `meanFieldLimit` (Basic) analogue that consumes the **coupling-metric**
stability estimate (`DobrushinStabilityEstimateCoupling`, produced B-free by
`dobrushin_package_exists`) and **coupling-metric** initial convergence
(`wasserstein1Coupling (μ_0^N) f₀ → 0`).  The conclusion is unchanged:
convergence of the empirical curves to the Vlasov solution in the genuine dual
`W₁` metric.  Axiom-clean (`#print axioms`): **B-free**.

**Why coupling-`hInit` — the initial-convergence type the B-free limit requires.**
The B-free estimate puts `wasserstein1Coupling` on the RHS base, so the squeeze
needs `wasserstein1Coupling (μ_0^N) f₀ → 0`.  Standard dual-`W₁` initial
convergence does NOT supply this B-free: `wasserstein1 ≤ wasserstein1Coupling`
(`wasserstein1_le_wasserstein1Coupling`), so dual-small does not bound the
coupling — the easy direction runs the wrong way for a *hypothesis*; converting
dual→coupling is the hard direction (= Foundation B, `wasserstein1_eq_coupling`).
The two are mathematically equal (KR duality) and coupling-convergence is the
*natural* form for empirical measures (one exhibits couplings to bound the cost
from above), so this is a nominal — not a real — strengthening.  The all-dual
`meanFieldLimit` (Basic) remains the standard-hypothesis form, routing through
the all-dual `dobrushin` (the single Foundation-B bridge). -/
theorem meanFieldLimit_coupling
    {d : ℕ}
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (_hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) (_hf₀ : HasFiniteFirstMoment f₀)
    (f : ℝ → Measure (PhaseSpace d))
    (_hf_sol : IsLagrangianVlasovSolution gradW f)
    (hf_init : f 0 = f₀)
    (X V : (N : ℕ) → ℝ → Fin N → PhysSpace d)
    (_hSol : ∀ (N : ℕ), IsNewtonSolution N gradW (X N) (V N))
    -- initial empirical measures converge to f₀ in the COUPLING metric
    (hInit : Filter.Tendsto
      (fun N : ℕ => wasserstein1Coupling (empiricalMeasure N (X N 0) (V N 0)) f₀)
      Filter.atTop (nhds 0))
    (C : ℝ) (hC : 0 < C)
    (hDobrushin : ∀ (N : ℕ), DobrushinStabilityEstimateCoupling
      (empiricalMeasureCurve N (X N) (V N)) f C)
    (T : ℝ) (_hT : 0 < T) :
    Filter.Tendsto
      (fun N : ℕ => ⨆ t ∈ Set.Icc 0 T,
        wasserstein1 (empiricalMeasureCurve N (X N) (V N) t) (f t))
      Filter.atTop (nhds 0) := by
  have hsup_bound : ∀ N : ℕ,
      ⨆ t ∈ Set.Icc 0 T, wasserstein1 (empiricalMeasureCurve N (X N) (V N) t) (f t) ≤
        ENNReal.ofReal (Real.exp (C * T)) *
          wasserstein1Coupling (empiricalMeasureCurve N (X N) (V N) 0) (f 0) := by
    intro N
    apply iSup_le; intro t
    apply iSup_le; intro ht
    calc wasserstein1 (empiricalMeasureCurve N (X N) (V N) t) (f t)
        ≤ ENNReal.ofReal (Real.exp (C * t)) *
            wasserstein1Coupling (empiricalMeasureCurve N (X N) (V N) 0) (f 0) :=
          hDobrushin N t ht.1
      _ ≤ ENNReal.ofReal (Real.exp (C * T)) *
            wasserstein1Coupling (empiricalMeasureCurve N (X N) (V N) 0) (f 0) := by
          apply mul_le_mul_of_nonneg_right _ (zero_le)
          apply ENNReal.ofReal_le_ofReal
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (le_of_lt hC))
  have hUpper : Filter.Tendsto
      (fun N : ℕ => ENNReal.ofReal (Real.exp (C * T)) *
        wasserstein1Coupling (empiricalMeasureCurve N (X N) (V N) 0) (f 0))
      Filter.atTop (nhds 0) := by
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.exp (C * T)))
      hInit (Or.inr ENNReal.ofReal_ne_top)
    simpa [empiricalMeasureCurve, hf_init, mul_zero] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
    (fun _ => zero_le) hsup_bound

end Vlasov
