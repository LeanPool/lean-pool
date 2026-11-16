/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.WeightedGradient.Multiplier
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# When is `C_c^∞(V)` an operator core of the generator?

`HeatSemigroup/BakryEmery/GammaTwo.lean` proves the weak `Γ₂` inequality along the heat flow under
exactly
one hypothesis, `hcore`: every `F ∈ D(A)`, `A = Tbar†Tbar`, is a limit of smooth compactly supported
classes **in the graph norm of `A`**, equivalently `ℒ = Δ - ⟪∇U, ∇·⟫` is essentially self-adjoint
on `C_c^∞(V)` in `L²(ν)`. This module proves the half of that statement which is a global
argument, and isolates the half which is a local regularity theorem.

## What is proved

Write `Tbar` for the closed unit-weight gradient of `ν = m.tilted (-U)` and `A = Tbar†Tbar ≥ 0`.

* `eq_zero_of_localRegularity`: if `u ∈ L²(ν)` satisfies `⟪A [f], u⟫ + ⟪[f], u⟫ = 0` for every
  `f ∈ C_c^∞(V)` — that is, `u ⊥ (A + 1) C_c^∞(V)` — and if **every** localization `[χ u]`,
  `χ ∈ C_c^∞(V)`, lies in `D(Tbar)`, then `u = 0`.
* `exists_seq_smooth_tendsto_adjointComp_of_localRegularity`: consequently, if that local
  regularity holds for every such `u`, then `C_c^∞(V)` **is** an operator core of `A`, i.e.
  `hcore` holds.
* `eq_zero_of_mem_closedWeightedOperator_domain` and
  `exists_seq_smooth_tendsto_adjointComp_of_mem_domain` are the same two statements with the
  stronger, more familiar hypothesis `u ∈ D(Tbar)` in place of the local one.

The potential is only assumed `C¹` and **no convexity, no semigroup and no `Γ₂` input is used**.

## The two ingredients and their separate owners

The classical proof that a weighted Laplacian on a complete space is essentially self-adjoint on
`C_c^∞` has two independent ingredients:

1. *interior regularity*: a distributional solution of `ℒ u = u` is locally in the form domain;
2. *completeness at infinity*: a solution that is locally in the form domain, on a complete
   space, is globally in it and therefore zero.

Ingredient 2 is what this module proves, in the quantitative form
`‖χ_r u‖ ≤ (M / r) ‖u‖` for the scaled cutoffs `χ_r` (`norm_toLp_mul_cutoff_le`); letting
`r → ∞` gives `u = 0`. The cutoff is tested against the equation through the already available
Leibniz rule `Tbar (χ x) = χ (Tbar x) + x (B ∇χ)` for an arbitrary form-domain `x`, the sequential
smooth graph core of `Tbar`, and the weak integration by parts `⟪A f, x⟫ = ⟪Tbar f, Tbar x⟫`. Only the
**first derivative** of the cutoff appears, so the unbounded commutator `⟪∇U, ∇χ⟫` that obstructs
a naive truncation of `F ∈ D(A)` never occurs.

Ingredient 1 is **not** proved here: it is the hypothesis of the two criterion theorems. It is a
genuine interior elliptic regularity statement for `div(e^{-U} ∇ ·)`, proved by mollification in
`HeatSemigroup/Generator/InteriorRegularity.lean`
(`toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`), which then discharges the
hypothesis of both criterion theorems (`exists_seq_smooth_tendsto_adjointComp`).

## The local hypothesis is equivalent to `hcore`, not weaker

If `hcore` holds then `(A + 1) C_c^∞(V)` is dense, so there is no nonzero class orthogonal to it
and the hypothesis of the criterion holds vacuously; the criterion proves the converse. The two
are therefore **logically equivalent**, and no claim of a weaker assumption is made. What the
criterion changes is *which* classical ingredient is left to prove: a global operator-theoretic
statement about `A` is replaced by a local regularity statement about a single equation, with the
global cutoff argument discharged once and for all.

## What this is not

No essential self-adjointness is proved **in this module**, and no weak `Γ₂` inequality is
proved unconditionally here; both follow once the local hypothesis is supplied, which
`HeatSemigroup/Generator/InteriorRegularity.lean` does. The statements above are implications; their
hypotheses are visible in their types and are not packaged into a structure, an instance or a
definition. The KLS target itself is proved in `KLS/Target.lean` (`KLS.kls`, through the BKL
route); this module contributes only the operator-core criterion described above.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Metric Set InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

open Energy Energy.WeightedGradient

section Cutoff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- One fixed smooth profile, equal to one on the ball of radius five and supported in the ball
of radius eight. -/
private def profile : ContDiffBump (0 : V) := ⟨5, 8, by norm_num, by norm_num⟩

/-- The scaled cutoff `χ_r (y) = profile (r⁻¹ • y)`: one on `closedBall 0 (5 r)`, zero off
`ball 0 (8 r)`, with gradient of size `O(1/r)`. -/
private def cutoff (r : ℝ) (y : V) : ℝ := (profile (V := V)) (r⁻¹ • y)

private theorem contDiff_cutoff (r : ℝ) : ContDiff ℝ ∞ (cutoff (V := V) r) :=
  (profile (V := V)).contDiff.comp (contDiff_id.const_smul _)

private theorem cutoff_nonneg (r : ℝ) (y : V) : 0 ≤ cutoff (V := V) r y :=
  (profile (V := V)).nonneg

private theorem cutoff_le_one (r : ℝ) (y : V) : cutoff (V := V) r y ≤ 1 :=
  (profile (V := V)).le_one

private theorem abs_cutoff_le_one (r : ℝ) (y : V) : |cutoff (V := V) r y| ≤ 1 :=
  abs_le.mpr ⟨le_trans (by norm_num) (cutoff_nonneg r y), cutoff_le_one r y⟩

private theorem cutoff_eq_one {r : ℝ} (hr : 0 < r) {y : V} (hy : ‖y‖ ≤ 5 * r) :
    cutoff (V := V) r y = 1 := by
  apply (profile (V := V)).one_of_mem_closedBall
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr),
    ← div_eq_inv_mul, div_le_iff₀ hr]
  exact hy

private theorem cutoff_eq_zero {r : ℝ} (hr : 0 < r) {y : V} (hy : 8 * r ≤ ‖y‖) :
    cutoff (V := V) r y = 0 := by
  apply (profile (V := V)).zero_of_le_dist
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr),
    ← div_eq_inv_mul, le_div_iff₀ hr]
  exact hy

private theorem tsupport_cutoff_subset {r : ℝ} (hr : 0 < r) :
    tsupport (cutoff (V := V) r) ⊆ closedBall (0 : V) (8 * r) := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  exact hy (cutoff_eq_zero hr (le_of_lt (not_le.1 h)))

private theorem hasCompactSupport_cutoff {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (cutoff (V := V) r) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : V) (8 * r))
    ((subset_tsupport _).trans (tsupport_cutoff_subset hr))

/-- On the open ball where the cutoff is constantly one its gradient vanishes. -/
private theorem gradient_cutoff_eq_zero {r : ℝ} (hr : 0 < r) {y : V} (hy : ‖y‖ < 5 * r) :
    gradient (cutoff (V := V) r) y = 0 := by
  have hmem : y ∈ ball (0 : V) (5 * r) := by
    rw [mem_ball, dist_zero_right]; exact hy
  have hev : cutoff (V := V) r =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_ball.mem_nhds hmem] with z hz
    rw [mem_ball, dist_zero_right] at hz
    exact cutoff_eq_one hr hz.le
  rw [gradient, hev.fderiv_eq, fderiv_const_apply, map_zero]

/-- A single bound for the gradients of the whole scaled family. -/
private theorem exists_norm_gradient_cutoff_le :
    ∃ M : ℝ, 0 < M ∧ ∀ r : ℝ, 0 < r → ∀ y : V, ‖gradient (cutoff (V := V) r) y‖ ≤ M / r := by
  have hb : ContDiff ℝ 1 ((profile (V := V)) : V → ℝ) := (profile (V := V)).contDiff
  obtain ⟨M, hM⟩ := ((profile (V := V)).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hb.continuous_fderiv one_ne_zero)
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun r hr y => ?_⟩
  have hlin : HasFDerivAt (fun y : V => r⁻¹ • y) (r⁻¹ • ContinuousLinearMap.id ℝ V) y :=
    (hasFDerivAt_id y).const_smul _
  have hd := (hb.differentiable one_ne_zero _).hasFDerivAt.comp y hlin
  have hnorm : ‖gradient (cutoff (V := V) r) y‖ = ‖fderiv ℝ (cutoff (V := V) r) y‖ := by
    rw [gradient, (toDual ℝ V).symm.norm_map]
  rw [hnorm]
  have hfd : fderiv ℝ (cutoff (V := V) r) y
      = fderiv ℝ (((profile (V := V)) : V → ℝ) ∘ fun y : V => r⁻¹ • y) y := rfl
  rw [hfd, hd.fderiv]
  have hop : ‖r⁻¹ • ContinuousLinearMap.id ℝ V‖ ≤ r⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_nonneg.2 hr.le)).trans_eq
      (mul_one _)
  calc
    _ ≤ ‖fderiv ℝ ((profile (V := V)) : V → ℝ) (r⁻¹ • y)‖ *
        ‖r⁻¹ • ContinuousLinearMap.id ℝ V‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ max M 1 * r⁻¹ := mul_le_mul ((hM _).trans (le_max_left _ _)) hop
      (norm_nonneg _) (le_trans zero_le_one (le_max_right _ _))
    _ = max M 1 / r := (div_eq_mul_inv _ _).symm

end Cutoff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

section Criterion

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- Multiplication by a smooth cutoff preserves a graph-core approximation when it fixes
both graph components and its gradient annihilates the scalar component. -/
private theorem exists_seq_localized_tendsto_graph
    (z : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {ξ : V → ℝ} (hξs : ContDiff ℝ ∞ ξ) (hξc : HasCompactSupport ξ)
    (hξm : AEStronglyMeasurable ξ (ν : Measure V))
    (hξb : ∀ᵐ y ∂(ν : Measure V), |ξ y| ≤ 1)
    (hgξm : AEStronglyMeasurable (gradient ξ) (ν : Measure V))
    {Nξ : ℝ} (hgξb : ∀ᵐ y ∂(ν : Measure V), ‖gradient ξ y‖ ≤ Nξ)
    (hξz : L2.bddSmulL (H := ℝ) hξm hξb (z : Lp ℝ 2 (ν : Measure V)) = z)
    (hξTz : L2.bddSmulL (H := V) hξm hξb
      ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) z) =
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) z)
    (hgξ0 : L2.bddSmulRightL (H := V) hgξm hgξb (z : Lp ℝ 2 (ν : Measure V)) = 0) :
    ∃ (g : ℕ → V → ℝ) (hg : ∀ n, ContDiff ℝ ∞ (g n))
        (_hgc : ∀ n, HasCompactSupport (g n)),
      Tendsto (fun n => (memLp_of_contDiff_hasCompactSupport ν
        (hξs.mul (hg n)) (hξc.mul_right)).toLp (fun y => ξ y * g n y)) atTop
        (𝓝 (z : Lp ℝ 2 (ν : Measure V))) ∧
      Tendsto (fun n => (memLp_gradient_of_contDiff_hasCompactSupport
        (hξs.mul (hg n)) (hξc.mul_right)).toLp (gradient fun y => ξ y * g n y)) atTop
        (𝓝 ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) z)) := by
  obtain ⟨g, hg, hgc, hcv1, hcv2⟩ := hν.exists_seq_smooth_tendsto_graph m
    (ContinuousLinearMap.id ℝ V) hi z
  have hfs : ∀ n, ContDiff ℝ ∞ fun y => ξ y * g n y :=
    fun n => hξs.mul (hg n)
  have hfc : ∀ n, HasCompactSupport fun y => ξ y * g n y :=
    fun n => hξc.mul_right
  -- the gradient class of a smooth compactly supported function, in the two shapes used
  have hbridge : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc' : HasCompactSupport f),
      (IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hf
          hfc').memLp_apply.toLp (apply (ContinuousLinearMap.id ℝ V) f)
        = (memLp_gradient_of_contDiff_hasCompactSupport hf hfc').toLp (gradient f) := by
    intro f hf hfc'
    refine Lp.ext ?_
    filter_upwards [(IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hf
        hfc').memLp_apply.coeFn_toLp,
      (memLp_gradient_of_contDiff_hasCompactSupport hf hfc').coeFn_toLp] with y e1 e2
    rw [e1, e2, apply_id]
  -- `[ξ gₙ] → z` in `L²`
  have hfL : ∀ n, (memLp_of_contDiff_hasCompactSupport ν (hfs n) (hfc n)).toLp _
      = L2.bddSmulL (H := ℝ) hξm hξb
        ((memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)) := by
    intro n
    refine Lp.ext ?_
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν (hfs n) (hfc n)).coeFn_toLp,
      L2.coeFn_bddSmulL (H := ℝ) hξm hξb
        ((memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)),
      (memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).coeFn_toLp] with y e1 e2 e3
    rw [e1, e2, e3, smul_eq_mul]
  have hcvf : Tendsto (fun n => (memLp_of_contDiff_hasCompactSupport ν (hfs n) (hfc n)).toLp
      (fun y => ξ y * g n y)) atTop
      (𝓝 (((z) : (Lp ℝ 2 (ν : Measure V))))) := by
    have h := ((L2.bddSmulL (H := ℝ) hξm hξb).continuous.tendsto
      (((z) :
        (Lp ℝ 2 (ν : Measure V))))).comp hcv1
    rw [hξz] at h
    exact h.congr fun n => (hfL n).symm
  -- `[∇(ξ gₙ)] → Tbar z` in `L²`
  have hgradf : ∀ n, (memLp_gradient_of_contDiff_hasCompactSupport (hfs n) (hfc n)).toLp
        (gradient fun y => ξ y * g n y)
      = L2.bddSmulL (H := V) hξm hξb
          ((memLp_gradient_of_contDiff_hasCompactSupport (hg n) (hgc n)).toLp (gradient (g n)))
        + L2.bddSmulRightL (H := V) hgξm hgξb
          ((memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)) := by
    intro n
    refine Lp.ext ?_
    filter_upwards [(memLp_gradient_of_contDiff_hasCompactSupport (hfs n) (hfc n)).coeFn_toLp,
      Lp.coeFn_add (L2.bddSmulL (H := V) hξm hξb
          ((memLp_gradient_of_contDiff_hasCompactSupport (hg n) (hgc n)).toLp (gradient (g n))))
        (L2.bddSmulRightL (H := V) hgξm hgξb
          ((memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n))),
      L2.coeFn_bddSmulL (H := V) hξm hξb
        ((memLp_gradient_of_contDiff_hasCompactSupport (hg n) (hgc n)).toLp (gradient (g n))),
      L2.coeFn_bddSmulRightL (H := V) hgξm hgξb
        ((memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)),
      (memLp_gradient_of_contDiff_hasCompactSupport (hg n) (hgc n)).coeFn_toLp,
      (memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).coeFn_toLp] with
      y e1 e2 e3 e4 e5 e6
    rw [e1, e2, Pi.add_apply, e3, e4, e5, e6,
      gradient_mul (hξs.differentiable (by simp)).differentiableAt
        ((hg n).differentiable (by simp)).differentiableAt]
  have hcvg : Tendsto (fun n => (memLp_gradient_of_contDiff_hasCompactSupport (hfs n)
      (hfc n)).toLp (gradient fun y => ξ y * g n y)) atTop
      (𝓝 ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) z)) := by
    have hcv2' : Tendsto (fun n => (memLp_gradient_of_contDiff_hasCompactSupport (hg n)
        (hgc n)).toLp (gradient (g n))) atTop (𝓝
          ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) z)) :=
      hcv2.congr fun n => hbridge _ (hg n) (hgc n)
    have h := (((L2.bddSmulL (H := V) hξm hξb).continuous.tendsto
        ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) z)).comp hcv2').add
      (((L2.bddSmulRightL (H := V) hgξm hgξb).continuous.tendsto
        (((z) : (Lp ℝ 2 (ν : Measure V))))).comp hcv1)
    rw [hξTz, hgξ0, add_zero] at h
    exact h.congr fun n => (hgradf n).symm
  exact ⟨g, hg, hgc, hcvf, hcvg⟩

/-- The scaled-cutoff estimate behind the criterion: a class annihilating `(A + 1) C_c^∞(V)`
whose localizations all lie in `D(Tbar)` has `‖χ_r u‖ ≤ (M / r) ‖u‖` for the cutoff family. -/
private theorem norm_toLp_mul_cutoff_le
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : (Lp ℝ 2 (ν : Measure V)))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2 (ν : Measure V))), u⟫ = 0)
    (hloc : ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
      (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {r M : ℝ} (hr : 0 < r) (hM0 : 0 ≤ M)
    (hM : ∀ y : V, ‖gradient (cutoff (V := V) r) y‖ ≤ M / r) :
    ‖(memLp_mul_of_contDiff_hasCompactSupport (ν := ν) (contDiff_cutoff r)
        (hasCompactSupport_cutoff hr) u).toLp _‖ ≤ (M / r) * ‖u‖ := by
  classical
  have hd : Dense ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain : Set
    (Lp ℝ 2 (ν : Measure V))) :=
    hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hr2 : (0:ℝ) < 2 * r := by linarith
  have hr4 : (0:ℝ) < 4 * r := by linarith
  have hMr : 0 ≤ M / r := div_nonneg hM0 hr.le
  -- the three cutoffs

  -- Prepare the three cutoff scales and their support identities.
  have hχs : ContDiff ℝ ∞ (cutoff (V := V) r) := contDiff_cutoff r
  have hχc : HasCompactSupport (cutoff (V := V) r) := hasCompactSupport_cutoff hr
  have hξs : ContDiff ℝ ∞ (cutoff (V := V) (2 * r)) := contDiff_cutoff _
  have hξc : HasCompactSupport (cutoff (V := V) (2 * r)) := hasCompactSupport_cutoff hr2
  have hζs : ContDiff ℝ ∞ (cutoff (V := V) (4 * r)) := contDiff_cutoff _
  have hζc : HasCompactSupport (cutoff (V := V) (4 * r)) := hasCompactSupport_cutoff hr4
  have hχm : AEStronglyMeasurable (cutoff (V := V) r)
    (ν : Measure V) := hχs.continuous.aestronglyMeasurable
  have hξm : AEStronglyMeasurable (cutoff (V := V) (2 * r)) (ν : Measure V) :=
    hξs.continuous.aestronglyMeasurable
  have hχb : ∀ᵐ y ∂(ν : Measure V), |cutoff (V := V) r y| ≤ 1 :=
    Filter.Eventually.of_forall (abs_cutoff_le_one r)
  have hξb : ∀ᵐ y ∂(ν : Measure V), |cutoff (V := V) (2 * r) y| ≤ 1 :=
    Filter.Eventually.of_forall (abs_cutoff_le_one (2 * r))
  have hgχm : AEStronglyMeasurable (gradient (cutoff (V := V) r)) (ν : Measure V) :=
    (continuous_gradient (hχs.of_le (mod_cast le_top))).aestronglyMeasurable
  have hgξm : AEStronglyMeasurable (gradient (cutoff (V := V) (2 * r))) (ν : Measure V) :=
    (continuous_gradient (hξs.of_le (mod_cast le_top))).aestronglyMeasurable
  have hgχb : ∀ᵐ y ∂(ν : Measure V), ‖gradient (cutoff (V := V) r) y‖ ≤ M / r :=
    Filter.Eventually.of_forall hM
  obtain ⟨Nξ, hNξ⟩ := (continuous_gradient (hξs.of_le (mod_cast le_top))
      (f := cutoff (V := V) (2 * r))).bounded_above_of_compact_support
    (hasCompactSupport_gradient hξc)
  have hgξb : ∀ᵐ y ∂(ν : Measure V), ‖gradient (cutoff (V := V) (2 * r)) y‖ ≤ Nξ :=
    Filter.Eventually.of_forall hNξ
  -- where the larger cutoffs are identically one
  have hnorm_le : ∀ y : V, y ∈ tsupport (cutoff (V := V) r) → ‖y‖ ≤ 8 * r := by
    intro y hy
    have := tsupport_cutoff_subset hr hy
    rwa [mem_closedBall, dist_zero_right] at this
  have hξone : ∀ y : V, y ∈ tsupport (cutoff (V := V) r) → cutoff (V := V) (2 * r) y = 1 := by
    intro y hy
    exact cutoff_eq_one hr2 (le_trans (hnorm_le y hy) (by linarith))
  have hgξzero : ∀ y : V, y ∈ tsupport (cutoff (V := V) r) →
      gradient (cutoff (V := V) (2 * r)) y = 0 := by
    intro y hy
    exact gradient_cutoff_eq_zero hr2 (lt_of_le_of_lt (hnorm_le y hy) (by linarith))
  have hζone : ∀ y : V, y ∈ tsupport (cutoff (V := V) (2 * r)) →
      cutoff (V := V) (4 * r) y = 1 := by
    intro y hy
    have := tsupport_cutoff_subset hr2 hy
    rw [mem_closedBall, dist_zero_right] at this
    exact cutoff_eq_one hr4 (le_trans this (by linarith))
  -- the three domain elements

  -- Place the localized functions in the closed operator domain.
  have hwmem : (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hζs hζc u).toLp _ ∈
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :=
    hloc _ hζs hζc
  have hw₁mem := hν.toLp_mul_mem_closedWeightedOperator_domain m (ContinuousLinearMap.id ℝ V) hi
    hχs hχc (⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
  have hzmem := hν.toLp_mul_mem_closedWeightedOperator_domain m (ContinuousLinearMap.id ℝ V) hi
    hχs hχc (⟨_, hw₁mem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
  have hζone2 : ∀ y : V, y ∈ tsupport (cutoff (V := V) r) → cutoff (V := V) (4 * r) y = 1 := by
    intro y hy
    exact cutoff_eq_one hr4 (le_trans (hnorm_le y hy) (by linarith))
  -- representatives
  have hw_ae := (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hζs hζc u).coeFn_toLp
  have hw₁_ae := (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc
    (((⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) :
      (Lp ℝ 2 (ν : Measure V)))).coeFn_toLp
  have hz_ae := (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc
    (((⟨_, hw₁mem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) :
      (Lp ℝ 2 (ν : Measure V)))).coeFn_toLp
  have hcu_ae := (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).coeFn_toLp
  have hTw₁ := hν.coeFn_closedWeightedOperator_toLp_mul m (ContinuousLinearMap.id ℝ V) hi hχs hχc
    (⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) hw₁mem
  have hTz := hν.coeFn_closedWeightedOperator_toLp_mul m (ContinuousLinearMap.id ℝ V) hi hχs hχc
    (⟨_, hw₁mem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) hzmem
  -- the two auxiliary `L²` classes
  set p : (Lp V 2 (ν : Measure V)) := L2.bddSmulL (H := V) hχm hχb
    ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) with hp
  set q : (Lp V 2 (ν : Measure V)) := L2.bddSmulRightL (H := V) hgχm hgχb
    (((⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) :
      (Lp ℝ 2 (ν : Measure V))) with hq
  have hp_ae := L2.coeFn_bddSmulL (H := V) hχm hχb
    ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain))
  have hq_ae := L2.coeFn_bddSmulRightL (H := V) hgχm hgχb (((⟨_, hwmem⟩ :
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
      (ν : Measure V)))
  -- `Tbar z = χ p + 2 χ q`

  -- Expand the operator pairings and cancel the nested cutoff terms.
  have hA : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
      = L2.bddSmulL (H := V) hχm hχb p + (2 : ℝ) • L2.bddSmulL (H := V) hχm hχb q := by
    refine Lp.ext ?_
    filter_upwards [hTz, hTw₁, hw₁_ae, hp_ae, hq_ae,
      L2.coeFn_bddSmulL (H := V) hχm hχb p, L2.coeFn_bddSmulL (H := V) hχm hχb q,
      Lp.coeFn_add (L2.bddSmulL (H := V) hχm hχb p)
        ((2 : ℝ) • L2.bddSmulL (H := V) hχm hχb q),
      Lp.coeFn_smul (2 : ℝ) (L2.bddSmulL (H := V) hχm hχb q)] with
      y e1 e2 e3 e4 e5 e6 e7 e8 e9
    rw [e1, e8, Pi.add_apply, e6, e9, Pi.smul_apply, e7, e4, e5, e2, e3, apply_id]
    module
  -- `⟪Tbar z, Tbar w⟫ = ‖p‖² + 2 ⟪q, p⟫`
  have hB : ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)⟫
      = ‖p‖ ^ 2 + 2 * ⟪q, p⟫ := by
    rw [hA, inner_add_left, real_inner_smul_left,
      L2.inner_bddSmulL_left (E := V) hχm hχb p
        ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)),
      L2.inner_bddSmulL_left (E := V) hχm hχb q
        ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)),
      ← hp, real_inner_self_eq_norm_sq]
  -- the tested class is `χ² u`
  have hζm : AEStronglyMeasurable (cutoff (V := V) (4 * r)) (ν : Measure V) :=
    hζs.continuous.aestronglyMeasurable
  have hζb : ∀ᵐ y ∂(ν : Measure V), |cutoff (V := V) (4 * r) y| ≤ 1 :=
    Filter.Eventually.of_forall (abs_cutoff_le_one (4 * r))
  have hc_eq : (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).toLp _
      = L2.bddSmulL (H := ℝ) hχm hχb u := by
    refine Lp.ext ?_
    filter_upwards [hcu_ae, L2.coeFn_bddSmulL (H := ℝ) hχm hχb u] with y e1 e2
    rw [e1, e2, smul_eq_mul]
  have hw_eq : (((⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
    hi).domain)) : (Lp ℝ 2 (ν : Measure V))) = L2.bddSmulL (H := ℝ) hζm hζb u := by
    refine Lp.ext ?_
    filter_upwards [hw_ae, L2.coeFn_bddSmulL (H := ℝ) hζm hζb u] with y e1 e2
    rw [e1, e2, smul_eq_mul]
  have hz_eq : (((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
    hi).domain)) : (Lp ℝ 2 (ν : Measure V)))
      = L2.bddSmulL (H := ℝ) hχm hχb
        ((memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).toLp _) := by
    refine Lp.ext ?_
    filter_upwards [hz_ae, hw₁_ae, hw_ae, hcu_ae,
      L2.coeFn_bddSmulL (H := ℝ) hχm hχb
        ((memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).toLp _)] with y e1 e2 e3 e4 e5
    rw [e1, e5, e4, e2, e3, smul_eq_mul]
    by_cases hy : y ∈ tsupport (cutoff (V := V) r)
    · rw [hζone2 y hy]; ring
    · rw [image_eq_zero_of_notMem_tsupport hy]; ring
  have hC : ⟪(((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
    hi).domain)) : (Lp ℝ 2 (ν : Measure V))), u⟫
      = ‖(memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).toLp _‖ ^ 2 := by
    rw [hz_eq, L2.inner_bddSmulL_left (E := ℝ) hχm hχb _ u, ← hc_eq, real_inner_self_eq_norm_sq]
  -- the orthogonality identity
  have hD : ⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)⟫
      = -⟪(((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) :
        (Lp ℝ 2 (ν : Measure V))), u⟫ := by
    have hξz : L2.bddSmulL (H := ℝ) hξm hξb ((((⟨_, hzmem⟩ :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
        (ν : Measure V))))
        = (((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) :
          (Lp ℝ 2 (ν : Measure V))) := by
      refine Lp.ext ?_
      filter_upwards [L2.coeFn_bddSmulL (H := ℝ) hξm hξb
        ((((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) :
          (Lp ℝ 2 (ν : Measure V)))), hz_ae] with y e1 e2
      rw [e1, e2, smul_eq_mul]
      by_cases hy : y ∈ tsupport (cutoff (V := V) r)
      · rw [hξone y hy]; ring
      · rw [image_eq_zero_of_notMem_tsupport hy]; ring
    have hξTz : L2.bddSmulL (H := V) hξm hξb
      ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain))
        = (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) := by
      refine Lp.ext ?_
      filter_upwards [L2.coeFn_bddSmulL (H := V) hξm hξb
        ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)), hTz] with y e1 e2
      rw [e1, e2]
      by_cases hy : y ∈ tsupport (cutoff (V := V) r)
      · rw [hξone y hy, one_smul]
      · rw [image_eq_zero_of_notMem_tsupport hy, apply_id,
          Analysis.BakryEmery.gradient_eq_zero_of_notMem_tsupport hy]
        simp
    have hgξ0 : L2.bddSmulRightL (H := V) hgξm hgξb ((((⟨_, hzmem⟩ :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
        (ν : Measure V)))) = 0 := by
      refine Lp.ext ?_
      filter_upwards [L2.coeFn_bddSmulRightL (H := V) hgξm hgξb
          ((((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
            hi).domain)) : (Lp ℝ 2 (ν : Measure V)))), hz_ae,
        Lp.coeFn_zero (E := V) (p := 2) (μ := (ν : Measure V))] with y e1 e2 e3
      rw [e1, e3, Pi.zero_apply, e2]
      by_cases hy : y ∈ tsupport (cutoff (V := V) r)
      · rw [hgξzero y hy, smul_zero]
      · rw [image_eq_zero_of_notMem_tsupport hy]; simp
    obtain ⟨g, hg, hgc, hcvf, hcvg⟩ := exists_seq_localized_tendsto_graph m hν hi
      (⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
      hξs hξc hξm hξb hgξm hgξb hξz hξTz hgξ0
    have hfs : ∀ n, ContDiff ℝ ∞ fun y => cutoff (V := V) (2 * r) y * g n y :=
      fun n => hξs.mul (hg n)
    have hfc : ∀ n, HasCompactSupport fun y => cutoff (V := V) (2 * r) y * g n y :=
      fun n => hξc.mul_right
    -- the generator image of the localized test function, and where it lives
    have hAae : ∀ n, (((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
      ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfs n)
          (hfc n)⟩ : (Lp ℝ 2 (ν : Measure V))) : V → ℝ)
        =ᵐ[(ν : Measure V)] fun y => -weightedLaplacian U
          (fun z => cutoff (V := V) (2 * r) z * g n z) y := by
      intro n
      rw [hν.adjointComp_toLp_eq m hi hνU hU (hfs n) (hfc n)]
      exact (memLp_neg_weightedLaplacian (ν := ν) hU (hfs n) (hfc n)).coeFn_toLp
    have hζ16 : ∀ (n : ℕ) (y : V),
        y ∈ tsupport (fun z => cutoff (V := V) (2 * r) z * g n z) →
        cutoff (V := V) (4 * r) y = 1 := fun n y hy => hζone y (tsupport_mul_subset_left hy)
    have hpair : ∀ n, ⟪((adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfs n)
          (hfc n)⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫
        = ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfs n) (hfc n)⟩ : (Lp ℝ 2
            (ν : Measure V))),
            (((⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
              hi).domain)) : (Lp ℝ 2 (ν : Measure V)))⟫ := by
      intro n
      have h0 : ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfs n)
          (hfc n)⟩ : (Lp ℝ 2 (ν : Measure V))), u - (((⟨_, hwmem⟩ :
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
              (ν : Measure V)))⟫ = 0 := by
        rw [L2.inner_def]
        refine integral_eq_zero_of_ae ?_
        filter_upwards [hAae n, Lp.coeFn_sub u (((⟨_, hwmem⟩ :
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
            (ν : Measure V))),
          hw_ae] with y e1 e2 e3
        rw [Pi.zero_apply, Real.inner_apply, e1, e2, Pi.sub_apply, e3]
        by_cases hy : y ∈ tsupport (fun z => cutoff (V := V) (2 * r) z * g n z)
        · rw [hζ16 n y hy]; ring
        · rw [weightedLaplacian_eq_zero_of_notMem_tsupport U hy]; ring
      rw [inner_sub_right, sub_eq_zero] at h0
      exact h0
    have hIBP : ∀ n, ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
      ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfs n)
          (hfc n)⟩ : (Lp ℝ 2 (ν : Measure V))), (((⟨_, hwmem⟩ :
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
              (ν : Measure V)))⟫
        = ⟪(memLp_gradient_of_contDiff_hasCompactSupport (hfs n) (hfc n)).toLp
            (gradient fun y => cutoff (V := V) (2 * r) y * g n y),
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)⟫ := by
      intro n
      rw [inner_adjointComp hd (⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfs n)
        (hfc n)⟩ : ((adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) hwmem]
      congr 1
      exact hν.closedWeightedOperator_toLp_eq m hi (hfs n) (hfc n)
    have hkey : ∀ n, ⟪(memLp_gradient_of_contDiff_hasCompactSupport (hfs n) (hfc n)).toLp
          (gradient fun y => cutoff (V := V) (2 * r) y * g n y),
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)⟫
        = -⟪((memLp_of_contDiff_hasCompactSupport ν (hfs n) (hfc n)).toLp
            (fun y => cutoff (V := V) (2 * r) y * g n y) : (Lp ℝ 2 (ν : Measure V))), u⟫ := by
      intro n
      have h := horth _ (hfs n) (hfc n)
      rw [← hIBP n, ← hpair n]
      linarith [h]
    have hlim1 : Tendsto (fun n => ⟪(memLp_gradient_of_contDiff_hasCompactSupport (hfs n)
          (hfc n)).toLp (gradient fun y => cutoff (V := V) (2 * r) y * g n y),
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)⟫) atTop
        (𝓝 (⟪(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hzmem⟩ :
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (⟨_, hwmem⟩ :
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)⟫)) :=
      hcvg.inner tendsto_const_nhds
    have hlim2 : Tendsto (fun n => -⟪((memLp_of_contDiff_hasCompactSupport ν (hfs n)
          (hfc n)).toLp (fun y => cutoff (V := V) (2 * r) y * g n y) : (Lp ℝ 2
            (ν : Measure V))), u⟫) atTop
        (𝓝 (-⟪(((⟨_, hzmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
          hi).domain)) : (Lp ℝ 2 (ν : Measure V))), u⟫)) :=
      (hcvf.inner tendsto_const_nhds).neg
    exact tendsto_nhds_unique (hlim1.congr hkey) hlim2
  -- the resulting quadratic estimate

  -- Convert the resulting energy comparison into the norm bound.
  have hqnorm : ‖q‖ ≤ M / r * ‖u‖ := by
    have h1 : ‖q‖ ≤ |M / r| * ‖(((⟨_, hwmem⟩ :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
        (ν : Measure V)))‖ := by
      rw [hq]
      simpa using L2.norm_bddSmulRightₗ_le (H := V) hgχm hgχb
        (((⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) :
          (Lp ℝ 2 (ν : Measure V)))
    have h2 : ‖(((⟨_, hwmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
      hi).domain)) : (Lp ℝ 2 (ν : Measure V)))‖ ≤ ‖u‖ := by
      rw [hw_eq]
      simpa using L2.norm_bddSmulₗ_le (H := ℝ) hζm hζb u
    calc ‖q‖ ≤ |M / r| * ‖(((⟨_, hwmem⟩ :
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
        (ν : Measure V)))‖ := h1
      _ = M / r * ‖(((⟨_, hwmem⟩ :
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)) : (Lp ℝ 2
          (ν : Measure V)))‖ := by rw [abs_of_nonneg hMr]
      _ ≤ M / r * ‖u‖ := by exact mul_le_mul_of_nonneg_left h2 hMr
  have hsq : ‖(memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).toLp _‖ ^ 2
      ≤ ‖q‖ ^ 2 := by
    have hcs : |⟪q, p⟫| ≤ ‖q‖ * ‖p‖ := abs_real_inner_le_norm q p
    have hid := hB.symm.trans (hD.trans (by rw [hC]))
    nlinarith [abs_nonneg (⟪q, p⟫ : ℝ), le_abs_self (⟪q, p⟫ : ℝ), neg_abs_le (⟪q, p⟫ : ℝ),
      norm_nonneg p, norm_nonneg q, sq_nonneg (‖p‖ - ‖q‖)]
  have hfinal : ‖(memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).toLp _‖ ≤ ‖q‖ := by
    nlinarith [norm_nonneg ((memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχs hχc u).toLp
      (fun y => cutoff (V := V) r y * u y)), norm_nonneg q]
  exact hfinal.trans hqnorm

/-- **A deficiency element of the minimal generator that is locally in the form domain
vanishes.**

Let `u ∈ L²(ν)` be orthogonal to `(A + 1) C_c^∞(V)`, that is, `⟪A [f], u⟫ + ⟪[f], u⟫ = 0` for
every smooth compactly supported `f`. If every localization `[χ u]`, `χ ∈ C_c^∞(V)`, lies in the
form domain `D(Tbar)`, then `u = 0`.

Only *local* membership is assumed: no global gradient of `u`, no smoothness of `u` and no
classical representative are used. The passage from local to global is the cutoff estimate
`‖χ_r u‖ ≤ (M / r) ‖u‖`, which is where completeness of the ambient Euclidean space enters. The
potential is only `C¹` and no convexity is used. -/
theorem eq_zero_of_localRegularity
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : (Lp ℝ 2 (ν : Measure V)))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2 (ν : Measure V))), u⟫ = 0)
    (hloc : ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
      (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    u = 0 := by
  classical
  obtain ⟨M, hM0, hM⟩ := exists_norm_gradient_cutoff_le (V := V)
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hbound : ∀ n : ℕ, ‖(memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
      (contDiff_cutoff ((n : ℝ) + 1)) (hasCompactSupport_cutoff (hpos n)) u).toLp _‖
      ≤ M / ((n : ℝ) + 1) * ‖u‖ := fun n =>
    norm_toLp_mul_cutoff_le m hν hi hνU hU u horth hloc (hpos n) hM0.le (hM _ (hpos n))
  -- the localizations converge to `u` in `L²`, by dominated convergence
  have hsq : ∀ n : ℕ, ‖u - (memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
      (contDiff_cutoff ((n : ℝ) + 1)) (hasCompactSupport_cutoff (hpos n)) u).toLp _‖ ^ 2
      = ∫ y, ((1 - cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2 ∂(ν : Measure V) := by
    intro n
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub u ((memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
        (contDiff_cutoff ((n : ℝ) + 1)) (hasCompactSupport_cutoff (hpos n)) u).toLp _),
      (memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
        (contDiff_cutoff ((n : ℝ) + 1)) (hasCompactSupport_cutoff (hpos n)) u).coeFn_toLp] with
      y e1 e2
    rw [Real.inner_apply, e1, Pi.sub_apply, e2]
    ring
  have hdom : Tendsto
    (fun n : ℕ => ∫ y, ((1 - cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2 ∂(ν : Measure V))
      atTop (𝓝 0) := by
    have hint : Integrable (fun y => (u y) ^ 2) (ν : Measure V) := (Lp.memLp u).integrable_sq
    have hmeas : ∀ n : ℕ, AEStronglyMeasurable
        (fun y => ((1 - cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2) (ν : Measure V) := by
      intro n
      exact ((((continuous_const.sub
        (contDiff_cutoff ((n : ℝ) + 1)).continuous)).aestronglyMeasurable).mul
          (Lp.aestronglyMeasurable u)).pow 2
    have hbd : ∀ n : ℕ, ∀ᵐ y ∂(ν : Measure V),
        ‖((1 - cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2‖ ≤ (u y) ^ 2 := by
      intro n
      refine Filter.Eventually.of_forall fun y => ?_
      have h1 : |1 - cutoff (V := V) ((n : ℝ) + 1) y| ≤ 1 :=
        abs_le.mpr ⟨by linarith [cutoff_le_one ((n : ℝ) + 1) y], by
          linarith [cutoff_nonneg ((n : ℝ) + 1) y]⟩
      have h2 : ((1 - cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2 ≤ (u y) ^ 2 := by
        have := mul_le_mul_of_nonneg_right h1 (abs_nonneg (u y))
        calc ((1 - cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2
            = (|1 - cutoff (V := V) ((n : ℝ) + 1) y| * |u y|) ^ 2 := by
              rw [← abs_mul, sq_abs]
          _ ≤ (1 * |u y|) ^ 2 := by
              apply pow_le_pow_left₀ (by positivity) this
          _ = (u y) ^ 2 := by rw [one_mul, sq_abs]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h2
    have hlim : ∀ᵐ y ∂(ν : Measure V), Tendsto
        (fun n : ℕ => ((1 - cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2) atTop (𝓝 0) := by
      refine Filter.Eventually.of_forall fun y => ?_
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      refine (Filter.eventually_atTop.2 ⟨⌈‖y‖⌉₊, fun n hn => ?_⟩)
      have hy : ‖y‖ ≤ 5 * ((n : ℝ) + 1) := by
        have h1 : ‖y‖ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
        linarith
      simp [cutoff_eq_one (hpos n) hy]
    have := tendsto_integral_of_dominated_convergence (μ := (ν : Measure V))
      (F := fun (n : ℕ) y => ((1 - cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2)
      (f := fun _ : V => (0 : ℝ)) (fun y => (u y) ^ 2) hmeas hint hbd hlim
    simpa using this
  have hten : Tendsto (fun n : ℕ => ‖u - (memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
      (contDiff_cutoff ((n : ℝ) + 1)) (hasCompactSupport_cutoff (hpos n)) u).toLp _‖)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ‖u - (memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
        (contDiff_cutoff ((n : ℝ) + 1)) (hasCompactSupport_cutoff (hpos n)) u).toLp _‖ ^ 2)
        atTop (𝓝 0) := by
      simpa only [hsq] using hdom
    have h2 := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h1
    simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at h2
    exact h2
  -- the two bounds force `‖u‖ = 0`
  have hzero : ‖u‖ ≤ 0 := by
    have hsum : Tendsto (fun n : ℕ => ‖u - (memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
        (contDiff_cutoff ((n : ℝ) + 1)) (hasCompactSupport_cutoff (hpos n)) u).toLp _‖
        + M / ((n : ℝ) + 1) * ‖u‖) atTop (𝓝 0) := by
      have h3 : Tendsto (fun n : ℕ => M / ((n : ℝ) + 1) * ‖u‖) atTop (𝓝 0) := by
        have := (tendsto_const_div_atTop_nhds_zero_nat M).mul_const ‖u‖
        simpa using (tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)).mul_const ‖u‖
      simpa using hten.add h3
    refine ge_of_tendsto hsum (Filter.Eventually.of_forall fun n => ?_)
    calc ‖u‖ = ‖(u - (memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
          (contDiff_cutoff ((n : ℝ) + 1)) (hasCompactSupport_cutoff (hpos n)) u).toLp _)
          + (memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
          (contDiff_cutoff ((n : ℝ) + 1)) (hasCompactSupport_cutoff (hpos n)) u).toLp _‖ := by
            rw [sub_add_cancel]
      _ ≤ ‖u - (memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
          (contDiff_cutoff ((n : ℝ) + 1)) (hasCompactSupport_cutoff (hpos n)) u).toLp _‖
          + ‖(memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
          (contDiff_cutoff ((n : ℝ) + 1)) (hasCompactSupport_cutoff (hpos n)) u).toLp _‖ :=
            norm_add_le _ _
      _ ≤ _ := by linarith [hbound n]
  exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg u))

/-- **Operator-core criterion: local regularity of deficiency elements implies that `C_c^∞(V)`
is an operator core of `A = Tbar†Tbar`.**

Assume that every `u ∈ L²(ν)` orthogonal to `(A + 1) C_c^∞(V)` has all of its localizations
`[χ u]`, `χ ∈ C_c^∞(V)`, in the form domain `D(Tbar)`. Then every `F ∈ D(A)` is the limit of smooth
compactly supported classes **in the graph norm of `A`**: `[fₙ] → F` and `A [fₙ] → A F` in
`L²(ν)`. This is the hypothesis `hcore` of
`HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_core`.

The proof is the standard deficiency argument: `eq_zero_of_localRegularity` says that the
orthogonal complement of the range of `A + 1` on `C_c^∞(V)` is trivial, so that range is dense;
and `‖(A + 1) v‖² = ‖A v‖² + 2 ‖Tbar v‖² + ‖v‖²` converts approximation of `(A + 1) F` into
simultaneous approximation of `F` and `A F`. Nothing beyond the stated hypothesis is assumed: the
potential is only `C¹` and no convexity, no semigroup and no `Γ₂` input is used. -/
theorem exists_seq_smooth_tendsto_adjointComp_of_localRegularity
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (hreg :
      ∀ u : (Lp ℝ 2 (ν : Measure V)),
        (∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
            ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
                      ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ :
                    (Lp ℝ 2 (ν : Measure V))),
                  u⟫ +
                ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
                    (Lp ℝ 2 (ν : Measure V))),
                  u⟫ =
              0) →
          ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
            (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (F : ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n)) (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto
          (fun n =>
            ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n) -
                (F : (Lp ℝ 2 (ν : Measure V)))‖)
          atTop (𝓝 0) ∧
        Tendsto
          (fun n =>
            ‖((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
                    ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩ :
                  (Lp ℝ 2 (ν : Measure V))) -
                ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F :
                  (Lp ℝ 2 (ν : Measure V)))‖)
          atTop (𝓝 0) := by
  classical
  have hd :
    Dense
      (((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain :
        Set (Lp ℝ 2 (ν : Measure V))) :=
    hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  set Ψ :
    ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain →ₗ[ℝ]
      (Lp ℝ 2 (ν : Measure V)) :=
    ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).toFun +
      ((adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain.subtype with
    hΨ
  have hΨapply :
    ∀ v : ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain,
      Ψ v =
        ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) v :
            (Lp ℝ 2 (ν : Measure V))) +
          (v : (Lp ℝ 2 (ν : Measure V))) :=
    fun v => rfl
  set K : Submodule ℝ (Lp ℝ 2 (ν : Measure V)) :=
    Submodule.map Ψ
      (Submodule.comap
        ((adjointComp
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain.subtype
        (smoothCore ν)) with
    hK
  -- the orthogonal complement of the range is trivial
  have hKorth : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    have horth :
      ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
        ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
                  ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ :
                (Lp ℝ 2 (ν : Measure V))),
              u⟫ +
            ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2 (ν : Measure V))),
              u⟫ =
          0 := by
      intro f hf hfc
      have hmemK : Ψ ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ ∈ K :=
        Submodule.mem_map_of_mem ⟨f, hf, hfc, rfl⟩
      have h0 := (Submodule.mem_orthogonal K u).mp hu _ hmemK
      rw [hΨapply, inner_add_left] at h0
      exact h0
    exact eq_zero_of_localRegularity m hν hi hνU hU u horth (hreg u horth)
  have hdense : Dense (K : Set (Lp ℝ 2 (ν : Measure V))) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (Submodule.topologicalClosure_eq_top_iff.mpr hKorth)
  obtain ⟨x, hxK, hxlim⟩ := mem_closure_iff_seq_limit.mp (hdense (Ψ F))
  have hchoice :
    ∀ n,
      ∃ z :
        ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain,
        (z : (Lp ℝ 2 (ν : Measure V))) ∈ smoothCore ν ∧ Ψ z = x n := by
    intro n
    obtain ⟨z, hzmem, hzeq⟩ := hxK n
    exact ⟨z, hzmem, hzeq⟩
  choose z hzs hzeq using hchoice
  have hzsm :
    ∀ n,
      ∃ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
        (z n : (Lp ℝ 2 (ν : Measure V))) =
          (memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :=
    hzs
  choose fn hfn hfnc hfneq using
    hzsm
  -- the graph-norm comparison
  have hcmp :
    ∀ n,
      ‖(z n : (Lp ℝ 2 (ν : Measure V))) - (F : (Lp ℝ 2 (ν : Measure V)))‖ ≤ ‖x n - Ψ F‖ ∧
        ‖((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n) :
                (Lp ℝ 2 (ν : Measure V))) -
              ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F :
                (Lp ℝ 2 (ν : Measure V)))‖ ≤
          ‖x n - Ψ F‖ := by
    intro n
    have hv : Ψ (z n - F) = x n - Ψ F := by rw [map_sub, hzeq n]
    have hcoe :
      ((z n - F :
            ((adjointComp
                (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) :
          (Lp ℝ 2 (ν : Measure V))) =
        (z n : (Lp ℝ 2 (ν : Measure V))) - (F : (Lp ℝ 2 (ν : Measure V))) :=
      rfl
    have hAsub :
      ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n - F) :
          (Lp ℝ 2 (ν : Measure V))) =
        ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n) :
            (Lp ℝ 2 (ν : Measure V))) -
          ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F :
            (Lp ℝ 2 (ν : Measure V))) :=
      LinearPMap.map_sub _ _ _
    have hnn :
      0 ≤
        ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
              (z n - F) :
            (Lp ℝ 2 (ν : Measure V))),
          ((z n - F :
              ((adjointComp
                  (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) :
            (Lp ℝ 2 (ν : Measure V)))⟫ := by
      rw [inner_adjointComp_self hd (z n - F)]
      positivity
    have hexp :
      ‖Ψ (z n - F)‖ ^ 2 =
        ‖((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
                    (z n - F) :
                  (Lp ℝ 2 (ν : Measure V)))‖ ^
              2 +
            2 *
              ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
                    (z n - F) :
                  (Lp ℝ 2 (ν : Measure V))),
                ((z n - F :
                    ((adjointComp
                        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V)
                          hi))).domain) :
                  (Lp ℝ 2 (ν : Measure V)))⟫ +
          ‖((z n - F :
                  ((adjointComp
                      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) :
                (Lp ℝ 2 (ν : Measure V)))‖ ^
            2 := by
      rw [hΨapply]
      exact norm_add_sq_real _ _
    rw [hAsub, hcoe] at hnn
    rw [hv, hcoe, hAsub] at hexp
    constructor
    · nlinarith [hexp, hnn, norm_nonneg (x n - Ψ F),
        norm_nonneg ((z n : (Lp ℝ 2 (ν : Measure V))) - (F : (Lp ℝ 2 (ν : Measure V)))),
        norm_nonneg
          (((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n) :
              (Lp ℝ 2 (ν : Measure V))) -
            ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F :
              (Lp ℝ 2 (ν : Measure V))))]
    · nlinarith [hexp, hnn, norm_nonneg (x n - Ψ F),
        norm_nonneg ((z n : (Lp ℝ 2 (ν : Measure V))) - (F : (Lp ℝ 2 (ν : Measure V)))),
        norm_nonneg
          (((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n) :
              (Lp ℝ 2 (ν : Measure V))) -
            ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F :
              (Lp ℝ 2 (ν : Measure V))))]
  have hlim0 : Tendsto (fun n => ‖x n - Ψ F‖) atTop (𝓝 0) := by
    have := (hxlim.sub (tendsto_const_nhds (x := Ψ F))).norm
    simpa using this
  have hzeq' :
    ∀ n,
      (⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩ :
          ((adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) =
        z n :=
    fun n => Subtype.ext (hfneq n).symm
  refine ⟨fn, hfn, hfnc, ?_, ?_⟩
  · refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim0
    rw [← hfneq n]
    exact (hcmp n).1
  · refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim0
    rw [hzeq' n]
    exact (hcmp n).2

/-- **The global form-domain special case of `eq_zero_of_localRegularity`.** If a deficiency
element happens to lie in `D(Tbar)` itself, it vanishes; the localizations are then automatic by
the Leibniz rule for a smooth compactly supported multiplier. -/
theorem eq_zero_of_mem_closedWeightedOperator_domain
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : (Lp ℝ 2
      (ν : Measure V))) (hu : u ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2
          (ν : Measure V))), u⟫ = 0) :
    u = 0 :=
  eq_zero_of_localRegularity m hν hi hνU hU u horth fun _χ hχ hχc =>
    hν.toLp_mul_mem_closedWeightedOperator_domain m (ContinuousLinearMap.id ℝ V) hi hχ hχc
      ⟨u, hu⟩

/-- **Operator-core criterion from global regularity of deficiency elements.** The recognizable
form of `exists_seq_smooth_tendsto_adjointComp_of_localRegularity`: if every `L²` class
orthogonal to `(A + 1) C_c^∞(V)` lies in the form domain `D(Tbar)`, then `C_c^∞(V)` is an operator
core of `A`. The implication from this hypothesis to the local one is proved
(`toLp_mul_mem_closedWeightedOperator_domain`); no strictness is claimed. It is recorded because
it is the shape in which the statement usually appears. -/
theorem exists_seq_smooth_tendsto_adjointComp_of_mem_domain
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (hreg : ∀ u : (Lp ℝ 2 (ν : Measure V)),
      (∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
        ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
          ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2
            (ν : Measure V))), u⟫ = 0) →
      u ∈ (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (F : ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
        - (F : (Lp ℝ 2 (ν : Measure V)))‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖((adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n)
          (hfnc n)⟩ : (Lp ℝ 2 (ν : Measure V))) - ((adjointComp
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
              (ν : Measure V)))‖) atTop (𝓝 0) :=
  exists_seq_smooth_tendsto_adjointComp_of_localRegularity m hν hi hνU hU
    (fun u horth _χ hχ hχc => hν.toLp_mul_mem_closedWeightedOperator_domain m
      (ContinuousLinearMap.id ℝ V) hi hχ hχc ⟨u, hreg u horth⟩) F

end Criterion

end FunctionalInequalities.KLS.LogConcave
