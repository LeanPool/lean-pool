/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.InteriorRegularity
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Bochner.Temperate
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.Tilted

/-!
# The weak Hessian on the generator domain and the curvature form of (16)

The weak Hessian estimate (Bizeul–Klartag–Lehec, arXiv:2610.05474v1,
eq. (16) and its use in Lemma 3.4), for the heat
model with unit weight. Let `ν = m.tilted (-U)` be a full-dimensional log-concave probability law
whose potential `U` has temperate growth and all exponential moments, let
`Tbar = hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi` be the closed gradient and
`A = Tbar†Tbar = -ℒ`, and let `eᵢ = stdOrthonormalBasis ℝ V i`. For `F ∈ D(A)`:

* `compLp_innerSL_mem_closedWeightedOperator_domain`: every weak first derivative
  `∂ᵢ F = ⟪eᵢ, Tbar F⟫` lies in `D(Tbar)`;
* `compLp_innerSL_closedWeightedOperator_comm`: the weak Hessian `⟪eⱼ, Tbar ∂ᵢ F⟫` is symmetric
  in `i, j`;
* `sum_norm_sq_closedWeightedOperator_add_le`: if `∇²U ≥ ρ` (any real `ρ`), then
  `Σᵢ ‖Tbar ∂ᵢ F‖² + ρ ‖Tbar F‖² ≤ ‖A F‖²`, the curvature form of (16) on `D(A)`.

## The argument

`C_c^∞(V)` is an operator core of `A` (`exists_seq_smooth_tendsto_adjointComp`): there are
`fₙ ∈ C_c^∞` with `[fₙ] → F` and `A [fₙ] → A F`. Since `‖Tbar u‖² = ⟪A u, u⟫` on `D(A)`, also
`Tbar [fₙ] → Tbar F`. For smooth compactly supported `f` the integrated Bochner inequality on the class
`𝒜` (`integral_hessianSq_add_le_of_hasTemperateGrowth`) reads, in `L²` norms,
`Σᵢ ‖Tbar [∂ᵢ f]‖² + ρ ‖Tbar [f]‖² ≤ ‖A [f]‖²`, because `Σᵢ ‖∇∂ᵢ f‖² = Σᵢ Σⱼ (∇²f(eᵢ, eⱼ))²`.
Applied to `fₙ - fₖ`, it shows that `Tbar [∂ᵢ fₙ]` is Cauchy, while
`[∂ᵢ fₙ] = ⟪eᵢ, Tbar [fₙ]⟫ → ⟪eᵢ, Tbar F⟫`; closedness of `Tbar` gives `⟪eᵢ, Tbar F⟫ ∈ D(Tbar)` with
`Tbar ⟪eᵢ, Tbar F⟫ = lim Tbar [∂ᵢ fₙ]`. Symmetry and the inequality pass to the limit from the
pointwise symmetry of second derivatives and the smooth inequality.

The membership statement assumes no curvature bound. The Cauchy step uses `∇²U ≥ 0`, which is
derived here from log-concavity: the continuous density `e^{-U} / Z` agrees `m`-a.e. with the
log-concave Borell representative of `ν`, which is continuous because `ν` has full support, so
the two agree everywhere and `U` is convex (`convexOn_of_eq_tilted`, `Density/Tilted.lean`).

## What this is not

No regularity of `F` beyond `D(A)` is claimed: the weak Hessian is the `L²` object
`Tbar ⟪eᵢ, Tbar F⟫`, not a classical second derivative, and nothing is said about the class `𝒜` or
Lemma 2.1 on `𝒜`. The Hessian square is taken in the fixed standard orthonormal basis; basis
independence and the identity form of (16) on `D(A)` are outside this module's statements.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

open Energy Energy.WeightedGradient

/-! ### Directional derivatives of smooth functions -/

section Partial

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A directional derivative of a smooth function is smooth. -/
private theorem contDiff_fderiv_apply_infty {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (v : V) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ f y v) :=
  ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const

variable [CompleteSpace V] [FiniteDimensional ℝ V]

/-- `Σᵢ ‖∇ (∂ᵢ f)(x)‖² = Σᵢ Σⱼ (∇²f(x)(eᵢ, eⱼ))²` in the standard orthonormal basis. -/
private theorem sum_norm_gradient_fderiv_apply_sq {f : V → ℝ} (hf : ContDiff ℝ 2 f) (x : V) :
    ∑ i, ‖gradient (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ V i)) x‖ ^ 2 =
      hessianSqStdBasis f x := by
  rw [hessianSqStdBasis_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_gradient_sq_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hf]

end Partial

/-- A real sequence of nonnegative numbers whose squares tend to zero tends to zero. -/
private theorem tendsto_zero_of_sq {α : Type*} {l : Filter α} {u : α → ℝ} (h0 : ∀ a, 0 ≤ u a)
    (h : Tendsto (fun a => u a ^ 2) l (𝓝 0)) : Tendsto u l (𝓝 0) := by
  have h' := (Real.continuous_sqrt.tendsto 0).comp h
  simpa [Function.comp_def, Real.sqrt_sq (h0 _)] using h'

/-- `x ≤ a - ρ b` and `0 ≤ b` give `x ≤ a + |ρ| b`. -/
private theorem le_add_abs_mul_of_le_sub {x a b ρ : ℝ} (h : x ≤ a - ρ * b) (hb : 0 ≤ b) :
    x ≤ a + |ρ| * b := by
  nlinarith [neg_abs_le ρ]

/-! ### The weak Hessian -/

section Hessian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- `Tbar [f]` depends only on the function `f`. -/
private theorem closedWeightedOperator_toLp_congr {f g : V → ℝ} (h : f = g)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) :
    hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩ =
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hg hgc⟩ := by
  subst h; rfl

/-- `Tbar [f - g] = Tbar [f] - Tbar [g]` on smooth compactly supported functions. -/
private theorem closedWeightedOperator_toLp_sub {f g : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi (hf.sub hg) (hfc.sub hgc)⟩ =
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩ -
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hg hgc⟩ := by
  rw [← LinearPMap.map_sub]
  congr 1

/-- `A [f - g] = A [f] - A [g]` on smooth compactly supported functions. -/
private theorem adjointComp_toLp_sub (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) {f g : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hf.sub hg) (hfc.sub hgc)⟩ =
      adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ -
        adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hg hgc⟩ := by
  rw [← LinearPMap.map_sub]
  congr 1

/-- `⟪v, Tbar [f]⟫ = [∂ᵥ f]` for smooth compactly supported `f`. -/
private theorem compLp_innerSL_closedWeightedOperator_toLp {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (v : V) :
    (innerSL ℝ v).compLp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩) =
      (memLp_of_contDiff_hasCompactSupport ν (contDiff_fderiv_apply_infty hf v)
        (hfc.fderiv_apply ℝ v)).toLp (fun y => fderiv ℝ f y v) := by
  rw [hν.closedWeightedOperator_toLp_eq m hi hf hfc]
  refine Lp.ext ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLp (innerSL ℝ v)
      ((memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) hf hfc).toLp (gradient f)),
    (memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) hf hfc).coeFn_toLp,
    (memLp_of_contDiff_hasCompactSupport ν (contDiff_fderiv_apply_infty hf v)
        (hfc.fderiv_apply ℝ v)).coeFn_toLp] with x h1 h2 h3
  rw [h1, h2, h3, innerSL_apply_apply, real_inner_comm, inner_gradient_left]

/-- The smooth curvature inequality in `L²` norms: for `f ∈ C_c^∞` and `∇²U ≥ ρ`,
`Σᵢ ‖Tbar [∂ᵢ f]‖² + ρ ‖Tbar [f]‖² ≤ ‖A [f]‖²`. -/
private theorem sum_norm_sq_add_le_of_smooth (hνU : (ν : Measure V) = m.tilted (-U))
    (hUt : U.HasTemperateGrowth) (hU : ContDiff ℝ 1 U)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∑ i, ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
          (contDiff_fderiv_apply_infty hf (stdOrthonormalBasis ℝ V i))
          (hfc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V i))⟩‖ ^ 2 +
      ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩‖ ^ 2 ≤
    ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩‖ ^ 2 := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hsum : ∑ i, ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
          (contDiff_fderiv_apply_infty hf (stdOrthonormalBasis ℝ V i))
          (hfc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V i))⟩‖ ^ 2 =
      ∫ x, hessianSqStdBasis f x ∂(ν : Measure V) := by
    have hmem : ∀ i, MemLp (gradient (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ V i))) 2
        (ν : Measure V) := fun i =>
      memLp_gradient_of_contDiff_hasCompactSupport
        (contDiff_fderiv_apply_infty hf _) (hfc.fderiv_apply ℝ _)
    calc _ = ∑ i, ∫ x, ‖gradient (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ V i)) x‖ ^ 2
          ∂(ν : Measure V) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hν.closedWeightedOperator_toLp_eq m hi (contDiff_fderiv_apply_infty hf _)
            (hfc.fderiv_apply ℝ _), L2.norm_toLp_sq]
      _ = ∫ x, ∑ i, ‖gradient (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ V i)) x‖ ^ 2
          ∂(ν : Measure V) :=
          (integral_finsetSum _ fun i _ =>
            (memLp_two_iff_integrable_sq_norm (hmem i).aestronglyMeasurable).1 (hmem i)).symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun x =>
          sum_norm_gradient_fderiv_apply_sq hf2 x)
  rw [hsum, hν.closedWeightedOperator_toLp_eq m hi hf hfc,
    hν.adjointComp_toLp_eq m hi hνU hU hf hfc, L2.norm_toLp_sq, L2.norm_toLp_sq]
  simp only [norm_neg, Real.norm_eq_abs, sq_abs]
  have hexp' : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-U)) :=
    hνU ▸ hexp
  rw [hνU]
  have h := integral_hessianSq_add_le_of_hasTemperateGrowth m hUt hexp'
    (hfc.hasTemperateGrowth hf) hH
  simpa only [Real.norm_eq_abs, sq_abs] using h

/-- The smooth curvature inequality on differences, for one direction `i`:
`‖Tbar [∂ᵢ f] - Tbar [∂ᵢ g]‖² ≤ ‖A [f] - A [g]‖² - ρ ‖Tbar [f] - Tbar [g]‖²`. -/
private theorem norm_sub_sq_le_of_smooth (hνU : (ν : Measure V) = m.tilted (-U))
    (hUt : U.HasTemperateGrowth) (hU : ContDiff ℝ 1 U)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) {f g : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (i : Fin (Module.finrank ℝ V)) :
    ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
            (contDiff_fderiv_apply_infty hf (stdOrthonormalBasis ℝ V i))
            (hfc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V i))⟩ -
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
            (contDiff_fderiv_apply_infty hg (stdOrthonormalBasis ℝ V i))
            (hgc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V i))⟩‖ ^ 2 ≤
      ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ -
          adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hg hgc⟩‖ ^ 2 -
        ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩ -
          hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hg hgc⟩‖ ^ 2 := by
  have hb := sum_norm_sq_add_le_of_smooth m hν hi hνU hUt hU hexp hH (hf.sub hg) (hfc.sub hgc)
  rw [closedWeightedOperator_toLp_sub m hν hi hf hfc hg hgc,
    adjointComp_toLp_sub m hν hi hνU hU hf hfc hg hgc] at hb
  have hpart : ∀ j, hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
          (contDiff_fderiv_apply_infty (hf.sub hg) (stdOrthonormalBasis ℝ V j))
          ((hfc.sub hgc).fderiv_apply ℝ (stdOrthonormalBasis ℝ V j))⟩ =
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
            (contDiff_fderiv_apply_infty hf (stdOrthonormalBasis ℝ V j))
            (hfc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V j))⟩ -
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
            (contDiff_fderiv_apply_infty hg (stdOrthonormalBasis ℝ V j))
            (hgc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V j))⟩ := fun j => by
    have hd1 := contDiff_fderiv_apply_infty hf (stdOrthonormalBasis ℝ V j)
    have hd2 := contDiff_fderiv_apply_infty hg (stdOrthonormalBasis ℝ V j)
    have hf1 : Differentiable ℝ f := hf.differentiable (by simp)
    have hg1 : Differentiable ℝ g := hg.differentiable (by simp)
    refine (closedWeightedOperator_toLp_congr m hν hi (funext fun y =>
      fderiv_sub_apply (hf1 y) (hg1 y) (stdOrthonormalBasis ℝ V j))
      (contDiff_fderiv_apply_infty (hf.sub hg) _) ((hfc.sub hgc).fderiv_apply ℝ _) (hd1.sub hd2)
      ((hfc.fderiv_apply ℝ _).sub (hgc.fderiv_apply ℝ _))).trans ?_
    exact closedWeightedOperator_toLp_sub m hν hi hd1 (hfc.fderiv_apply ℝ _) hd2
      (hgc.fderiv_apply ℝ _)
  rw [Finset.sum_congr rfl fun j _ => by rw [hpart j]] at hb
  have hle := Finset.single_le_sum (f := fun j => ‖hν.closedWeightedOperator m
      (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
            (contDiff_fderiv_apply_infty hf (stdOrthonormalBasis ℝ V j))
            (hfc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V j))⟩ -
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
            (contDiff_fderiv_apply_infty hg (stdOrthonormalBasis ℝ V j))
            (hgc.fderiv_apply ℝ (stdOrthonormalBasis ℝ V j))⟩‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

/--
**The approximation behind the weak Hessian estimate.** For `F ∈ D(A)` there are `fₙ ∈ C_c^∞` with
`Tbar [fₙ] → Tbar F`, `A [fₙ] → A F`, and, for every `i`, `⟪eᵢ, Tbar F⟫ ∈ D(Tbar)` with
`Tbar [∂ᵢ fₙ] → Tbar ⟪eᵢ, Tbar F⟫`. -/
private theorem exists_seq_smooth_tendsto_weakHessian (hνU : (ν : Measure V) = m.tilted (-U))
    (hUt : U.HasTemperateGrowth) (hU : ContDiff ℝ 1 U)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n)) (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto
          (fun n =>
            hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi (hfn n) (hfnc n)⟩)
          atTop
          (𝓝
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) ∧
        Tendsto
            (fun n =>
              adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
                ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩)
            atTop
            (𝓝 (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) ∧
          ∀ i,
            ∃ h :
              (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
                  (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                    ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
                (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
              Tendsto
                (fun n =>
                  hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                    ⟨_,
                      hν.toLp_mem_closedWeightedOperator_domain m hi
                        (contDiff_fderiv_apply_infty (hfn n) (stdOrthonormalBasis ℝ V i))
                        ((hfnc n).fderiv_apply ℝ (stdOrthonormalBasis ℝ V i))⟩)
                atTop
                (𝓝 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, h⟩)) := by
  obtain ⟨fn, hfn, hfnc, h1, h2⟩ := hν.exists_seq_smooth_tendsto_adjointComp m hi hνU hU F
  have hTF :
    Tendsto
      (fun n =>
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi (hfn n) (hfnc n)⟩)
      atTop
      (𝓝
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) :=
    tendsto_apply_of_tendsto_adjointComp
      (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (x := fun n =>
      ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩)
      (tendsto_iff_norm_sub_tendsto_zero.2 h1) (tendsto_iff_norm_sub_tendsto_zero.2 h2)
  have hAF :
    Tendsto
      (fun n =>
        adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩)
      atTop (𝓝 (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 h2
  refine ⟨fn, hfn, hfnc, hTF, hAF, fun i => ?_⟩
  have hdf : ∀ n, ContDiff ℝ ∞ (fun y => fderiv ℝ (fn n) y (stdOrthonormalBasis ℝ V i)) :=
    fun n => contDiff_fderiv_apply_infty (hfn n) _
  have hdfc : ∀ n, HasCompactSupport (fun y => fderiv ℝ (fn n) y (stdOrthonormalBasis ℝ V i)) :=
    fun n => (hfnc n).fderiv_apply ℝ _
  have hx :
    ∀ n,
      (memLp_of_contDiff_hasCompactSupport ν (hdf n) (hdfc n)).toLp _ ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :=
    fun n => hν.toLp_mem_closedWeightedOperator_domain m hi (hdf n) (hdfc n)
  have hxa :
    Tendsto (fun n => (memLp_of_contDiff_hasCompactSupport ν (hdf n) (hdfc n)).toLp _) atTop
      (𝓝
        ((innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩))) := by
    have hc :=
      ((((innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLpL 2 (ν : Measure V))).continuous.tendsto
            _).comp
        hTF
    refine hc.congr fun n => ?_
    exact compLp_innerSL_closedWeightedOperator_toLp m hν hi (hfn n) (hfnc n) _
  have hcau :
    CauchySeq
      (fun n => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hx n⟩) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have hA2 := cauchySeq_iff_tendsto_dist_atTop_0.mp hAF.cauchySeq
    have hT2 := cauchySeq_iff_tendsto_dist_atTop_0.mp hTF.cauchySeq
    have hR := (hA2.pow 2).add ((hT2.pow 2).const_mul |ρ|)
    rw [zero_pow two_ne_zero, mul_zero, add_zero] at hR
    refine
      tendsto_zero_of_sq (fun _ => dist_nonneg)
        (squeeze_zero (fun _ => sq_nonneg _) (fun p => ?_) hR)
    simp only [dist_eq_norm]
    exact
      le_add_abs_mul_of_le_sub
        (norm_sub_sq_le_of_smooth m hν hi hνU hUt hU hexp hH (hfn p.1) (hfnc p.1) (hfn p.2)
          (hfnc p.2) i)
        (sq_nonneg _)
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcau
  obtain ⟨hmem, hTG⟩ :=
    exists_mem_domain_apply_eq_of_tendsto
      (hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi) hx hxa hG
  exact ⟨hmem, hTG ▸ hG⟩

omit [CompleteSpace V] in
include hν in
/-- The curvature bound `∇²U ≥ 0` of a log-concave tilted law with a `C²` potential. -/
private theorem zero_mul_le_bilinearIteratedFDerivTwo (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 2 U) (x v : V) :
    0 * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v := by
  rw [zero_mul]
  exact bilinearIteratedFDerivTwo_nonneg_of_convexOn hU
    (convexOn_of_eq_tilted m hν hνU hU.continuous) x v

/--
**the weak Hessian estimate, weak first derivatives in the form domain.** For `ν = m.tilted (-U)`
log-concave,
with `U` of temperate growth and all exponential moments, and `F ∈ D(A)`, every weak first
derivative `∂ᵢ F = ⟪eᵢ, Tbar F⟫` (standard orthonormal basis) lies in `D(Tbar)`. No curvature bound
beyond the convexity of `U` implied by log-concavity is assumed. -/
theorem compLp_innerSL_mem_closedWeightedOperator_domain (hνU : (ν : Measure V) = m.tilted (-U))
    (hUt : U.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (i : Fin (Module.finrank ℝ V)) :
    (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := by
  have hU2 : ContDiff ℝ 2 U := hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨_, _, _, -, -, hD⟩ :=
    exists_seq_smooth_tendsto_weakHessian m hν hi hνU hUt (hU2.of_le (by norm_num)) hexp
      (zero_mul_le_bilinearIteratedFDerivTwo m hν hνU hU2) F
  exact (hD i).1

/-- **the weak Hessian estimate, symmetry of the weak Hessian.** Under the hypotheses of
`compLp_innerSL_mem_closedWeightedOperator_domain`, `⟪eⱼ, Tbar ∂ᵢ F⟫ = ⟪eᵢ, Tbar ∂ⱼ F⟫` in `L²(ν)`. -/
theorem compLp_innerSL_closedWeightedOperator_comm
    (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hD : ∀ i, (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (i j : Fin (Module.finrank ℝ V)) :
    (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD i⟩) =
      (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD j⟩) := by
  have hU2 : ContDiff ℝ 2 U := hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨fn, hfn, hfnc, -, -, hlim⟩ := exists_seq_smooth_tendsto_weakHessian m hν hi hνU hUt
    (hU2.of_le (by norm_num)) hexp (zero_mul_le_bilinearIteratedFDerivTwo m hν hνU hU2) F
  have hc : ∀ (k : Fin (Module.finrank ℝ V)) {a : Lp V 2 (ν : Measure V)}
      {s : ℕ → Lp V 2 (ν : Measure V)}, Tendsto s atTop (𝓝 a) →
      Tendsto (fun n => (innerSL ℝ (stdOrthonormalBasis ℝ V k)).compLp (s n)) atTop
        (𝓝 ((innerSL ℝ (stdOrthonormalBasis ℝ V k)).compLp a)) := fun k a _ hs =>
    ((((innerSL ℝ (stdOrthonormalBasis ℝ V k)).compLpL 2
      (ν : Measure V))).continuous.tendsto a).comp hs
  have h1 := hc j (hlim i).2
  have h2 := hc i (hlim j).2
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  have hf2 : ContDiff ℝ 2 (fn n) := (hfn n).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [compLp_innerSL_closedWeightedOperator_toLp m hν hi
      (contDiff_fderiv_apply_infty (hfn n) _) ((hfnc n).fderiv_apply ℝ _),
    compLp_innerSL_closedWeightedOperator_toLp m hν hi
      (contDiff_fderiv_apply_infty (hfn n) _) ((hfnc n).fderiv_apply ℝ _)]
  exact MemLp.toLp_congr _ _ (Eventually.of_forall fun y =>
    fderiv_apply_comm hf2 y (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V j))

/-- **the weak Hessian estimate, the curvature form of BKL (16) on `D(A)`.** Under the hypotheses of
`compLp_innerSL_mem_closedWeightedOperator_domain`, if `∇²U ≥ ρ` for a real `ρ`, then
`Σᵢ ‖Tbar ∂ᵢ F‖² + ρ ‖Tbar F‖² ≤ ‖A F‖²`. -/
theorem sum_norm_sq_closedWeightedOperator_add_le
    (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hD : ∀ i, (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    ∑ i, ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD i⟩‖ ^ 2 +
        ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩‖ ^ 2 ≤
      ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F‖ ^ 2 := by
  have hU1 : ContDiff ℝ 1 U := hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨fn, hfn, hfnc, hTF, hAF, hlim⟩ :=
    exists_seq_smooth_tendsto_weakHessian m hν hi hνU hUt hU1 hexp hH F
  have hL := (tendsto_finsetSum Finset.univ fun i _ => ((hlim i).2.norm.pow 2)).add
    ((hTF.norm.pow 2).const_mul ρ)
  exact le_of_tendsto_of_tendsto' hL (hAF.norm.pow 2) fun n =>
    sum_norm_sq_add_le_of_smooth m hν hi hνU hUt hU1 hexp hH (hfn n) (hfnc n)

end Hessian

end FunctionalInequalities.KLS.LogConcave
