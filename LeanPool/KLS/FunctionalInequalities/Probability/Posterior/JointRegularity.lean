/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.Exponent
public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.CompactPrior
public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.Generator
public import LeanPool.KLS.FunctionalInequalities.Probability.Posterior.CompactDomain
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Joint regularity of the compact posterior in `(c, Q)`

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19, (67), compact-prior stage. The posterior expectation
`(c, Q) ↦ ∫ f dμ_{c,Q}` of a measurable `f` bounded on the prior support is `C^∞` jointly in the
parameter
pair `p = (c, Q) ∈ E × (E →L[ℝ] E)` (product norm, operator norm on the second factor), for every
finite
pair including `Q = 0`, non-symmetric `Q` and dimension zero; hence so are the posterior mean and
the
posterior covariance operator. The proof linearises the exponent: the score `p ↦ ⟪c,x⟫ − ½⟪Qx,x⟫` is
continuous linear in `p`, so after a finite-dimensional chart it is the pairing with a Riesz feature
`ψ(x)`, and the joint expectation is the `c`-only expectation (`Generator.lean`) of the
pushed-forward
prior `ψ_*μ` at `Q' = 0`, composed with the chart; the chart is an implementation device and is
private.
Prior isotropy is not used here; the inverse covariance and the drift of (67) are in
`KLS/BKL/Posterior/Regularity.lean`. No stochastic process, SDE or Itô statement.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory FunctionalInequalities
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Probability.Posterior

section Chart

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Euclidean model of the parameter space (implementation device). -/
private abbrev parameterSpace := EuclideanSpace ℝ (Fin (Module.finrank ℝ (E × (E →L[ℝ] E))))

/-- Euclidean coordinates of the parameter space `E × (E →L[ℝ] E)`; the operator norm is kept on the
second factor (this is a linear chart, not a whitening). -/
private def parameterChart : (E × (E →L[ℝ] E)) ≃L[ℝ]
    parameterSpace E :=
  (Module.finBasis ℝ (E × (E →L[ℝ] E))).equivFunL.trans
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (Module.finrank ℝ (E × (E →L[ℝ] E))) => ℝ)).symm

/-- The exponent of (67) as a continuous linear functional of the parameter pair. -/
private def parameterScore (x : E) : (E × (E →L[ℝ] E)) →L[ℝ] ℝ :=
  (innerSL ℝ x).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)) -
    (1 / 2 : ℝ) • ((innerSL ℝ x).comp
      ((ContinuousLinearMap.apply ℝ E x).comp (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))))

section ParameterScores

omit [FiniteDimensional ℝ E]
private theorem parameterScore_apply (x : E) (p : E × (E →L[ℝ] E)) :
    parameterScore E x p = quadraticExponent p.1 p.2 x := by
  change ⟪x, p.1⟫ - (1 / 2 : ℝ) * ⟪x, p.2 x⟫ = quadraticExponent p.1 p.2 x
  simp only [quadraticExponent]
  rw [real_inner_comm x p.1, real_inner_comm x (p.2 x)]

private theorem continuous_parameterScore : Continuous (parameterScore E) := by
  have hi : Continuous (fun x : E => innerSL ℝ x) := (InnerProductSpace.toDualMap ℝ E).continuous
  have he : Continuous (fun x : E =>
      (ContinuousLinearMap.apply ℝ E x).comp (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))) :=
    (ContinuousLinearMap.apply ℝ E).continuous.clm_comp_const _
  exact (hi.clm_comp_const _).sub ((hi.clm_comp he).const_smul (1 / 2 : ℝ))

end ParameterScores

/-- Riesz representative of the score in the chart coordinates. -/
private def parameterFeature (x : E) :
    parameterSpace E :=
  (InnerProductSpace.toDual ℝ _).symm
    ((parameterScore E x).comp (parameterChart E).symm.toContinuousLinearMap)

private theorem continuous_parameterFeature : Continuous (parameterFeature E) :=
  (InnerProductSpace.toDual ℝ _).symm.continuous.comp
    ((continuous_parameterScore E).clm_comp_const (parameterChart E).symm.toContinuousLinearMap)

private theorem parameterFeature_pairing (p : E × (E →L[ℝ] E)) (x : E) :
    ⟪parameterChart E p, parameterFeature E x⟫ = quadraticExponent p.1 p.2 x := by
  rw [real_inner_comm]
  unfold parameterFeature
  rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply, parameterScore_apply]

private def parameterLinearBlock : E →L[ℝ]
    parameterSpace E :=
  (parameterChart E).toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E (E →L[ℝ] E))

/-- The adjoint of the `c`-block of the chart retracts the feature to the point. -/
private def parameterRetract :
    parameterSpace E →L[ℝ] E :=
  (parameterLinearBlock E).adjoint

private theorem parameterRetract_feature (x : E) :
    parameterRetract E (parameterFeature E x) = x := by
  apply ext_inner_left ℝ
  intro c
  rw [parameterRetract, ContinuousLinearMap.adjoint_inner_right]
  have h := parameterFeature_pairing E (c, 0) x
  simp only [quadraticExponent, zero_apply, inner_zero_left, mul_zero,
    sub_zero] at h
  change ⟪parameterChart E (c, 0), parameterFeature E x⟫ = ⟪c, x⟫
  convert! h using 1

end Chart

section Expectation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The prior pushed forward by the feature map (an internal device, not a new posterior object). -/
private def featureLaw (μ : ProbabilityMeasure E) :
    ProbabilityMeasure (parameterSpace E) :=
  -- The measurability witness stays referenced so that the definition keeps the section instances
  -- it used before `ProbabilityMeasure.map` began taking the function itself (Mathlib v4.35).
  have _hmeas := (continuous_parameterFeature E).measurable
  μ.map (parameterFeature E)

private theorem featureLaw_support_subset (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    (featureLaw μ : Measure (parameterSpace E)).support ⊆
      parameterFeature E '' (μ : Measure E).support := by
  have hk : IsCompact (parameterFeature E '' (μ : Measure E).support) :=
    hc.image (continuous_parameterFeature E)
  have ha :
    parameterFeature E '' (μ : Measure E).support ∈
      ae (featureLaw μ : Measure (parameterSpace E)) := by
    rw [mem_ae_iff]
    change
      ((μ : Measure E).map (parameterFeature E))
          (parameterFeature E '' (μ : Measure E).support)ᶜ =
        0
    rw [Measure.map_apply (continuous_parameterFeature E).measurable
        hk.isClosed.measurableSet.compl]
    apply measure_mono_null ?_ (μ : Measure E).measure_compl_support
    intro x hx hxS
    exact hx ⟨x, hxS, rfl⟩
  exact Measure.support_subset_of_isClosed hk.isClosed ha

private theorem featureLaw_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    IsCompact (featureLaw μ : Measure (parameterSpace E)).support :=
  (hc.image (continuous_parameterFeature E)).of_isClosed_subset
    (featureLaw μ : Measure (parameterSpace E)).isClosed_support (featureLaw_support_subset μ hc)

private theorem feature_statistic_bound (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} {C : ℝ}
    (hb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) :
    ∀ y ∈ (featureLaw μ : Measure (parameterSpace E)).support,
      ‖(f ∘ parameterRetract E) y‖ ≤ C := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := featureLaw_support_subset μ hc hy
  simpa only [Function.comp_apply, parameterRetract_feature] using hb x hx

/--
The joint posterior expectation is the `c`-only expectation of the feature law at `Q' = 0`, with
both the numerator and the normalising integral transported. -/
private theorem posteriorExpectation_feature (μ : ProbabilityMeasure E) {f : E → ℝ}
    (hf : Measurable f) (p : E × (E →L[ℝ] E)) :
    posteriorExpectation μ p.1 p.2 f =
      posteriorExpectation (featureLaw μ) (parameterChart E p) 0 (f ∘ parameterRetract E) := by
  have hphase (x : E) :
    quadraticExponent (parameterChart E p) (0 : _ →L[ℝ] _) (parameterFeature E x) =
      quadraticExponent p.1 p.2 x := by
    simpa only [quadraticExponent, zero_apply, inner_zero_left, mul_zero, sub_zero] using
      parameterFeature_pairing E p x
  have hp : Continuous (quadraticExponent (parameterChart E p) (0 : _ →L[ℝ] _)) := by
    unfold quadraticExponent
    fun_prop
  have hf' : Measurable (f ∘ parameterRetract E) :=
    hf.comp (parameterRetract E).continuous.measurable
  have hN :
    (∫ y,
        Real.exp (quadraticExponent (parameterChart E p) 0 y) *
          (f ∘ parameterRetract E) y ∂(featureLaw μ : Measure (parameterSpace E))) =
      ∫ x, Real.exp (quadraticExponent p.1 p.2 x) * f x ∂(μ : Measure E) := by
    have h :=
      integral_map (μ := (μ : Measure E))
        (continuous_parameterFeature E).measurable.aemeasurable
        (hp.measurable.exp.mul hf').aestronglyMeasurable
    simpa only [featureLaw, ProbabilityMeasure.toMeasure_map, Function.comp_apply, Pi.mul_apply,
      hphase, parameterRetract_feature] using h
  have hZ :
    (∫ y,
        Real.exp
          (quadraticExponent (parameterChart E p) 0
            y) ∂(featureLaw μ : Measure (parameterSpace E))) =
      ∫ x, Real.exp (quadraticExponent p.1 p.2 x) ∂(μ : Measure E) := by
    have h :=
      integral_map (μ := (μ : Measure E))
        (continuous_parameterFeature E).measurable.aemeasurable
        hp.measurable.exp.aestronglyMeasurable
    simpa only [featureLaw, ProbabilityMeasure.toMeasure_map, hphase] using h
  unfold posteriorExpectation
  rw [integral_tilted_eq_div μ, integral_tilted_eq_div (featureLaw μ), hN, hZ]

/-- **Joint smoothness of the posterior expectation** (BKL (67), compact stage): for a compactly
supported prior and a measurable `f` bounded on the prior support, `(c, Q) ↦ ∫ f dμ_{c,Q}` is `C^∞`
on
`E × (E →L[ℝ] E)`; every finite pair, including `Q = 0`, non-symmetric `Q` and dimension zero. `f`
may be
discontinuous or unbounded off the support. -/
theorem contDiff_posteriorExpectation_joint (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => posteriorExpectation μ p.1 p.2 f) := by
  have hbound :
    ∀ y ∈ (featureLaw μ : Measure (parameterSpace E)).support,
      ‖(f ∘ parameterRetract E) y‖ ≤ max C 0 := by
    intro y hy
    exact (feature_statistic_bound μ hc hb y hy).trans (le_max_left C 0)
  have hsm :=
    contDiff_posteriorExpectation_c (featureLaw μ) (featureLaw_compact μ hc)
      (hf.comp (parameterRetract E).continuous.measurable) (le_max_right C 0) hbound
      (0 : _ →L[ℝ] _)
  have hcom := hsm.comp (parameterChart E).contDiff
  have he :
    (fun p : E × (E →L[ℝ] E) => posteriorExpectation μ p.1 p.2 f) =
      (fun c => posteriorExpectation (featureLaw μ) c 0 (f ∘ parameterRetract E)) ∘
        parameterChart E := by
    funext p
    exact posteriorExpectation_feature μ hf p
  rw [he]
  exact hcom

/--
A continuous statistic is bounded on the compact support, so its posterior expectation is jointly
`C^∞`. -/
theorem contDiff_posteriorExpectation_joint_of_continuous (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {g : E → ℝ} (hg : Continuous g) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => posteriorExpectation μ p.1 p.2 g) := by
  obtain ⟨C, _hC, hb⟩ := exists_bound_on_support_of_compact μ hc hg
  exact contDiff_posteriorExpectation_joint μ hc hg.measurable hb

end Expectation

section Moments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/--
The posterior mean `a(c,Q) = ∫ x dμ_{c,Q}` is jointly `C^∞` (reconstructed from its coordinates in
an
orthonormal basis). -/
theorem contDiff_posteriorMean_joint (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) => posteriorMean μ p.1 p.2) := by
  let b := stdOrthonormalBasis ℝ E
  have hs (i : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞
      (fun p : E × (E →L[ℝ] E) => posteriorExpectation μ p.1 p.2 (fun x => ⟪b i, x⟫)) :=
    contDiff_posteriorExpectation_joint_of_continuous μ hc (by fun_prop)
  have hm :
    ContDiff ℝ ∞
      (fun p : E × (E →L[ℝ] E) =>
        ∑ i, posteriorExpectation μ p.1 p.2 (fun x => ⟪b i, x⟫) • b i) :=
    ContDiff.sum (fun i _hi => (hs i).smul contDiff_const)
  have he :
    (fun p : E × (E →L[ℝ] E) => posteriorMean μ p.1 p.2) = fun p =>
      ∑ i, posteriorExpectation μ p.1 p.2 (fun x => ⟪b i, x⟫) • b i := by
    funext p
    rw [← b.sum_repr' (posteriorMean μ p.1 p.2)]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← integral_inner_eq_inner_posteriorMean μ hc p.1 p.2 (b i)]
    rfl
  rw [he]
  exact hm

/--
Covariances of two linear statistics under the posterior are jointly `C^∞` (polynomial moments of
the compact posterior). -/
theorem contDiff_covariance_pair_joint (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (u v : E) :
    ContDiff ℝ ∞
      (fun p : E × (E →L[ℝ] E) =>
        covariance (fun x => ⟪u, x⟫) (fun x => ⟪v, x⟫)
          ((μ : Measure E).tilted (quadraticExponent p.1 p.2))) := by
  have hs :=
    contDiff_posteriorExpectation_joint_of_continuous μ hc (g := fun x => ⟪u, x⟫ * ⟪v, x⟫)
      (by fun_prop)
  have hu :=
    contDiff_posteriorExpectation_joint_of_continuous μ hc (g := fun x => ⟪u, x⟫) (by fun_prop)
  have hv :=
    contDiff_posteriorExpectation_joint_of_continuous μ hc (g := fun x => ⟪v, x⟫) (by fun_prop)
  have he :
    (fun p : E × (E →L[ℝ] E) =>
        covariance (fun x => ⟪u, x⟫) (fun x => ⟪v, x⟫)
          ((μ : Measure E).tilted (quadraticExponent p.1 p.2))) =
      (fun p => posteriorExpectation μ p.1 p.2 (fun x => ⟪u, x⟫ * ⟪v, x⟫)) -
        (fun p => posteriorExpectation μ p.1 p.2 (fun x => ⟪u, x⟫)) *
          (fun p => posteriorExpectation μ p.1 p.2 (fun x => ⟪v, x⟫)) := by
    funext p
    let : IsProbabilityMeasure ((μ : Measure E).tilted (quadraticExponent p.1 p.2)) :=
      isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc p.1 p.2
    rw [covariance_eq_sub
        (memLp_two_tilted_quadraticExponent_of_compact μ hc p.1 p.2
          (by fun_prop : Continuous (fun x => ⟪u, x⟫)))
        (memLp_two_tilted_quadraticExponent_of_compact μ hc p.1 p.2
          (by fun_prop : Continuous (fun x => ⟪v, x⟫)))]
    rfl
  rw [he]
  exact hs.sub (hu.mul hv)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- An operator is the sum of its matrix entries times rank-one operators in a finite orthonormal
basis. -/
private theorem operator_eq_sum_rankOne {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (A : E →L[ℝ] E) :
    A = ∑ j, ∑ i, ⟪b i, A (b j)⟫ • InnerProductSpace.rankOne ℝ (b i) (b j) := by
  apply ContinuousLinearMap.ext
  intro x
  conv_lhs => rw [← b.sum_repr' x]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    InnerProductSpace.rankOne_apply, smul_smul]
  apply Finset.sum_congr rfl
  intro j _hj
  conv_lhs => rw [← b.sum_repr' (A (b j)), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [smul_smul]
  congr 1
  ring

/--
**Joint smoothness of the posterior covariance** `A(c,Q) = Cov(μ_{c,Q})` on `E × (E →L[ℝ] E)`, in
the
operator norm; no isotropy or symmetry of `Q` is needed. -/
theorem contDiff_posteriorCovariance_joint (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    ContDiff ℝ ∞
      (fun p : E × (E →L[ℝ] E) =>
        Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E)) := by
  let b := stdOrthonormalBasis ℝ E
  have he (p : E × (E →L[ℝ] E)) (i j : Fin (Module.finrank ℝ E)) :
    ⟪b i, Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E) (b j)⟫ =
      covariance (fun x => ⟪b j, x⟫) (fun x => ⟪b i, x⟫)
        ((μ : Measure E).tilted (quadraticExponent p.1 p.2)) := by
    rw [real_inner_comm, Covariance.operator_inner,
      covarianceBilin_apply_eq_cov (compactPosterior_memLp_id_two μ hc p.1 p.2)]
    rfl
  have hs :
    ContDiff ℝ ∞
      (fun p : E × (E →L[ℝ] E) =>
        ∑ j,
          ∑ i,
            covariance (fun x => ⟪b j, x⟫) (fun x => ⟪b i, x⟫)
                ((μ : Measure E).tilted (quadraticExponent p.1 p.2)) •
              InnerProductSpace.rankOne ℝ (b i) (b j)) :=
    ContDiff.sum
      (fun j _hj =>
        ContDiff.sum
          (fun i _hi => (contDiff_covariance_pair_joint μ hc (b j) (b i)).smul contDiff_const))
  have hfun :
    (fun p : E × (E →L[ℝ] E) =>
        Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E)) =
      fun p =>
      ∑ j,
        ∑ i,
          covariance (fun x => ⟪b j, x⟫) (fun x => ⟪b i, x⟫)
              ((μ : Measure E).tilted (quadraticExponent p.1 p.2)) •
            InnerProductSpace.rankOne ℝ (b i) (b j) := by
    funext p
    rw [operator_eq_sum_rankOne b
        (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))]
    simp only [he]
  rw [hfun]
  exact hs

end Moments

end FunctionalInequalities.Probability.Posterior
