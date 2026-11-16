/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.AdjointClosure

/-!
# The generator on smooth compactly supported tests: `Tbar†Tbar f = -ℒ f`

Weighted integration by parts and the smooth-test generator identity of Bakry–Émery, for the
smooth-potential model with unit weight. Let `ν` be a full-dimensional log-concave probability law
on a finite-dimensional Euclidean space `V` whose measure is the tilted Haar measure
`m.tilted (-U)` for a `C¹` potential `U`, and let

`Tbar = hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi`

be the closed unit-weight gradient, so that the heat semigroup is `P_t = exp (-t Tbar†Tbar)`. For
`f ∈ C_c^∞(V)` and the weighted Laplacian `ℒ f = Δ f - ⟪∇U, ∇f⟫`
(`Analysis.BakryEmery.weightedLaplacian`):

* weighted integration by parts: `∫ ⟪∇f, ∇g⟫ dν = ∫ (-ℒf) g dν` for every `C¹` function `g`
  (`integral_inner_gradient_eq`);
* the smooth-test generator identity: `-ℒ f ∈ L²(ν)`, `[f] ∈ D(Tbar†Tbar)` and
`Tbar†Tbar [f] = [-ℒ f]`
  (`memLp_neg_weightedLaplacian`, `toLp_mem_adjointComp_domain`, `adjointComp_toLp_eq`).

The proof of the smooth-test generator identity goes through the adjoint, not through a pointwise
computation. The weak identity
`⟪[-ℒf], [g]⟫ = ⟪[∇f], [∇g]⟫` is weighted integration by parts on smooth compactly supported `g`; by
`closure_domRestrict_eq_of_smoothCore_le` these classes are a graph-norm core of `Tbar`, and
`Analysis.Semigroup.inner_eq_inner_closure_apply` extends the identity to every `x ∈ D(Tbar)`. Then
`[∇f] = Tbar [f]` lies in `D(Tbar†)` with `Tbar† [∇f] = [-ℒf]` (`LinearPMap.adjoint_apply_eq`,
using the
dense domain), which is exactly membership in `D(Tbar†Tbar)` and the value of `adjointComp`.

## What this is not

These are statements about individual test functions. They do **not** say that `C_c^∞(V)` is an
operator core of `Tbar†Tbar` (density in the graph norm of `Tbar†Tbar`), nor that the closure of
`-ℒ` on
`C_c^∞` equals `Tbar†Tbar`. No
`Γ`, `Γ₂`, Bochner or gradient estimate, no statement about `P_t f` for `t > 0`, and no Buser
inequality is made. The hypothesis `(ν : Measure V) = m.tilted (-U)` is an explicit premise: it is
not derived here from log-concavity, and no convexity of `U` is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities.Analysis.Semigroup
  FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff LinearPMap RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

open Energy Energy.WeightedGradient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

section Tilted

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)

include hνU hU in
omit [SecondCountableTopology V] in
/--
**weighted integration by parts, weighted integration by parts for the law `ν = m.tilted (-U)`**:
for a `C²` compactly
supported `f` and a `C¹` function `g`, `∫ ⟪∇f, ∇g⟫ dν = ∫ (-ℒf) g dν`. -/
theorem integral_inner_gradient_eq {f g : V → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 1 g) :
    ∫ x, ⟪gradient f x, gradient g x⟫ ∂(ν : Measure V) =
      ∫ x, -weightedLaplacian U f x * g x ∂(ν : Measure V) := by
  rw [hνU]
  exact integral_inner_gradient_tilted m hU hf hfc hg

include hνU hU in
omit [SecondCountableTopology V] in
/--
The weighted Laplacian has zero mean: `∫ ℒf dν = 0` for `C²` compactly supported `f`. This is
weighted integration by parts against the constant test `g = 1`, and it is the infinitesimal form of
the conservation of
integrals by the heat semigroup (`HeatSemigroup.integral`). -/
theorem integral_weightedLaplacian_eq_zero {f : V → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : ∫ x, weightedLaplacian U f x ∂(ν : Measure V) = 0 := by
  have h := integral_inner_gradient_eq m hνU hU hf hfc (contDiff_const (c := (1 : ℝ)))
  simp only [gradient_fun_const, inner_zero_right, integral_zero, mul_one, integral_neg] at h
  exact (neg_eq_zero.mp h.symm)

end Tilted

section Generator

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)

omit [FiniteDimensional ℝ V] in
/-- The gradient of a smooth compactly supported function is square integrable for every
probability law. -/
theorem memLp_gradient_of_contDiff_hasCompactSupport {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) : MemLp (gradient f) 2 (ν : Measure V) := by
  simpa only [apply_id] using
    (IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hf hfc).memLp_apply

omit [SecondCountableTopology V] in
/--
`-ℒ f ∈ L²(ν)` for `f ∈ C_c^∞(V)` and a `C¹` potential: the integrability clause of the smooth-test
generator identity. -/
theorem memLp_neg_weightedLaplacian (hU : ContDiff ℝ 1 U) {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) : MemLp (fun x => -weightedLaplacian U f x) 2 (ν : Measure V) :=
  (memLp_weightedLaplacian hU (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hfc 2).neg

/-- The class of a smooth compactly supported function lies in the domain of the closed
unit-weight gradient. -/
theorem toLp_mem_closedWeightedOperator_domain {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    (memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :=
  (LinearPMap.le_closure _).1
    (toLp_mem_domain_operator ν (ContinuousLinearMap.id ℝ V) _
      (IsTest.of_contDiff_hasCompactSupport ν _ hf hfc))

/-- The closed unit-weight gradient sends the class of a smooth compactly supported function to
the class of its gradient. -/
theorem closedWeightedOperator_toLp_eq {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩ =
      (memLp_gradient_of_contDiff_hasCompactSupport hf hfc).toLp (gradient f) := by
  have htest := IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hf hfc
  have hmem := toLp_mem_domain_operator ν (ContinuousLinearMap.id ℝ V)
    (hν.absolutelyContinuous_haar m hi) htest
  rw [← (LinearPMap.le_closure (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi)).2
    (x := ⟨_, hmem⟩) (y := ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩) rfl,
    operator_apply ν (ContinuousLinearMap.id ℝ V) _ (hν.frontier_support_eq_zero hi) htest hmem rfl]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun y => by rw [apply_id])

include hνU hU in
/-- **The weak identity on the domain of `Tbar`**: for `f ∈ C_c^∞(V)` and every `x ∈ D(Tbar)`,
`⟪[-ℒf], x⟫ = ⟪[∇f], Tbar x⟫` in `L²(ν)`. On smooth compactly supported classes this is weighted
integration by parts; it
extends to `D(Tbar)` because those classes are a graph-norm core of `Tbar`. -/
theorem inner_toLp_neg_weightedLaplacian_eq {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f)
    (x : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    ⟪(memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).toLp (fun y => -weightedLaplacian U f y),
        (x : Lp ℝ 2 (ν : Measure V))⟫ =
      ⟪(memLp_gradient_of_contDiff_hasCompactSupport hf hfc).toLp (gradient f),
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi x⟫ := by
  have hSclos :
    ((hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domRestrict
          (smoothCore ν)).closure =
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi :=
    hν.closure_domRestrict_eq_of_smoothCore_le m (ContinuousLinearMap.id ℝ V) hi le_rfl
      (smoothCore_le_domain_operator ν (ContinuousLinearMap.id ℝ V) _)
  have hSc :
    ((hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domRestrict
        (smoothCore ν)).IsClosable :=
    (hν.weightedOperator_isClosable m (ContinuousLinearMap.id ℝ V) hi).leIsClosable
      LinearPMap.domRestrict_le
  have hcore :
    ∀ y :
      ((hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domRestrict
          (smoothCore ν)).domain,
      ⟪(memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).toLp
            (fun y => -weightedLaplacian U f y),
          (y : Lp ℝ 2 (ν : Measure V))⟫ =
        ⟪(memLp_gradient_of_contDiff_hasCompactSupport hf hfc).toLp (gradient f),
          (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domRestrict (smoothCore ν)
            y⟫ := by
    rintro ⟨y, hy⟩
    have hy1 : y ∈ smoothCore ν := (Submodule.mem_inf.mp hy).1
    have hy2 : y ∈ (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :=
      (Submodule.mem_inf.mp hy).2
    obtain ⟨g, hg, hgc, rfl⟩ := hy1
    have htest := IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hg hgc
    have hSy :
      (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi).domRestrict (smoothCore ν)
          ⟨_, hy⟩ =
        htest.memLp_apply.toLp (apply (ContinuousLinearMap.id ℝ V) g) := by
      erw [LinearPMap.domRestrict_apply (x := ⟨_, hy⟩) (y := ⟨_, hy2⟩) rfl]
      exact
        operator_apply ν (ContinuousLinearMap.id ℝ V) _ (hν.frontier_support_eq_zero hi) htest
          hy2 rfl
    rw [hSy, L2.inner_def, L2.inner_def]
    have h1 :
      (fun a =>
          ⟪((memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).toLp
                  (fun y => -weightedLaplacian U f y) :
                Lp ℝ 2 (ν : Measure V))
              a,
            ((memLp_of_contDiff_hasCompactSupport ν hg hgc).toLp g : Lp ℝ 2 (ν : Measure V))
              a⟫) =ᵐ[(ν : Measure V)]
        fun a => -weightedLaplacian U f a * g a := by
      filter_upwards [(memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).coeFn_toLp,
        (memLp_of_contDiff_hasCompactSupport ν hg hgc).coeFn_toLp] with a ha hb
      rw [ha, hb, Real.inner_apply]
    have h2 :
      (fun a =>
          ⟪((memLp_gradient_of_contDiff_hasCompactSupport hf hfc).toLp (gradient f) :
                Lp V 2 (ν : Measure V))
              a,
            (htest.memLp_apply.toLp (apply (ContinuousLinearMap.id ℝ V) g) :
                Lp V 2 (ν : Measure V))
              a⟫) =ᵐ[(ν : Measure V)]
        fun a => ⟪gradient f a, gradient g a⟫ := by
      filter_upwards [(memLp_gradient_of_contDiff_hasCompactSupport hf hfc).coeFn_toLp,
        htest.memLp_apply.coeFn_toLp] with a ha hb
      rw [ha, hb, apply_id]
    rw [integral_congr_ae h1, integral_congr_ae h2]
    exact
      (integral_inner_gradient_eq m hνU hU (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hfc
          (hg.of_le (WithTop.coe_le_coe.mpr le_top))).symm
  have := inner_eq_inner_closure_apply hSc hcore
  rw [hSclos] at this
  exact this x

include hνU hU in
/--
**the smooth-test generator identity, domain clause**: for `f ∈ C_c^∞(V)`, the class `[f]` lies in
`D(Tbar†Tbar)`. -/
theorem toLp_mem_adjointComp_domain {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    (memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f ∈
      (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain := by
  have hD := hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc
  refine ⟨mem_adjointCompDomain.mpr ⟨hD, ?_⟩, hD⟩
  rw [hν.closedWeightedOperator_toLp_eq m hi hf hfc]
  exact
    LinearPMap.mem_adjoint_domain_of_exists _
      ⟨_, fun x => hν.inner_toLp_neg_weightedLaplacian_eq m hi hνU hU hf hfc x⟩

include hνU hU in
/--
**the smooth-test generator identity, value clause**: for `f ∈ C_c^∞(V)`, `Tbar†Tbar [f] = [-ℒ f]`
with
`ℒ f = Δ f - ⟪∇U, ∇f⟫`.
The generator of the heat semigroup `P_t = exp (-t Tbar†Tbar)` is therefore `ℒ` on smooth compactly
supported tests: `d/dt P_t f |_{t=0} = ℒ f`. -/
theorem adjointComp_toLp_eq {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨(memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f,
          hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ =
      (memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).toLp
        (fun x => -weightedLaplacian U f x) := by
  rw [adjointComp_apply]
  refine
    LinearPMap.adjoint_apply_eq
      (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) _ fun x => ?_
  rw [hν.inner_toLp_neg_weightedLaplacian_eq m hi hνU hU hf hfc x]
  congr 1
  exact (hν.closedWeightedOperator_toLp_eq m hi hf hfc).symm

end Generator

end FunctionalInequalities.KLS.LogConcave
