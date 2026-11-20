/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.Holder
public import LeanPool.FastDynamo.Analysis.WholePlaneFourier
public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Exterior cutoffs on whole-plane `L²`

Indicator multiplication by a measurable set is constructed on the `Lp` quotient
(`l2MeasurableSetRestriction`), and converges strongly to zero along every measurable exhaustion
whose exterior indicators tend pointwise to zero.  The specialization to complements of balls in
`ℝ²` gives the exterior cutoffs `wholePlaneExteriorCutoff`, which converge strongly to zero as
the radius tends to infinity.  Through their two-component form (`Local/WholePlaneC2.lean`)
they give the disc truncation of the compactly supported witness `f_*` in the proof of
`prop:local-seed` (`Local/HorizontalSeedWitness.lean`).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Metric MeasureTheory Set
open scoped ENNReal Topology

universe u v w x

section MeasurableCutoff

variable {X : Type u} [MeasurableSpace X]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The `L∞` class of the indicator of a measurable set.  Unlike
`indicatorConstLp`, this construction does not require the set to have finite
measure, which is essential for exterior regions. -/
def measurableSetIndicatorLInf (mu : Measure X) (s : Set X)
    (hs : MeasurableSet s) : Lp ℂ ∞ mu :=
  (memLp_top_of_bound
    (stronglyMeasurable_const.indicator hs).aestronglyMeasurable 1
    (ae_of_all mu fun x ↦ by
      by_cases hx : x ∈ s
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx])).toLp
    (s.indicator (fun _ ↦ (1 : ℂ)))

/-- Almost-everywhere representative of the measurable indicator class. -/
theorem measurableSetIndicatorLInf_coe_ae (mu : Measure X) (s : Set X)
    (hs : MeasurableSet s) :
    (measurableSetIndicatorLInf mu s hs : X → ℂ) =ᵐ[mu]
      s.indicator (fun _ ↦ 1) := by
  exact MemLp.coeFn_toLp _

/-- Quotient-level restriction of an `L²` field to a measurable set,
implemented as multiplication by its indicator. -/
def l2MeasurableSetRestriction (mu : Measure X) (s : Set X)
    (hs : MeasurableSet s) : Lp E 2 mu →L[ℂ] Lp E 2 mu :=
  scalarVectorMulL2 mu (measurableSetIndicatorLInf mu s hs)

/-- The quotient-level restriction has the expected pointwise representative. -/
theorem l2MeasurableSetRestriction_coe_ae (mu : Measure X) (s : Set X)
    (hs : MeasurableSet s) (f : Lp E 2 mu) :
    (l2MeasurableSetRestriction (E := E) mu s hs f : X → E) =ᵐ[mu]
      s.indicator (fun x ↦ f x) := by
  filter_upwards [scalarVectorMulL2_coe_ae mu
      (measurableSetIndicatorLInf mu s hs) f,
    measurableSetIndicatorLInf_coe_ae mu s hs] with x hmul hind
  change
    (scalarVectorMulL2 mu (measurableSetIndicatorLInf mu s hs) f : X → E) x =
      s.indicator (fun x ↦ f x) x
  rw [hmul, hind]
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

end MeasurableCutoff

section StrongConvergence

variable {X : Type u} [MeasurableSpace X]
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {I : Type w} {l : Filter I} [l.IsCountablyGenerated]

/-- Plancherel-type identity used to run dominated convergence in `L²`: the integral of
`‖f x‖²` against `μ` is `‖f‖²`. -/
private theorem integral_norm_sq_restriction_eq
    (mu : Measure X) (f : Lp E 2 mu) :
    ∫ x, ‖f x‖ ^ 2 ∂mu = ‖f‖ ^ 2 := by
  have h := congrArg (fun z : ℂ ↦ RCLike.re z) (L2.inner_def f f)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)] at h
  simpa only [← norm_sq_eq_re_inner] using h.symm

/-- Generic dominated-convergence theorem for quotient-level `L²`
restrictions.  It is enough that the measurable set indicators converge
pointwise almost everywhere to zero. -/
theorem tendsto_l2MeasurableSetRestriction_zero
    (mu : Measure X) (s : I → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hpoint : ∀ᵐ x ∂mu,
      Tendsto (fun i ↦ (s i).indicator (fun _ ↦ (1 : ℂ)) x) l (𝓝 0))
    (f : Lp E 2 mu) :
    Tendsto (fun i ↦ l2MeasurableSetRestriction (E := E) mu (s i) (hs i) f)
      l (𝓝 0) := by
  let F : I → X → ℝ := fun i x ↦ ‖(s i).indicator (fun y ↦ f y) x‖ ^ 2
  have hmeas : ∀ i, AEStronglyMeasurable (F i) mu := by
    intro i
    exact (((Lp.stronglyMeasurable f).indicator (hs i)).norm.pow 2).aestronglyMeasurable
  have hbound : ∀ i, ∀ᵐ x ∂mu, ‖F i x‖ ≤ ‖f x‖ ^ 2 := by
    intro i
    filter_upwards [] with x
    dsimp only [F]
    by_cases hx : x ∈ s i
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hint : Integrable (fun x ↦ ‖f x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm
      (Lp.stronglyMeasurable f).aestronglyMeasurable).1 (Lp.memLp f)
  have hlim : ∀ᵐ x ∂mu, Tendsto (fun i ↦ F i x) l (𝓝 0) := by
    filter_upwards [hpoint] with x hx
    have hmul := hx.smul_const (f x)
    have hind : (fun i ↦
        (s i).indicator (fun y ↦ f y) x) =
        (fun i ↦ ((s i).indicator (fun _ ↦ (1 : ℂ)) x) • f x) := by
      funext i
      by_cases hxi : x ∈ s i
      · simp [Set.indicator_of_mem hxi]
      · simp [Set.indicator_of_notMem hxi]
    have hfield : Tendsto (fun i ↦
        (s i).indicator (fun y ↦ f y) x) l (𝓝 0) := by
      rw [hind]
      simpa using hmul
    simpa [F] using (tendsto_norm.comp hfield).pow 2
  have hintegral : Tendsto (fun i ↦ ∫ x, F i x ∂mu) l (𝓝 0) := by
    simpa using tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ ‖f x‖ ^ 2)
      (Eventually.of_forall hmeas)
      (Eventually.of_forall hbound) hint hlim
  have hsq : Tendsto (fun i ↦
      ‖l2MeasurableSetRestriction (E := E) mu (s i) (hs i) f‖ ^ 2)
      l (𝓝 0) := by
    apply hintegral.congr'
    filter_upwards [] with i
    rw [← integral_norm_sq_restriction_eq mu
      (l2MeasurableSetRestriction (E := E) mu (s i) (hs i) f)]
    apply integral_congr_ae
    filter_upwards [l2MeasurableSetRestriction_coe_ae
      (E := E) mu (s i) (hs i) f] with x hx
    simp only [F, hx]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs,
    abs_norm] using hsqrt

end StrongConvergence

section WholePlane

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Strict exterior of the closed radius-`R` ball in the whole plane.  This is
the set `{y | R < ‖y‖}`. -/
def wholePlaneExterior (R : ℝ) : Set WholePlane :=
  (Metric.closedBall (0 : WholePlane) R)ᶜ

/-- A point lies in the exterior region exactly when `R < ‖x‖`. -/
@[simp] theorem mem_wholePlaneExterior_iff (R : ℝ) (x : WholePlane) :
    x ∈ wholePlaneExterior R ↔ R < ‖x‖ := by
  simp [wholePlaneExterior, Metric.mem_closedBall]

/-- Exterior regions are measurable. -/
theorem measurableSet_wholePlaneExterior (R : ℝ) :
    MeasurableSet (wholePlaneExterior R) :=
  measurableSet_closedBall.compl

/-- Quotient-level multiplication by the indicator of the exterior of the
radius-`R` ball. -/
def wholePlaneExteriorCutoff (R : ℝ) :
    WholePlaneL2 E →L[ℂ] WholePlaneL2 E :=
  l2MeasurableSetRestriction volume (wholePlaneExterior R)
    (measurableSet_wholePlaneExterior R)

/-- Representative formula for the whole-plane exterior cutoff. -/
theorem wholePlaneExteriorCutoff_coe_ae (R : ℝ) (f : WholePlaneL2 E) :
    (wholePlaneExteriorCutoff (E := E) R f : WholePlane → E) =ᵐ[volume]
      (wholePlaneExterior R).indicator (fun x ↦ f x) :=
  l2MeasurableSetRestriction_coe_ae volume _ _ f

/-- At every point, strict exterior indicators vanish as the real radius tends
to infinity. -/
theorem tendsto_wholePlaneExterior_indicator (x : WholePlane) :
    Tendsto (fun R : ℝ ↦
      (wholePlaneExterior R).indicator (fun _ ↦ (1 : ℂ)) x)
      atTop (𝓝 0) := by
  have hevent : ∀ᶠ R : ℝ in atTop, x ∉ wholePlaneExterior R := by
    filter_upwards [eventually_gt_atTop ‖x‖] with R hR
    simpa only [mem_wholePlaneExterior_iff, not_lt] using hR.le
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [hevent] with R hR
  simp [Set.indicator_of_notMem hR]

/-- Exterior cutoff converges strongly to zero as the real radius tends to
infinity. -/
theorem tendsto_wholePlaneExteriorCutoff_apply_zero (f : WholePlaneL2 E) :
    Tendsto (fun R : ℝ ↦ wholePlaneExteriorCutoff (E := E) R f)
      atTop (𝓝 0) := by
  exact tendsto_l2MeasurableSetRestriction_zero volume
    wholePlaneExterior measurableSet_wholePlaneExterior
    (ae_of_all volume tendsto_wholePlaneExterior_indicator) f

end WholePlane

end

end FastDynamo
