/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueHarmonicPart

/-!
# ExitMeanValueHarmonicDensity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Differences of harmonic parts and the density of the data

The harmonic parts of `ExitMeanValueHarmonicPart.lean` are attached to nonnegative continuous
data vanishing at infinity, because the exit decomposition is an extended-real statement.  A
general datum is a difference of two nonnegative ones, so this file records what differences
give.

One generic process fact comes first: the exit mean-value property is preserved by subtraction
of bounded measurable functions (`hasExitMeanValueOn_sub`).

The analytic input is the density of the resolvent range.  A positive `C₀`-contractive resolvent
has dense range at every shift, and a continuous datum vanishing at infinity is the difference of
its positive and negative parts, both nonnegative and vanishing at infinity.  Hence every
continuous datum vanishing at infinity is uniformly approximated by differences
`R_mu g₁ - R_mu g₂` of resolvents of nonnegative such data
(`exists_nonneg_c0_resolvent_approx`).

The two together are what a consumer instantiates: a bounded measurable function uniformly
approximated by differences of harmonic parts inherits their exit mean-value property.
-/

namespace DivergenceFormProcess.StoppedDirichlet

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal

noncomputable section

section Process

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- **The exit mean-value property is preserved by differences.**  Both functions are integrable
against the exit distribution because they are bounded and measurable. -/
theorem hasExitMeanValueOn_sub {U : Set alpha} (hU : IsOpen U) {h k : alpha → ℝ}
    (hh : Measurable h) (hk : Measurable k) {M N : ℝ}
    (hM : ∀ z, ‖h z‖ ≤ M) (hN : ∀ z, ‖k z‖ ≤ N)
    (hharm : HasExitMeanValueOn P hP U h) (hkharm : HasExitMeanValueOn P hP U k) :
    HasExitMeanValueOn P hP U fun z ↦ h z - k z := by
  intro y hy
  set nu := IsConservative.continuousProcess P hP y with hnu
  have hint1 : Integrable (fun omega ↦ h (exitPosition U omega)) nu :=
    Integrable.of_bound (hh.comp (measurable_exitPosition hU)).aestronglyMeasurable M
      (Eventually.of_forall fun omega ↦ hM _)
  have hint2 : Integrable (fun omega ↦ k (exitPosition U omega)) nu :=
    Integrable.of_bound (hk.comp (measurable_exitPosition hU)).aestronglyMeasurable N
      (Eventually.of_forall fun omega ↦ hN _)
  change (∫ omega, (h (exitPosition U omega) - k (exitPosition U omega)) ∂nu) = h y - k y
  rw [integral_sub hint1 hint2, hharm y hy, hkharm y hy]

end Process

end

end DivergenceFormProcess.StoppedDirichlet

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess MarkovProcess.Semigroup
open DivergenceFormProcess.StoppedDirichlet
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ## The positive part of a continuous datum vanishing at infinity -/

/-- The positive part of a continuous datum vanishing at infinity. -/
def c0PosPart (g : C₀(Vec d, ℝ)) : C₀(Vec d, ℝ) where
  toFun := fun x ↦ max (g x) 0
  continuous_toFun := g.continuous.max continuous_const
  zero_at_infty' := by
    have hmax : Continuous fun r : ℝ ↦ max r 0 := continuous_id.max continuous_const
    have hcomp := (hmax.tendsto (0 : ℝ)).comp g.zero_at_infty'
    simpa only [Function.comp_def, max_self] using! hcomp

@[simp] theorem c0PosPart_apply (g : C₀(Vec d, ℝ)) (x : Vec d) :
    c0PosPart g x = max (g x) 0 := rfl

theorem c0PosPart_nonneg (g : C₀(Vec d, ℝ)) (x : Vec d) : 0 ≤ c0PosPart g x :=
  le_max_right _ _

/-- **A continuous datum vanishing at infinity is the difference of two nonnegative ones.** -/
theorem c0PosPart_sub_c0PosPart_neg (g : C₀(Vec d, ℝ)) :
    c0PosPart g - c0PosPart (-g) = g := by
  refine ZeroAtInftyContinuousMap.ext fun x ↦ ?_
  rw [ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply, c0PosPart_apply, c0PosPart_apply,
    ZeroAtInftyContinuousMap.coe_neg, Pi.neg_apply]
  rcases le_total 0 (g x) with hx | hx
  · rw [max_eq_left hx, max_eq_right (by linarith only [hx] : -g x ≤ (0 : ℝ)), sub_zero]
  · rw [max_eq_right hx, max_eq_left (by linarith only [hx] : (0 : ℝ) ≤ -g x), zero_sub, neg_neg]

/-- The absolute value of a continuous datum vanishing at infinity is at most its norm. -/
theorem abs_apply_le_norm_zeroAtInfty (g : C₀(Vec d, ℝ)) (y : Vec d) : |g y| ≤ ‖g‖ := by
  rw [← Real.norm_eq_abs, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm g.toBCF y

/-! ## Density of the resolvent range at nonnegative data -/

/-- **The resolvents of nonnegative data are dense.**  Every continuous datum vanishing at
infinity is uniformly approximated by a difference of resolvents of nonnegative continuous data
vanishing at infinity: the resolvent has dense range, and a general datum splits into its
positive and negative parts. -/
theorem exists_nonneg_c0_resolvent_approx (R : PositiveC0ContractiveResolvent (Vec d))
    (mu : PositiveShift) (F : C₀(Vec d, ℝ)) {eps : ℝ} (heps : 0 < eps) :
    ∃ g₁ g₂ : C₀(Vec d, ℝ), (∀ y, 0 ≤ g₁ y) ∧ (∀ y, 0 ≤ g₂ y) ∧
      ∀ y, |R.toContractiveResolvent.operator mu g₁ y -
        R.toContractiveResolvent.operator mu g₂ y - F y| ≤ eps := by
  obtain ⟨b, ⟨g, rfl⟩, hdist⟩ :=
    Metric.mem_closure_iff.mp (R.toContractiveResolvent.denseRange mu F) eps heps
  refine ⟨c0PosPart g, c0PosPart (-g), c0PosPart_nonneg g, c0PosPart_nonneg (-g), fun y ↦ ?_⟩
  have hsplit : R.toContractiveResolvent.operator mu (c0PosPart g) -
      R.toContractiveResolvent.operator mu (c0PosPart (-g)) =
      R.toContractiveResolvent.operator mu g := by
    rw [← map_sub, c0PosPart_sub_c0PosPart_neg]
  have hsplit' : R.toContractiveResolvent.operator mu (c0PosPart g) y -
      R.toContractiveResolvent.operator mu (c0PosPart (-g)) y =
      R.toContractiveResolvent.operator mu g y := by
    have hval := congrArg (fun f : C₀(Vec d, ℝ) ↦ f y) hsplit
    simpa only [ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply] using hval
  rw [hsplit']
  have hnorm : |R.toContractiveResolvent.operator mu g y - F y| ≤
      ‖R.toContractiveResolvent.operator mu g - F‖ := by
    have h := abs_apply_le_norm_zeroAtInfty (R.toContractiveResolvent.operator mu g - F) y
    rwa [ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply] at h
  refine hnorm.trans ?_
  rw [← dist_eq_norm, dist_comm]
  exact hdist.le

variable [NeZero d]

namespace WholeSpaceAnalyticData

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
