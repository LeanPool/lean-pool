/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.StoppedDirichletHarmonic

/-!
# ExitMeanValueLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The vanishing-shift limit of the discounted exit average

Let `Q` be the continuous-path process of a conservative Feller kernel semigroup, let `U` be an
open set with exit time `tau`, and let `psi` be a bounded measurable function.  The *discounted
exit average* at the shift `lam` is

  `E_y[1_{tau < infinity} e^{-lam tau} psi(X_tau)]`   (`discountedExitAverage`),

the quantity produced by the resolvent decomposition at the first exit from `U`.  This file
proves the two facts that turn such a family of identities into the exit mean-value property of
`StoppedDirichletHarmonic.lean`.

* As the shift decreases to zero the discount disappears
  (`tendsto_discountedExitAverage_nhdsGT_zero`): the integrands converge pointwise and are
  bounded by a constant, so dominated convergence applies along `nhdsWithin 0 (Ioi 0)`.
* Consequently, if for every small positive shift the discounted exit average is the difference
  of `psi` and some value at the starting point, and those values converge as the shift
  decreases to zero, then the limit function is represented by the exit distribution
  (`hasExitMeanValueOn_of_tendsto_discountedExitAverage`).  Only two facts about the process
  enter: the exit position lies outside `U`, and the exit time is almost surely finite, which
  is where the finiteness of the expected exit time is consumed.

A third, unrelated, stability fact is recorded: the exit mean-value property passes to uniform
limits (`hasExitMeanValueOn_of_forall_approx`), because the exit distribution is a subprobability
law.  This is what a density argument in the boundary data consumes.

Nothing here refers to a generator, and nothing here is specific to the divergence-form setting.
-/

namespace DivergenceFormProcess.StoppedDirichlet

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal

noncomputable section

section PathLevel

variable {alpha : Type*} [MetricSpace alpha]

/-- The event that the path leaves `U`. -/
def exitEvent (U : Set alpha) : Set (ContinuousPath alpha) :=
  {omega : ContinuousPath alpha | ContinuousPath.exitTime U omega < ⊤}

variable [MeasurableSpace alpha] [BorelSpace alpha]

theorem measurableSet_exitEvent {U : Set alpha} (hU : IsOpen U) :
    MeasurableSet (exitEvent (alpha := alpha) U) :=
  ContinuousPath.measurableSet_exitTime_lt_top U hU

/-- The exponential discount at the exit time. -/
def exitDiscount (U : Set alpha) (lam : ℝ) (omega : ContinuousPath alpha) : ℝ :=
  Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)

theorem measurable_exitDiscount {U : Set alpha} (hU : IsOpen U) (lam : ℝ) :
    Measurable (exitDiscount (alpha := alpha) U lam) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
    (ENNReal.measurable_toReal.comp (ContinuousPath.measurable_exitTime U hU))

/-- The integrand of the discounted exit average: the discounted value of `psi` at the exit
position, on the event that the path leaves `U`. -/
def discountedExitIntegrand (U : Set alpha) (lam : ℝ) (psi : alpha → ℝ)
    (omega : ContinuousPath alpha) : ℝ :=
  Set.indicator (exitEvent U)
    (fun omega ↦ exitDiscount U lam omega * psi (exitPosition U omega)) omega

theorem measurable_discountedExitIntegrand {U : Set alpha} (hU : IsOpen U) (lam : ℝ)
    {psi : alpha → ℝ} (hpsi : Measurable psi) :
    Measurable (discountedExitIntegrand (alpha := alpha) U lam psi) :=
  ((measurable_exitDiscount hU lam).mul
    (hpsi.comp (measurable_exitPosition hU))).indicator (measurableSet_exitEvent hU)

omit [MeasurableSpace alpha] [BorelSpace alpha] in
theorem exitDiscount_nonneg (U : Set alpha) (lam : ℝ) (omega : ContinuousPath alpha) :
    0 ≤ exitDiscount U lam omega := (Real.exp_pos _).le

omit [MeasurableSpace alpha] [BorelSpace alpha] in
theorem exitDiscount_le_one {U : Set alpha} {lam : ℝ} (hlam : 0 ≤ lam)
    (omega : ContinuousPath alpha) : exitDiscount U lam omega ≤ 1 := by
  rw [exitDiscount, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam) ENNReal.toReal_nonneg

omit [MeasurableSpace alpha] [BorelSpace alpha] in
theorem norm_discountedExitIntegrand_le {U : Set alpha} {lam : ℝ} (hlam : 0 ≤ lam)
    {psi : alpha → ℝ} {M : ℝ} (hM : ∀ y, ‖psi y‖ ≤ M) (omega : ContinuousPath alpha) :
    ‖discountedExitIntegrand U lam psi omega‖ ≤ M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (exitPosition U omega))
  rw [discountedExitIntegrand]
  by_cases homega : omega ∈ exitEvent U
  · rw [Set.indicator_of_mem homega, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (exitDiscount_nonneg U lam omega)]
    calc exitDiscount U lam omega * |psi (exitPosition U omega)|
        ≤ 1 * |psi (exitPosition U omega)| :=
          mul_le_mul_of_nonneg_right (exitDiscount_le_one hlam omega) (abs_nonneg _)
      _ ≤ M := by
          rw [one_mul, ← Real.norm_eq_abs]
          exact hM _
  · rw [Set.indicator_of_notMem homega, norm_zero]
    exact hM0

end PathLevel

section Process

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- **The discounted exit average.**  The expectation of the discounted value of `psi` at the
exit position, on the event that the path leaves `U`. -/
def discountedExitAverage (U : Set alpha) (lam : ℝ) (psi : alpha → ℝ) (y : alpha) : ℝ :=
  ∫ omega, discountedExitIntegrand U lam psi omega
    ∂(IsConservative.continuousProcess P hP y)

/-- **The discount disappears as the shift decreases to zero.**  The discounted exit averages
converge to the undiscounted average over the paths that leave `U`. -/
theorem tendsto_discountedExitAverage_nhdsGT_zero {U : Set alpha} (hU : IsOpen U)
    {psi : alpha → ℝ} (hpsi : Measurable psi) {M : ℝ} (hM : ∀ y, ‖psi y‖ ≤ M) (y : alpha) :
    Tendsto (fun lam : ℝ ↦ discountedExitAverage P hP U lam psi y) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ omega, Set.indicator (exitEvent U) (fun omega ↦ psi (exitPosition U omega)) omega
        ∂(IsConservative.continuousProcess P hP y))) := by
  set mu := IsConservative.continuousProcess P hP y with hmu
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ M) ?_ ?_
    (integrable_const M) ?_
  · filter_upwards [self_mem_nhdsWithin] with lam _
    exact (measurable_discountedExitIntegrand hU lam hpsi).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with lam hlam
    exact Eventually.of_forall fun omega ↦
      norm_discountedExitIntegrand_le (le_of_lt hlam) hM omega
  · refine Eventually.of_forall fun omega ↦ ?_
    by_cases homega : omega ∈ exitEvent U
    · simp only [discountedExitIntegrand, Set.indicator_of_mem homega]
      have hone : Tendsto (fun lam : ℝ ↦ exitDiscount U lam omega) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
        have hcont : Continuous fun lam : ℝ ↦ exitDiscount U lam omega :=
          Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)
        have hzero : Tendsto (fun lam : ℝ ↦ exitDiscount U lam omega) (𝓝[>] (0 : ℝ))
            (𝓝 (exitDiscount U 0 omega)) :=
          (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
        simpa only [exitDiscount, neg_zero, zero_mul, Real.exp_zero] using hzero
      simpa only [one_mul] using hone.mul_const (psi (exitPosition U omega))
    · simp only [discountedExitIntegrand, Set.indicator_of_notMem homega]
      exact tendsto_const_nhds

/-- From a starting point of `U` with a finite expected exit time, the path leaves `U` almost
surely and its exit position lies outside `U`. -/
theorem ae_exitPosition_notMem (hK : P.KolmogorovRegular hP) {U : Set alpha} (hU : IsOpen U)
    {y : alpha} (hy : y ∈ U) (hwfin : expectedExitTime P hP U y ≠ ⊤) :
    ∀ᵐ omega ∂(IsConservative.continuousProcess P hP y),
      omega ∈ exitEvent U ∧ exitPosition U omega ∉ U := by
  have haefin : ∀ᵐ omega ∂(IsConservative.continuousProcess P hP y),
      ContinuousPath.exitTime U omega < ⊤ :=
    ae_lt_top (ContinuousPath.measurable_exitTime U hU) hwfin
  filter_upwards [haefin, IsConservative.ae_eval_zero_eq hP hK y] with omega hfin h0
  refine ⟨hfin, ?_⟩
  have hfront := ContinuousPath.coordinate_exitTime_mem_frontier U hU omega (h0 ▸ hy) hfin.ne
  rw [hU.frontier_eq] at hfront
  exact hfront.2

/-- **The exit mean-value property from a vanishing-shift limit.**  Suppose that for every small
positive shift the discounted exit average of `psi` is the value of `psi` at the starting point
less a correction, and that the corrected values converge to `h` as the shift decreases to zero.
Then `h`, which agrees with `psi` off `U`, is represented by the exit distribution of `U`. -/
theorem hasExitMeanValueOn_of_tendsto_discountedExitAverage
    (hK : P.KolmogorovRegular hP) {U : Set alpha} (hU : IsOpen U)
    {psi : alpha → ℝ} (hpsi : Measurable psi) {M : ℝ} (hM : ∀ y, ‖psi y‖ ≤ M)
    (hwfin : ∀ y ∈ U, expectedExitTime P hP U y ≠ ⊤)
    {mu : ℝ} (hmu : 0 < mu) (val : ℝ → alpha → ℝ) {h : alpha → ℝ}
    (hdec : ∀ lam ∈ Set.Ioo (0 : ℝ) mu, ∀ y ∈ U,
      discountedExitAverage P hP U lam psi y = val lam y)
    (hoff : ∀ y, y ∉ U → h y = psi y)
    (hlim : ∀ y ∈ U, Tendsto (fun lam : ℝ ↦ val lam y) (𝓝[>] (0 : ℝ)) (𝓝 (h y))) :
    HasExitMeanValueOn P hP U h := by
  intro y hy
  have hae := ae_exitPosition_notMem P hP hK hU hy (hwfin y hy)
  have hrewrite : ∫ omega, h (exitPosition U omega)
        ∂(IsConservative.continuousProcess P hP y) =
      ∫ omega, Set.indicator (exitEvent U) (fun omega ↦ psi (exitPosition U omega)) omega
        ∂(IsConservative.continuousProcess P hP y) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with omega homega
    rw [Set.indicator_of_mem homega.1, hoff _ homega.2]
  have hbase := tendsto_discountedExitAverage_nhdsGT_zero P hP hU hpsi hM y
  rw [hrewrite]
  refine tendsto_nhds_unique hbase ?_
  refine (hlim y hy).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hmu] with lam hlam
  exact (hdec lam hlam y hy).symm

/-- **The exit mean-value property passes to uniform limits.**  A uniform limit of bounded
measurable functions represented by the exit distribution is itself represented by it. -/
theorem hasExitMeanValueOn_of_forall_approx {U : Set alpha} (hU : IsOpen U)
    {h : alpha → ℝ} (hh : Measurable h) {M : ℝ} (hM : ∀ y, ‖h y‖ ≤ M)
    (happrox : ∀ eps > (0 : ℝ), ∃ g : alpha → ℝ, Measurable g ∧ (∃ C : ℝ, ∀ y, ‖g y‖ ≤ C) ∧
      HasExitMeanValueOn P hP U g ∧ ∀ y, ‖g y - h y‖ ≤ eps) :
    HasExitMeanValueOn P hP U h := by
  intro y hy
  set nu := IsConservative.continuousProcess P hP y with hnu
  have hhint : Integrable (fun omega ↦ h (exitPosition U omega)) nu :=
    Integrable.of_bound (hh.comp (measurable_exitPosition hU)).aestronglyMeasurable M
      (Eventually.of_forall fun omega ↦ hM _)
  have hkey : ∀ eps > (0 : ℝ),
      ‖(∫ omega, h (exitPosition U omega) ∂nu) - h y‖ ≤ 2 * eps := by
    intro eps heps
    obtain ⟨g, hg, ⟨C, hC⟩, hgharm, hgh⟩ := happrox eps heps
    have hgint : Integrable (fun omega ↦ g (exitPosition U omega)) nu :=
      Integrable.of_bound (hg.comp (measurable_exitPosition hU)).aestronglyMeasurable C
        (Eventually.of_forall fun omega ↦ hC _)
    have hdiff : (∫ omega, h (exitPosition U omega) ∂nu) - h y =
        (∫ omega, (h (exitPosition U omega) - g (exitPosition U omega)) ∂nu) +
          (g y - h y) := by
      rw [integral_sub hhint hgint, hgharm y hy]
      ring
    have hfirst : ‖∫ omega, (h (exitPosition U omega) - g (exitPosition U omega)) ∂nu‖ ≤ eps := by
      have hbound : ∀ omega : ContinuousPath alpha,
          ‖h (exitPosition U omega) - g (exitPosition U omega)‖ ≤ eps := by
        intro omega
        rw [← norm_neg, neg_sub]
        exact hgh _
      simpa only [probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (μ := nu) (C := eps)
          (Eventually.of_forall hbound)
    have hsecond : ‖g y - h y‖ ≤ eps := hgh y
    rw [hdiff]
    calc ‖(∫ omega, (h (exitPosition U omega) - g (exitPosition U omega)) ∂nu) + (g y - h y)‖
        ≤ ‖∫ omega, (h (exitPosition U omega) - g (exitPosition U omega)) ∂nu‖ + ‖g y - h y‖ :=
          norm_add_le _ _
      _ ≤ 2 * eps := by linarith only [hfirst, hsecond]
  have hzero : (∫ omega, h (exitPosition U omega) ∂nu) - h y = 0 := by
    refine norm_le_zero_iff.mp (le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_)
    have hc2 : (0 : ℝ) < c / 2 := by linarith only [hc]
    calc ‖(∫ omega, h (exitPosition U omega) ∂nu) - h y‖ ≤ 2 * (c / 2) := hkey _ hc2
      _ = c := by ring
  exact sub_eq_zero.mp hzero

end Process

end

end DivergenceFormProcess.StoppedDirichlet
