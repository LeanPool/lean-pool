/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ExitMeanValueLimit
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ResolventExitDecomposition

/-!
# ExitMeanValueDecomposition

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The resolvent decomposition at an exit time, read as a discounted exit average

The library splits the discounted occupation of a nonnegative observable at the first exit from an
open set `U` into the occupation before exit -- the killed resolvent -- and the occupation after
exit, restarted from the exit location.  This file records the second term in the shape the
vanishing-shift argument of `ExitMeanValueLimit.lean` consumes.

* `lintegralDiscountedExit` is the extended-real discounted exit average, and
  `toReal_lintegralDiscountedExit` identifies it with the real discounted exit average of
  `ExitMeanValueLimit.lean` for a bounded nonnegative observable.
* `eq_killedResolvent_add_lintegralDiscountedExit` restates the library decomposition: if the
  expected discounted occupation of the observable is the function `phi` at every starting point,
  then

    `phi x = R^U_lam f (x) + E_x[1_{tau < infinity} e^{-lam tau} phi(X_tau)]`.

  The hypothesis names the whole-space resolvent of the observable; it is discharged by the
  identification of the process resolvent with the analytic one, which the caller supplies.
-/

namespace DivergenceFormProcess.StoppedDirichlet

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- **The extended-real discounted exit average.**  The expectation of the discounted value of a
nonnegative extended observable at the exit position, on the event that the path leaves `U`. -/
def lintegralDiscountedExit (U : Set alpha) (lam : ℝ) (phi : alpha → ℝ≥0∞) (z : alpha) : ℝ≥0∞ :=
  ∫⁻ omega, Set.indicator (exitEvent U)
      (fun omega ↦ ENNReal.ofReal (exitDiscount U lam omega) * phi (exitPosition U omega)) omega
    ∂(IsConservative.continuousProcess P hP z)

/-- The extended-real and the real discounted exit averages agree on a bounded nonnegative
observable. -/
theorem toReal_lintegralDiscountedExit {U : Set alpha} (hU : IsOpen U) (lam : ℝ)
    {psi : alpha → ℝ} (hpsi : Measurable psi) (hpsi0 : ∀ y, 0 ≤ psi y) (z : alpha) :
    (lintegralDiscountedExit P hP U lam (fun y ↦ ENNReal.ofReal (psi y)) z).toReal =
      discountedExitAverage P hP U lam psi z := by
  have hpoint : ∀ omega : ContinuousPath alpha,
      Set.indicator (exitEvent U)
        (fun omega ↦ ENNReal.ofReal (exitDiscount U lam omega) *
          ENNReal.ofReal (psi (exitPosition U omega))) omega =
      ENNReal.ofReal (discountedExitIntegrand U lam psi omega) := by
    intro omega
    by_cases homega : omega ∈ exitEvent U
    · rw [Set.indicator_of_mem homega, discountedExitIntegrand, Set.indicator_of_mem homega,
        ENNReal.ofReal_mul (exitDiscount_nonneg U lam omega)]
    · rw [Set.indicator_of_notMem homega, discountedExitIntegrand,
        Set.indicator_of_notMem homega, ENNReal.ofReal_zero]
  have hnonneg : ∀ omega : ContinuousPath alpha, 0 ≤ discountedExitIntegrand U lam psi omega := by
    intro omega
    rw [discountedExitIntegrand]
    by_cases homega : omega ∈ exitEvent U
    · rw [Set.indicator_of_mem homega]
      exact mul_nonneg (exitDiscount_nonneg U lam omega) (hpsi0 _)
    · rw [Set.indicator_of_notMem homega]
  rw [lintegralDiscountedExit]
  simp only [hpoint]
  rw [discountedExitAverage,
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall hnonneg)
      (measurable_discountedExitIntegrand hU lam hpsi).aestronglyMeasurable]

/-- The discounted exit average of a bounded observable is finite. -/
theorem lintegralDiscountedExit_ne_top {U : Set alpha} {lam : ℝ} (hlam : 0 ≤ lam)
    {phi : alpha → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ⊤) (hphi : ∀ y, phi y ≤ C) (z : alpha) :
    lintegralDiscountedExit P hP U lam phi z ≠ ⊤ := by
  have hbound : lintegralDiscountedExit P hP U lam phi z ≤ C := by
    have hpoint : ∀ omega : ContinuousPath alpha,
        Set.indicator (exitEvent U)
          (fun omega ↦ ENNReal.ofReal (exitDiscount U lam omega) *
            phi (exitPosition U omega)) omega ≤ C := by
      intro omega
      by_cases homega : omega ∈ exitEvent U
      · rw [Set.indicator_of_mem homega]
        calc ENNReal.ofReal (exitDiscount U lam omega) * phi (exitPosition U omega)
            ≤ 1 * C :=
              mul_le_mul' (by
                simpa only [ENNReal.ofReal_one] using
                  ENNReal.ofReal_le_ofReal (exitDiscount_le_one hlam omega))
                (hphi _)
          _ = C := one_mul C
      · rw [Set.indicator_of_notMem homega]
        exact zero_le
    calc lintegralDiscountedExit P hP U lam phi z
        ≤ ∫⁻ _omega : ContinuousPath alpha, C
          ∂(IsConservative.continuousProcess P hP z) := lintegral_mono hpoint
      _ = C := by rw [lintegral_const, measure_univ, mul_one]
  exact ne_top_of_le_ne_top hC hbound

/-- **The real discounted exit average is linear.**  It is a Bochner integral in the
observable. -/
theorem discountedExitAverage_add_const_mul {U : Set alpha} (hU : IsOpen U) (lam : ℝ)
    (hlam : 0 ≤ lam) {psi1 psi2 : alpha → ℝ} (h1 : Measurable psi1) (h2 : Measurable psi2)
    {M1 M2 : ℝ} (hM1 : ∀ y, ‖psi1 y‖ ≤ M1) (hM2 : ∀ y, ‖psi2 y‖ ≤ M2) (c : ℝ) (z : alpha) :
    discountedExitAverage P hP U lam (fun y ↦ psi1 y + c * psi2 y) z =
      discountedExitAverage P hP U lam psi1 z +
        c * discountedExitAverage P hP U lam psi2 z := by
  have hpoint : ∀ omega : ContinuousPath alpha,
      discountedExitIntegrand U lam (fun y ↦ psi1 y + c * psi2 y) omega =
        discountedExitIntegrand U lam psi1 omega +
          c * discountedExitIntegrand U lam psi2 omega := by
    intro omega
    simp only [discountedExitIntegrand]
    by_cases homega : omega ∈ exitEvent U
    · rw [Set.indicator_of_mem homega, Set.indicator_of_mem homega,
        Set.indicator_of_mem homega]
      ring
    · rw [Set.indicator_of_notMem homega, Set.indicator_of_notMem homega,
        Set.indicator_of_notMem homega]
      ring
  have hint1 : Integrable (discountedExitIntegrand U lam psi1)
      (IsConservative.continuousProcess P hP z) :=
    Integrable.of_bound (measurable_discountedExitIntegrand hU lam h1).aestronglyMeasurable M1
      (Filter.Eventually.of_forall fun omega ↦
        norm_discountedExitIntegrand_le hlam hM1 omega)
  have hint2 : Integrable (discountedExitIntegrand U lam psi2)
      (IsConservative.continuousProcess P hP z) :=
    Integrable.of_bound (measurable_discountedExitIntegrand hU lam h2).aestronglyMeasurable M2
      (Filter.Eventually.of_forall fun omega ↦
        norm_discountedExitIntegrand_le hlam hM2 omega)
  simp only [discountedExitAverage, hpoint]
  rw [integral_add hint1 (hint2.const_mul c), integral_const_mul]

variable [LocallyCompactSpace alpha]

/-- **The resolvent decomposition at the exit time, in discounted-exit form.**  If the expected
discounted occupation of the observable `f` is `phi` at every starting point, then the value of
`phi` splits into the killed resolvent of `f` on `U` and the discounted exit average of `phi`. -/
theorem eq_killedResolvent_add_lintegralDiscountedExit
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    {phi : alpha → ℝ≥0∞}
    (hres : ∀ z : alpha, (∫⁻ eta, ContinuousPath.pathResolvent lam f eta
      ∂(IsConservative.continuousProcess P hP z)) = phi z) (x : alpha) :
    phi x = IsConservative.killedResolvent P hP U hU lam f x +
      lintegralDiscountedExit P hP U lam phi x := by
  have hbase := hFeller.lintegral_pathResolvent_eq_killedResolvent_add P hP hK U hU lam hf x
  rw [hres x] at hbase
  rw [hbase]
  congr 1
  refine lintegral_congr fun omega ↦ ?_
  have hset : ({omega | ContinuousPath.exitTime U omega < ⊤} : Set (ContinuousPath alpha)) =
      exitEvent U := rfl
  rw [hset]
  by_cases homega : omega ∈ exitEvent U
  · rw [Set.indicator_of_mem homega, Set.indicator_of_mem homega, hres _]
    rfl
  · rw [Set.indicator_of_notMem homega, Set.indicator_of_notMem homega]

end

end DivergenceFormProcess.StoppedDirichlet
