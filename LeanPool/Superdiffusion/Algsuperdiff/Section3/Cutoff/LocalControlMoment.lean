/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.LocalControlBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.LawTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.GaussianMaximum

/-!
# LocalControlMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Gaussian moments for local cutoff controls

This module transports J2's literal one-sided tail to finite translated
unit-cube maxima without introducing an independence assumption.
-/

namespace Algsuperdiff.Section3.Cutoff

open MeasureTheory Set
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- The dimension-only constant in the finite Gaussian maximum estimate for
triadic unit descendants.  It is deliberately named so later shell-scale
summability statements cannot silently change the normalization. -/
def gaussianMaximumDimConst (d : ℕ) : ℝ :=
  IndependentSums.gammaMomentConst 2 *
    Real.sqrt (3 * (1 + (d : ℝ) * Real.log 3))

theorem gaussianMaximumDimConst_pos (d : ℕ) :
    0 < gaussianMaximumDimConst d := by
  unfold gaussianMaximumDimConst
  apply mul_pos
  · exact IndependentSums.gammaMomentConst_pos (by norm_num)
  · apply Real.sqrt_pos.2
    have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity

private theorem measurableSet_unitCubeValueNorm_tail (t : ℝ) :
    MeasurableSet {j : ShellField d | t < ShellField.unitCubeValueNorm j} :=
  measurableSet_lt measurable_const ShellField.unitCubeValueNorm_measurable

/-- J2's sequence-level tail induces the same literal tail for the exact
zero-shell marginal law. -/
theorem zeroShell_unitCubeValueNorm_gaussian_tail (M : ABKModel d)
    (t : ℝ) (ht : 1 ≤ t) :
    (ShellField.zeroShellLaw M.P).toMeasure
        {j | t < ShellField.unitCubeValueNorm j} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2))) := by
  change Measure.map (fun omega : ShellSeq d => omega 0) M.P.toMeasure
      {j | t < ShellField.unitCubeValueNorm j} ≤ _
  rw [Measure.map_apply_of_aemeasurable
    ShellField.measurable_zeroShellMap.aemeasurable
    (measurableSet_unitCubeValueNorm_tail t)]
  refine (measure_mono ?_).trans (M.J2.gaussian_tail t ht)
  intro omega hω
  exact lt_of_lt_of_le hω (unitCubeValueNorm_le_j2Observable (omega 0))

/-- Stationarity transports J2's unit-cube tail to every translated unit
control under the zero-shell law. -/
theorem zeroShell_translatedUnitCubeControl_gaussian_tail (M : ABKModel d)
    (z : Vec d) (t : ℝ) (ht : 1 ≤ t) :
    (ShellField.zeroShellLaw M.P).toMeasure
        {j | t < translatedUnitCubeControl z j} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2))) := by
  have hmap := map_translatedUnitCubeControl_zero_eq M z
  have htail := zeroShell_unitCubeValueNorm_gaussian_tail M t ht
  calc
    (ShellField.zeroShellLaw M.P).toMeasure
        {j | t < translatedUnitCubeControl z j} =
        Measure.map (translatedUnitCubeControl z)
          (ShellField.zeroShellLaw M.P).toMeasure {x | t < x} := by
      simpa only [Set.preimage_ofPred_eq] using!
        (Measure.map_apply_of_aemeasurable
          (measurable_translatedUnitCubeControl z).aemeasurable
          (measurableSet_lt measurable_const measurable_id)).symm
    _ = Measure.map ShellField.unitCubeValueNorm
          (ShellField.zeroShellLaw M.P).toMeasure {x | t < x} := by rw [hmap]
    _ = (ShellField.zeroShellLaw M.P).toMeasure
          {j | t < ShellField.unitCubeValueNorm j} := by
      simpa only [Set.preimage_ofPred_eq] using!
        Measure.map_apply_of_aemeasurable ShellField.unitCubeValueNorm_measurable.aemeasurable
          (measurableSet_lt measurable_const measurable_id)
    _ ≤ _ := htail

/-- Under the zero-shell marginal, the exact finite maximum over the unit
descendants of a nonnegative-scale origin cube is integrable.  No independence
of the translated controls is used: the finite-maximum lemma consumes only
their individual J2 tails. -/
theorem integrable_originCubeUnitControlMax_zero (M : ABKModel d)
    (q : ℤ) (hq : 0 ≤ q) :
    Integrable (originCubeUnitControlMax q hq)
      (ShellField.zeroShellLaw M.P).toMeasure := by
  let S := descendantsAtScale (originCube d q) 0
  let hS : S.Nonempty := descendantsAtScale_nonempty (originCube d q) hq
  let X : TriadicCube d → ShellField d → ℝ :=
    fun R => translatedUnitCubeControl (triadicCubeShift R)
  have hNonneg : ∀ R ∈ S, ∀ j, 0 ≤ X R j := by
    intro R _ j
    exact translatedUnitCubeControl_nonneg _ j
  have hMeas : ∀ R ∈ S, Measurable (X R) := by
    intro R _
    exact measurable_translatedUnitCubeControl _
  have hTail : ∀ R ∈ S, ∀ t : ℝ, 1 ≤ t →
      (ShellField.zeroShellLaw M.P).toMeasure {j | 1 * t < X R j} ≤
        ENNReal.ofReal (Real.exp (-(t ^ (2 : ℝ)))) := by
    intro R _ t ht
    simpa only [one_mul, X, ← Real.rpow_natCast] using!
      zeroShell_translatedUnitCubeControl_gaussian_tail M
        (triadicCubeShift R) t ht
  simpa only [originCubeUnitControlMax, S, X, hS] using!
    Algsuperdiff.Probability.integrable_finset_sup'_of_gaussian_tail
      (μ := (ShellField.zeroShellLaw M.P).toMeasure) hS (by norm_num : (0 : ℝ) < 1)
      hNonneg hMeas hTail

/-- The finite translated-unit maximum has the explicit dimension--depth
Gaussian expectation bound.  The expectation is used only together with the
integrability theorem above (and is therefore never a totalized-integral
surrogate). -/
theorem integral_originCubeUnitControlMax_zero_le (M : ABKModel d)
    (q : ℤ) (hq : 0 ≤ q) :
    ∫ j, originCubeUnitControlMax q hq j ∂(ShellField.zeroShellLaw M.P).toMeasure ≤
      gaussianMaximumDimConst d * Real.sqrt (1 + q.toNat) := by
  let S := descendantsAtScale (originCube d q) 0
  let hS : S.Nonempty := descendantsAtScale_nonempty (originCube d q) hq
  let X : TriadicCube d → ShellField d → ℝ :=
    fun R => translatedUnitCubeControl (triadicCubeShift R)
  have hCard : S.card = (3 ^ d) ^ q.toNat := by
    exact card_originCubeUnitControlMax_lattice q hq
  have hNonneg : ∀ R ∈ S, ∀ j, 0 ≤ X R j := by
    intro R _ j
    exact translatedUnitCubeControl_nonneg _ j
  have hMeas : ∀ R ∈ S, Measurable (X R) := by
    intro R _
    exact measurable_translatedUnitCubeControl _
  have hTail : ∀ R ∈ S, ∀ t : ℝ, 1 ≤ t →
      (ShellField.zeroShellLaw M.P).toMeasure {j | 1 * t < X R j} ≤
        ENNReal.ofReal (Real.exp (-(t ^ (2 : ℝ)))) := by
    intro R _ t ht
    simpa only [one_mul, X, ← Real.rpow_natCast] using!
      zeroShell_translatedUnitCubeControl_gaussian_tail M
        (triadicCubeShift R) t ht
  simpa only [originCubeUnitControlMax, S, X, hS, mul_one, gaussianMaximumDimConst] using!
    Algsuperdiff.Probability.integral_finset_sup'_le_of_gaussian_tail_of_card_eq_three_pow_sqrt
      (μ := (ShellField.zeroShellLaw M.P).toMeasure) hS
      (by norm_num : (0 : ℝ) < 1) hCard hNonneg hMeas hTail

/-- On nonnegative cube scales, the exact local control is integrable under
the zero-shell marginal because it is pointwise bounded by the integrable
finite descendant maximum. -/
theorem integrable_localCubeControl_under_zeroShellLaw_of_nonneg (M : ABKModel d)
    (q : ℤ) (hq : 0 ≤ q) :
    Integrable (localCubeControl q) (ShellField.zeroShellLaw M.P).toMeasure := by
  apply (integrable_originCubeUnitControlMax_zero M q hq).mono'
  · exact (measurable_localCubeControl q).aestronglyMeasurable
  · filter_upwards with j
    rw [Real.norm_eq_abs, abs_of_nonneg (localCubeControl_nonneg q j)]
    exact localCubeControl_le_originCubeUnitControlMax q hq j

/-- On nonpositive cube scales, the local control is integrable under the
zero-shell marginal by direct comparison with the unit-cube control. -/
theorem integrable_localCubeControl_under_zeroShellLaw_of_nonpos (M : ABKModel d)
    (q : ℤ) (hq : q ≤ 0) :
    Integrable (localCubeControl q) (ShellField.zeroShellLaw M.P).toMeasure := by
  have hUnit : Integrable ShellField.unitCubeValueNorm
      (ShellField.zeroShellLaw M.P).toMeasure := by
    rw [ShellField.zeroShellLaw]
    apply (integrable_map_measure
      ShellField.unitCubeValueNorm_measurable.aestronglyMeasurable
      ShellField.measurable_zeroShellMap.aemeasurable).mpr
    simpa only [Function.comp_apply] using! integrable_unitCubeValueNorm_zero M
  apply hUnit.mono'
  · exact (measurable_localCubeControl q).aestronglyMeasurable
  · filter_upwards with j
    rw [Real.norm_eq_abs, abs_of_nonneg (localCubeControl_nonneg q j)]
    calc
      localCubeControl q j ≤ localCubeControl 0 j :=
        localCubeControl_le_localCubeControl_zero q hq j
      _ = ShellField.unitCubeValueNorm j := localCubeControl_zero_eq_unitCubeValueNorm j

/-- A convenient complete zero-shell integrability A for every integer cube scale. -/
theorem integrable_localCubeControl_under_zeroShellLaw (M : ABKModel d) (q : ℤ) :
    Integrable (localCubeControl q) (ShellField.zeroShellLaw M.P).toMeasure := by
  rcases le_total 0 q with hq | hq
  · exact integrable_localCubeControl_under_zeroShellLaw_of_nonneg M q hq
  · exact integrable_localCubeControl_under_zeroShellLaw_of_nonpos M q hq

/-- The nonnegative-scale local control inherits the finite-maximum expectation
bound.  Both integrability facts are supplied explicitly before monotonicity
of the Bochner integral is invoked. -/
theorem integral_localCubeControl_under_zeroShellLaw_le_of_nonneg (M : ABKModel d)
    (q : ℤ) (hq : 0 ≤ q) :
    ∫ j, localCubeControl q j ∂(ShellField.zeroShellLaw M.P).toMeasure ≤
      gaussianMaximumDimConst d * Real.sqrt (1 + q.toNat) := by
  calc
    ∫ j, localCubeControl q j ∂(ShellField.zeroShellLaw M.P).toMeasure ≤
        ∫ j, originCubeUnitControlMax q hq j ∂(ShellField.zeroShellLaw M.P).toMeasure := by
      apply integral_mono
      · exact integrable_localCubeControl_under_zeroShellLaw_of_nonneg M q hq
      · exact integrable_originCubeUnitControlMax_zero M q hq
      · intro j
        exact localCubeControl_le_originCubeUnitControlMax q hq j
    _ ≤ _ := integral_originCubeUnitControlMax_zero_le M q hq

end

end Algsuperdiff.Section3.Cutoff
