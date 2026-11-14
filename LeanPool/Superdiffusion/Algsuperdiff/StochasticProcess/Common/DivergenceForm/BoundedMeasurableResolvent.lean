/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PenalizationEverywhere
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.LinftyResolventBound
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ShiftedResolventRegularity
public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.PositiveShift

/-!
# BoundedMeasurableResolvent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-
The analytic resolvent on bounded measurable data, with its domain-interior
continuous representative.
-/

/-!
# The `L²` class of a bounded measurable datum on a bounded domain

A bounded measurable function on a bounded domain lies in `L²` of that domain,
so the `α`-shifted resolvent applies to it.  This file constructs the zero
extension `domainExtension` of such a datum, records its measurability and its
uniform bound, and packages the resulting `L²` class as
`boundedMeasurableToScalarL2` together with its almost-everywhere
representative and the same uniform bound.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- The extension by zero of a function defined on the domain. -/
def domainExtension (f : U → ℝ) : Vec d → ℝ :=
  Function.extend (Subtype.val : U → Vec d) f 0

@[simp] theorem domainExtension_of_mem {f : U → ℝ} {x : Vec d} (hx : x ∈ U) :
    domainExtension f x = f ⟨x, hx⟩ := by
  have := Subtype.val_injective (p := fun y : Vec d => y ∈ U)
  simpa using! this.extend_apply f 0 ⟨x, hx⟩

theorem measurable_domainExtension (hU : MeasurableSet U) {f : U → ℝ}
    (hf : Measurable f) : Measurable (domainExtension f) :=
  (MeasurableEmbedding.subtype_coe hU).measurable_extend hf measurable_const

theorem abs_domainExtension_le {f : U → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D)
    (x : Vec d) : |domainExtension f x| ≤ |D| := by
  by_cases hx : x ∈ U
  · rw [domainExtension_of_mem hx]
    exact (hfD ⟨x, hx⟩).trans (le_abs_self D)
  · have hnot : ¬ ∃ y : U, (y : Vec d) = x := by
      rintro ⟨y, rfl⟩
      exact hx y.2
    have hzero : domainExtension f x = 0 := by
      simpa [domainExtension] using
        Function.extend_apply' f (0 : Vec d → ℝ) x hnot
    rw [hzero, abs_zero]
    exact abs_nonneg D

/-- A bounded measurable function on a bounded domain lies in `L²` there. -/
theorem memScalarL2_domainExtension (hU : IsOpenBoundedConvexDomain U)
    {f : U → ℝ} (hfmeas : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    MemScalarL2 U (domainExtension f) := by
  let := hU.isFiniteMeasure_restrict_volume
  have hmeas : AEStronglyMeasurable (domainExtension f) (volumeMeasureOn U) :=
    (measurable_domainExtension hU.isOpen.measurableSet hfmeas).aestronglyMeasurable
  have htop : MemLp (domainExtension f) ⊤ (volumeMeasureOn U) := by
    refine memLp_top_of_bound hmeas |D| ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs] using abs_domainExtension_le hfD x
  exact htop.mono_exponent (by simp)

/-- The `L²` class of a bounded measurable function on the domain. -/
def boundedMeasurableToScalarL2 (hU : IsOpenBoundedConvexDomain U)
    {f : U → ℝ} (hfmeas : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    ScalarL2 U :=
  (memScalarL2_domainExtension hU hfmeas hfD).toLp _

theorem boundedMeasurableToScalarL2_coeFn (hU : IsOpenBoundedConvexDomain U)
    {f : U → ℝ} (hfmeas : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    boundedMeasurableToScalarL2 hU hfmeas hfD =ᵐ[volumeMeasureOn U]
      domainExtension f :=
  MemLp.coeFn_toLp _

theorem abs_boundedMeasurableToScalarL2_le (hU : IsOpenBoundedConvexDomain U)
    {f : U → ℝ} (hfmeas : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    ∀ᵐ x ∂volumeMeasureOn U,
      |boundedMeasurableToScalarL2 hU hfmeas hfD x| ≤ |D| := by
  filter_upwards [boundedMeasurableToScalarL2_coeFn hU hfmeas hfD] with x hx
  rw [hx]
  exact abs_domainExtension_le hfD x

section RegularityWitness

end RegularityWitness

section Representative

end Representative

end

end DivergenceFormProcess.Form
