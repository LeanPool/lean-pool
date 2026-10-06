/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.InvariantFullMeasureEvent

/-!
# High-contrast homogenization: Provider.Quenched.InvariantFullMeasureEventAE

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Invariant full-measure events from almost-everywhere properties

An almost-everywhere property need not itself define a measurable set.  Its
failure set nevertheless has outer measure zero, hence admits a measurable
null superset.  The complement is a measurable full-measure subset on which
the property holds pointwise, and the integer-translation invariant core can
then be applied without any measurability hypothesis on the property.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- An almost-everywhere property under a stationary probability law holds on
a measurable, literally integer-translation invariant probability-one event.
No measurability assumption on the property is required. -/
theorem exists_integerTranslate_invariant_fullMeasure_of_ae
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) {Good : CoeffSpace d → Prop}
    (hGood : ∀ᵐ a ∂P, Good a) :
    ∃ Ωend : Set (CoeffSpace d),
      MeasurableSet Ωend ∧
      P.real Ωend = 1 ∧
      (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Ωend = Ωend) ∧
      ∀ a ∈ Ωend, Good a := by
  have hbad : P {a | ¬Good a} = 0 := ae_iff.mp hGood
  obtain ⟨N, hbadN, hN, hNzero⟩ := exists_measurable_superset_of_null hbad
  let Ωgood : Set (CoeffSpace d) := Nᶜ
  have hΩgood : MeasurableSet Ωgood := hN.compl
  have hΩgood_subset : ∀ a ∈ Ωgood, Good a := by
    intro a ha
    by_contra haGood
    exact ha (hbadN haGood)
  have hΩgood_ae : ∀ᵐ a ∂P, a ∈ Ωgood := by
    exact compl_mem_ae_iff.mpr hNzero
  have hΩgood_full : P.real Ωgood = 1 := by
    have hmeasure : P Ωgood = P Set.univ :=
      (ae_mem_iff_measure_eq hΩgood.nullMeasurableSet).mp hΩgood_ae
    calc
      P.real Ωgood = P.real Set.univ := congrArg ENNReal.toReal hmeasure
      _ = 1 := probReal_univ
  obtain ⟨Ωend, hΩend, hΩend_full, hΩend_invariant, hΩend_subset⟩ :=
    exists_integerTranslate_invariant_fullMeasure_subset
      hP hΩgood hΩgood_full
  exact ⟨Ωend, hΩend, hΩend_full, hΩend_invariant,
    fun a ha ↦ hΩgood_subset a (hΩend_subset ha)⟩

end

end HCPolySupport.HighContrast.Quenched
