/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.StationarityTransport

/-!
# High-contrast homogenization: Provider.Quenched.InvariantFullMeasureEvent

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Integer-translation invariant full-measure events

This file constructs the literal invariant event used in the quenched endgame.
Starting from one measurable full-measure event, it intersects all of its
integer translates.  The resulting event is a measurable, full-measure,
translation-invariant subset of the original event.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Integer translations of coefficient fields compose additively. -/
theorem translateCoeff_add (z w : Fin d → ℤ) (a : CoeffSpace d) :
    translateCoeff z (translateCoeff w a) = translateCoeff (z + w) a := by
  apply Subtype.ext
  apply AEEqFun.ext
  have hw :=
    (measurePreserving_add_right (volume : Measure (Vec d))
      (Source.AKL.intTranslation z)).quasiMeasurePreserving.ae
        (Source.AKL.translateField_ae w a.1)
  filter_upwards [Source.AKL.translateField_ae z
      (Source.AKL.translateField w a.1), hw,
    Source.AKL.translateField_ae (z + w) a.1] with x hz hwx hzw
  change
    (Source.AKL.translateField z (Source.AKL.translateField w a.1)) x =
      (Source.AKL.translateField (z + w) a.1) x
  rw [hz, hwx, hzw]
  apply congrArg (fun y : Vec d => a.1 y)
  funext i
  simp [Source.AKL.intTranslation, add_assoc]

/-- Translation by the zero integer vector fixes every coefficient field. -/
theorem translateCoeff_zero (a : CoeffSpace d) :
    translateCoeff (0 : Fin d → ℤ) a = a := by
  apply Subtype.ext
  apply AEEqFun.ext
  filter_upwards [Source.AKL.translateField_ae (0 : Fin d → ℤ) a.1] with x hx
  change (Source.AKL.translateField (0 : Fin d → ℤ) a.1) x = a.1 x
  rw [hx]
  apply congrArg (fun y : Vec d => a.1 y)
  funext i
  simp [Source.AKL.intTranslation]

/-- Every measurable full-measure event contains a measurable full-measure
subevent that is literally invariant under all integer translations. -/
theorem exists_integerTranslate_invariant_fullMeasure_subset
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    {Ωgood : Set (CoeffSpace d)} (hΩgood : MeasurableSet Ωgood)
    (hΩgood_full : P.real Ωgood = 1) :
    ∃ Ωend : Set (CoeffSpace d),
      MeasurableSet Ωend ∧
      P.real Ωend = 1 ∧
      (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Ωend = Ωend) ∧
      Ωend ⊆ Ωgood := by
  let Ωend : Set (CoeffSpace d) := ⋂ z : Fin d → ℤ, translateCoeff z ⁻¹' Ωgood
  have hΩend : MeasurableSet Ωend :=
    MeasurableSet.iInter fun z =>
      hΩgood.preimage (Recurrence.measurePreserving_translateCoeff hP z).measurable
  have hΩgood_measure : P Ωgood = P Set.univ :=
    (measureReal_eq_measureReal_iff).1 (hΩgood_full.trans probReal_univ.symm)
  have hΩgood_ae : ∀ᵐ a ∂P, a ∈ Ωgood :=
    (ae_mem_iff_measure_eq hΩgood.nullMeasurableSet).2 hΩgood_measure
  have hΩend_ae : ∀ᵐ a ∂P, a ∈ Ωend := by
    have htranslated : ∀ z : Fin d → ℤ,
        ∀ᵐ a ∂P, translateCoeff z a ∈ Ωgood := fun z =>
      (Recurrence.measurePreserving_translateCoeff hP z).quasiMeasurePreserving.ae hΩgood_ae
    simpa only [Ωend, Set.mem_iInter, Set.mem_preimage] using
      (ae_all_iff.2 htranslated)
  have hΩend_full : P.real Ωend = 1 := by
    have hmeasure : P Ωend = P Set.univ :=
      (ae_mem_iff_measure_eq hΩend.nullMeasurableSet).1 hΩend_ae
    calc
      P.real Ωend = P.real Set.univ := congrArg ENNReal.toReal hmeasure
      _ = 1 := probReal_univ
  refine ⟨Ωend, hΩend, hΩend_full, ?_, ?_⟩
  · intro w
    ext a
    simp only [Set.mem_preimage, Ωend, Set.mem_iInter]
    constructor
    · intro ha z
      have hz := ha (z - w)
      simpa [translateCoeff_add] using hz
    · intro ha z
      simpa [translateCoeff_add] using ha (z + w)
  · intro a ha
    have hzero := (Set.mem_iInter.1 ha) (0 : Fin d → ℤ)
    simpa [translateCoeff_zero] using hzero

end

end Quenched
end HighContrast
end HCPolySupport
