/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.Stationarity
public import LeanPool.HighContrastHomogenization.Setup.LocalSigmaFields

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorInvariantEvent

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The invariant full-measure event of the coefficient space

The integer translations act on the coefficient space as a group, and the
intersection of all their preimages of a full-measure measurable event is again
a measurable full-measure event, this time invariant under every integer
translation.  This is the event on which one common corrector family can be
defined for all phases at once.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

open MeasureTheory

variable {d : ℕ}

/-! ## The integer translation group action -/

/-- The translation vector of a sum of integer vectors splits. -/
theorem intTranslation_add (z w : Fin d → ℤ) :
    Source.AKL.intTranslation (z + w) =
      Source.AKL.intTranslation z + Source.AKL.intTranslation w := by
  funext i
  simp [Source.AKL.intTranslation]

/-- The translation vector of the zero integer vector vanishes. -/
theorem intTranslation_zero :
    Source.AKL.intTranslation (0 : Fin d → ℤ) = (0 : Vec d) := by
  funext i
  simp [Source.AKL.intTranslation]

/-- Translating a field by zero leaves it unchanged. -/
theorem translateField_zero (a : Source.AKL.Field d) :
    Source.AKL.translateField 0 a = a := by
  apply AEEqFun.ext
  filter_upwards [Source.AKL.translateField_ae (0 : Fin d → ℤ) a] with x hx
  rw [hx, intTranslation_zero, add_zero]

/-- Successive field translations compose. -/
theorem translateField_translateField (z w : Fin d → ℤ)
    (a : Source.AKL.Field d) :
    Source.AKL.translateField z (Source.AKL.translateField w a) =
      Source.AKL.translateField (z + w) a := by
  apply AEEqFun.ext
  have hmp := measurePreserving_add_right (volume : Measure (Vec d))
    (Source.AKL.intTranslation z)
  filter_upwards [Source.AKL.translateField_ae z (Source.AKL.translateField w a),
    hmp.quasiMeasurePreserving.tendsto_ae (Source.AKL.translateField_ae w a),
    Source.AKL.translateField_ae (z + w) a] with x hx1 hx2 hx3
  rw [hx1, hx2, hx3, intTranslation_add, add_assoc]

/-- Translating a coefficient sample by zero leaves it unchanged. -/
@[simp] theorem translateCoeff_zero (a : CoeffSpace d) :
    translateCoeff 0 a = a :=
  Subtype.ext (translateField_zero a.1)

/-- Successive coefficient translations compose. -/
theorem translateCoeff_translateCoeff (z w : Fin d → ℤ) (a : CoeffSpace d) :
    translateCoeff z (translateCoeff w a) = translateCoeff (z + w) a :=
  Subtype.ext (translateField_translateField z w a.1)

/-! ## The invariant core of an event -/

/-- The integer-translation invariant core of an event: the samples all of
whose integer translates lie in the event. -/
@[expose]
def invariantTranslationCore (G : Set (CoeffSpace d)) : Set (CoeffSpace d) :=
  ⋂ z : Fin d → ℤ, translateCoeff z ⁻¹' G

theorem mem_invariantTranslationCore_iff {G : Set (CoeffSpace d)}
    {a : CoeffSpace d} :
    a ∈ invariantTranslationCore G ↔
      ∀ z : Fin d → ℤ, translateCoeff z a ∈ G :=
  Set.mem_iInter

/-- The invariant core is invariant under every integer translation. -/
theorem preimage_translateCoeff_invariantTranslationCore
    (G : Set (CoeffSpace d)) (z : Fin d → ℤ) :
    translateCoeff z ⁻¹' invariantTranslationCore G =
      invariantTranslationCore G := by
  ext a
  simp only [Set.mem_preimage, mem_invariantTranslationCore_iff]
  constructor
  · intro h w
    have hw := h (w - z)
    have hsum : w - z + z = w := sub_add_cancel w z
    rwa [translateCoeff_translateCoeff, hsum] at hw
  · intro h w
    rw [translateCoeff_translateCoeff]
    exact h (w + z)

/-! ## Full measure under a stationary law -/

end

end HighContrast
end HCPolySupport
