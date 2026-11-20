/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WholePlaneBandLimitedRellichUnconditional

/-!
# Compactness for supported whole-plane local coefficients

The generic compactness assembly in `WholePlaneLocalCompactness` reduces
bounded coefficient multiplication to scalar restriction on a common
finite-volume support.  The band-limited Rellich theorem proves that
restriction compact.  This leaf module discharges the
restriction premise: multiplication `H¹ → L²` by a bounded scalar coefficient
supported in a measurable finite-volume set is compact.  No coefficient
regularity, PDE theorem, or spectral input is used.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Supported scalar localizations -/

/-- Multiplication `H¹ → L²` by a bounded scalar coefficient supported
almost everywhere in a measurable finite-volume set is compact. -/
theorem isCompactOperator_wholePlaneScalarLocalizationH1_of_ae_zero_off
    (s : Set WholePlane) (hs : MeasurableSet s)
    (hsm : volume s ≠ (∞ : ℝ≥0∞)) (a : WholePlaneScalarLInf)
    (ha : ∀ᵐ x ∂volume, x ∉ s → a x = 0) :
    IsCompactOperator (wholePlaneScalarLocalizationH1 a) := by
  exact isCompactOperator_wholePlaneScalarLocalizationH1_of_restriction
    s hs hsm a ha
      (isCompactOperator_wholePlaneScalarRestrictionH1 s hs hsm)

end

end FastDynamo
