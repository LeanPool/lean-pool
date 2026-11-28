/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.Expectile
public import LeanPool.MathFin.Risk.Spectral

/-!
# Law invariance of risk functionals

A risk functional `ρ : (Ω → ℝ) → ℝ` of losses on a probability space `(Ω, P)` is **law invariant**
when two losses with the same law have the same risk (`IsLawInvariant`). This is the formal home of
the sentence "value-at-risk is a quantile of a law": a cell of the library that stands alone,
because its objects depend on a loss only through its distribution, is a law-invariant functional.
The library's four are instances:

* value-at-risk `valueAtRisk` and expected shortfall `expectedShortfall` are defined from the
  quantile function of `P.map X`, so law invariance is the definition unfolded;
* the spectral risk measures `spectralRiskMeasure φ` integrate the value-at-risk curve;
* the expectile `expectile α` is the root of a gap built from the integrals
  `∫ (Y − e)⁺ dP = ∫ (y − e)⁺ d(P.map Y)`.

## Main definitions

* `IsLawInvariant`: `P.map X = P.map Y` implies `ρ X = ρ Y`, for measurable losses.

## Main results

* `isLawInvariant_valueAtRisk`, `isLawInvariant_expectedShortfall`,
  `isLawInvariant_spectralRiskMeasure`, `isLawInvariant_expectile`.
* `expectedShortfall_isCoherentRiskMeasure_and_isLawInvariant`: expected shortfall is a
  law-invariant coherent risk measure.
* `IsLawInvariant.eq_of_hasLaw`: two losses with the law `μ` have the same risk.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Definitions 2.8 and 2.12
* [H. Föllmer and A. Schied, *Convex measures of risk and trading constraints*][FollmerSchied2002]

## Tags

law invariance, distribution-based risk measure, value at risk, expected shortfall, spectral risk
measure, expectile, MSC 91G70, MSC 60E05, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A risk functional `ρ` of losses on `(Ω, P)` is **law invariant** if measurable losses with the
same law have the same risk. -/
def IsLawInvariant (P : Measure Ω) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ ⦃X Y : Ω → ℝ⦄, AEMeasurable X P → AEMeasurable Y P → P.map X = P.map Y → ρ X = ρ Y

variable {P : Measure Ω} {ρ : (Ω → ℝ) → ℝ}

/-- A law-invariant functional gives equal risk to two losses with a common law. -/
lemma IsLawInvariant.eq_of_hasLaw (hρ : IsLawInvariant P ρ) {X Y : Ω → ℝ} {μ : Measure ℝ}
    (hX : ProbabilityTheory.HasLaw X μ P) (hY : ProbabilityTheory.HasLaw Y μ P) : ρ X = ρ Y :=
  hρ hX.aemeasurable hY.aemeasurable (hX.map_eq.trans hY.map_eq.symm)

/-- **Value-at-risk is law invariant**: it is the quantile of the law. -/
theorem isLawInvariant_valueAtRisk (α : ℝ) : IsLawInvariant P fun X ↦ valueAtRisk X P α :=
  fun _ _ _ _ h ↦ by simp only [valueAtRisk, h]

/-- **Expected shortfall is law invariant**: it averages the value-at-risk curve. -/
theorem isLawInvariant_expectedShortfall (α : ℝ) :
    IsLawInvariant P fun X ↦ expectedShortfall X P α :=
  fun _ _ _ _ h ↦ by simp only [expectedShortfall, valueAtRisk, h]

/-- **Expected shortfall is a law-invariant coherent risk measure** on the integrable losses, for
every level `α ∈ (0, 1)`. Kusuoka's theorem is the converse direction, the representation of
law-invariant coherent risk measures through expected shortfalls; it is not proved here. -/
theorem expectedShortfall_isCoherentRiskMeasure_and_isLawInvariant [IsProbabilityMeasure P]
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    IsCoherentRiskMeasure P (fun X ↦ expectedShortfall X P α) ∧
      IsLawInvariant P fun X ↦ expectedShortfall X P α :=
  ⟨expectedShortfall_isCoherentRiskMeasure hα, isLawInvariant_expectedShortfall α⟩

/-- **Spectral risk measures are law invariant**: they integrate the value-at-risk curve against
the spectrum. -/
theorem isLawInvariant_spectralRiskMeasure (φ : ℝ → ℝ) :
    IsLawInvariant P fun X ↦ spectralRiskMeasure φ X P :=
  fun _ _ _ _ h ↦ by simp only [spectralRiskMeasure, valueAtRisk, h]

/-- **Expectiles are law invariant**: the expectile gap at a threshold `e` is a function of the
law, through `∫ (Y − e)⁺ dP = ∫ (y − e)⁺ d(P.map Y)`. -/
theorem isLawInvariant_expectile (α : ℝ) :
    IsLawInvariant P fun Y ↦ expectile α Y P := by
  have key {Y : Ω → ℝ} (hY : AEMeasurable Y P) (e : ℝ) :
      expectileGap α Y P e = α * ∫ y, max (y - e) 0 ∂(P.map Y) -
        (1 - α) * ∫ y, max (e - y) 0 ∂(P.map Y) := by
    have h1 : ∫ ω, max (Y ω - e) 0 ∂P = ∫ y, max (y - e) 0 ∂(P.map Y) :=
      (integral_map (f := fun y ↦ max (y - e) 0) hY
        (Continuous.aestronglyMeasurable (by fun_prop))).symm
    have h2 : ∫ ω, max (e - Y ω) 0 ∂P = ∫ y, max (e - y) 0 ∂(P.map Y) :=
      (integral_map (f := fun y ↦ max (e - y) 0) hY
        (Continuous.aestronglyMeasurable (by fun_prop))).symm
    rw [expectileGap, h1, h2]
  intro X Y hX hY h
  have : expectileGap α X P = expectileGap α Y P := funext fun e ↦ by rw [key hX, key hY, h]
  simp only [expectile, this]

end MathFin
