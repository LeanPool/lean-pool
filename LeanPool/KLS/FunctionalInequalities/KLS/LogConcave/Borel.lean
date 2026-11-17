/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.LogConcave
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compact-set and Borel-set log-concavity

Source: Blueprint `thm:compact-borell-logconcavity-equivalence`, Bobkov (1999),
equation (5.1), and finite-dimensional Radon inner regularity.
Read `innerMeasure`, `BorelLogConcave`, then `LogConcave.borel_iff`.

The definitions and the equivalence are fully proved. Neither density,
full-dimensional support, positive dimension nor a second moment is assumed.
The set function `innerMeasure` is not packaged as a countably additive `Measure`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.KLS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Inner measure of an arbitrary set, using compact subsets, including the empty set.
No outer-measure evaluation of the arbitrary set occurs in this definition. -/
def innerMeasure (μ : Measure E) (S : Set E) : ENNReal :=
  ⨆ (K : Set E) (_ : K ⊆ S) (_ : IsCompact K), μ K

/-- Bobkov's Borel-set formulation, with inner measure on the Minkowski combination.
The exponent range excludes both endpoints, exactly as in the compact-set predicate. -/
def BorelLogConcave (μ : ProbabilityMeasure E) : Prop :=
  ∀ (B₀ B₁ : Set E), MeasurableSet B₀ → MeasurableSet B₁ →
    ∀ t : ℝ, 0 < t → t < 1 →
      (μ : Measure E) B₀ ^ t * (μ : Measure E) B₁ ^ (1 - t) ≤
        innerMeasure (μ : Measure E)
          {z | ∃ x ∈ B₀, ∃ y ∈ B₁, z = t • x + (1 - t) • y}

section InnerMeasureProperties

omit [NormedSpace ℝ E] [BorelSpace E]

/-- Inner measure is monotone in the set. -/
theorem innerMeasure_mono (μ : Measure E) {S T : Set E} (h : S ⊆ T) :
    innerMeasure μ S ≤ innerMeasure μ T := by
  unfold innerMeasure
  exact iSup₂_le fun K hK ↦ iSup_le fun hc ↦ le_iSup₂_of_le K (hK.trans h) (le_iSup_of_le hc le_rfl)

/-- Inner measure never exceeds the outer-measure value of the set. -/
theorem innerMeasure_le (μ : Measure E) (S : Set E) : innerMeasure μ S ≤ μ S := by
  unfold innerMeasure
  exact iSup₂_le fun K hK ↦ iSup_le fun _ ↦ measure_mono hK

/-- Every compact subset gives a lower bound for the inner measure. -/
theorem le_innerMeasure_of_isCompact (μ : Measure E) {K S : Set E} (hK : IsCompact K)
    (hKS : K ⊆ S) : μ K ≤ innerMeasure μ S :=
  le_iSup₂_of_le K hKS (le_iSup_of_le hK le_rfl)

/-- On measurable sets the inner measure agrees with an inner regular measure. -/
theorem innerMeasure_eq_of_measurableSet (μ : Measure E) [μ.InnerRegular] {S : Set E}
    (hS : MeasurableSet S) : innerMeasure μ S = μ S :=
  (hS.measure_eq_iSup_isCompact μ).symm

end InnerMeasureProperties

section CompactCombinations

omit [MeasurableSpace E] [BorelSpace E]

/-- The Minkowski combination of two compact sets is compact: it is the continuous image of
the compact product. Finite dimension is not needed for this step. -/
theorem isCompact_combination {K₀ K₁ : Set E} (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (t : ℝ) : IsCompact {z : E | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y} := by
  have he : {z : E | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y} =
      (fun p : E × E ↦ t • p.1 + (1 - t) • p.2) '' (K₀ ×ˢ K₁) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩; exact ⟨x, hx, y, hy, rfl⟩
  rw [he]
  exact (hK₀.prod hK₁).image (by fun_prop)

/-- The Minkowski combination is monotone in both sets. -/
theorem combination_mono {A₀ A₁ B₀ B₁ : Set E} (h₀ : A₀ ⊆ B₀) (h₁ : A₁ ⊆ B₁) (t : ℝ) :
    {z : E | ∃ x ∈ A₀, ∃ y ∈ A₁, z = t • x + (1 - t) • y} ⊆
      {z : E | ∃ x ∈ B₀, ∃ y ∈ B₁, z = t • x + (1 - t) • y} := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact ⟨x, h₀ hx, y, h₁ hy, rfl⟩

end CompactCombinations

/-- Compact-set log-concavity is equivalent to the Borel/inner-measure formulation.
Compact sets are Borel and the inner measure is dominated by the measure, so the Borel
formulation specializes. Conversely, compact inner regularity writes each Borel mass as a
supremum over compact subsets; positive powers and products commute with these suprema, and
the compact combination of two compact subsets is a compact subset of the Borel combination.
The empty compact subset handles null sets; finite dimension includes the zero space. -/
theorem LogConcave.borel_iff [FiniteDimensional ℝ E] (μ : ProbabilityMeasure E) :
    LogConcave μ ↔ BorelLogConcave μ := by
  constructor
  · intro h B₀ B₁ hB₀ hB₁ t ht0 ht1
    have ht1' : 0 < 1 - t := by linarith
    have key :
      ∀ K₀ K₁ : Set E,
        K₀ ⊆ B₀ →
          IsCompact K₀ →
            K₁ ⊆ B₁ →
              IsCompact K₁ →
                (μ : Measure E) K₀ ^ t * (μ : Measure E) K₁ ^ (1 - t) ≤
                  innerMeasure (μ : Measure E)
                    {z | ∃ x ∈ B₀, ∃ y ∈ B₁, z = t • x + (1 - t) • y} :=
      fun K₀ K₁ h₀ hK₀ h₁ hK₁ ↦
      (h K₀ K₁ hK₀ hK₁ t ht0 ht1).trans
        (le_innerMeasure_of_isCompact _ (isCompact_combination hK₀ hK₁ t)
          (combination_mono h₀ h₁ t))
    calc
      (μ : Measure E) B₀ ^ t * (μ : Measure E) B₁ ^ (1 - t) =
          (⨆ (K : Set E) (_ : K ⊆ B₀) (_ : IsCompact K), (μ : Measure E) K) ^ t *
            (⨆ (K : Set E) (_ : K ⊆ B₁) (_ : IsCompact K), (μ : Measure E) K) ^ (1 - t) := by
        rw [hB₀.measure_eq_iSup_isCompact, hB₁.measure_eq_iSup_isCompact]
      _ =
          ⨆ (K₀ : Set E) (_ : K₀ ⊆ B₀) (_ : IsCompact K₀) (K₁ : Set E) (_ : K₁ ⊆ B₁) (_ :
            IsCompact K₁), (μ : Measure E) K₀ ^ t * (μ : Measure E) K₁ ^ (1 - t) := by
        simp_rw (config := { congrConsts := false }) [← ENNReal.orderIsoRpow_apply t ht0, ←
          ENNReal.orderIsoRpow_apply (1 - t) ht1']
        simp_rw (config := { congrConsts := false }) [(ENNReal.orderIsoRpow _ ht0).map_iSup _,
          (ENNReal.orderIsoRpow _ ht1').map_iSup _, ENNReal.iSup_mul, ENNReal.mul_iSup]
      _ ≤ _ := by
        refine iSup₂_le fun K₀ h₀ ↦ iSup_le fun hK₀ ↦ iSup₂_le fun K₁ h₁ ↦ iSup_le fun hK₁ ↦ ?_
        exact key K₀ K₁ h₀ hK₀ h₁ hK₁
  · intro h K₀ K₁ hK₀ hK₁ t ht0 ht1
    exact (h K₀ K₁ hK₀.measurableSet hK₁.measurableSet t ht0 ht1).trans (innerMeasure_le _ _)

end FunctionalInequalities.KLS
