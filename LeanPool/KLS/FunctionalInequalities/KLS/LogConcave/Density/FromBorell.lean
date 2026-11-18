/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.BrunnMinkowski
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Basic

/-!
# Compact-set log-concavity from a Borell density

The finite-dimensional Prékopa–Leindler theorem promotes pointwise
log-concavity of an actual Haar density to compact-set log-concavity of
its probability law. This is the general-dimensional counterpart of
`KLS.LineDensity.logConcave`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set

namespace FunctionalInequalities.KLS.IsBorellDensity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- A probability law with a pointwise log-concave Borell density is log-concave
on compact sets. This does not require the density to be positive everywhere. -/
theorem compactLogConcave {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) : LogConcave ν := by
  intro K₀ K₁ hK₀ hK₁ t ht0 ht1
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  set C := {z : V | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y} with hC
  have hCc : IsCompact C := isCompact_combination hK₀ hK₁ t
  have hmass :
    ∀ S : Set V, MeasurableSet S → (ν : Measure V) S = ∫⁻ x, ENNReal.ofReal (S.indicator ρ x) := by
    intro S hS
    have hind :
      ∀ x, ENNReal.ofReal (S.indicator ρ x) = S.indicator (fun y => ENNReal.ofReal (ρ y)) x := by
      intro x
      by_cases hx : x ∈ S <;> simp [hx]
    simp_rw [hind]
    rw [lintegral_indicator hS, ← hρ.withDensity_eq, withDensity_apply _ hS]
  rw [hmass K₀ hK₀.measurableSet, hmass K₁ hK₁.measurableSet, hmass C hCc.measurableSet]
  refine
    Analysis.prekopaLeindler (hρ.measurable.indicator hK₀.measurableSet)
      (hρ.measurable.indicator hK₁.measurableSet) (hρ.measurable.indicator hCc.measurableSet)
      (fun x => Set.indicator_nonneg (fun y _ => hρ.nonneg y) x)
      (fun y => Set.indicator_nonneg (fun z _ => hρ.nonneg z) y) ht0 ht1 ?_
  intro x y
  have hh0 : ∀ z, 0 ≤ C.indicator ρ z := fun z =>
    Set.indicator_nonneg (fun w _ => hρ.nonneg w) z
  by_cases hx : x ∈ K₀
  · by_cases hy : y ∈ K₁
    · have hz : t • x + (1 - t) • y ∈ C := ⟨x, hx, y, hy, rfl⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hz]
      exact hρ.logConcave x y t ht0 ht1
    · rw [Set.indicator_of_notMem hy, Real.zero_rpow ht1'.ne', mul_zero]
      exact hh0 _
  · rw [Set.indicator_of_notMem hx, Real.zero_rpow ht0.ne', zero_mul]
    exact hh0 _

end FunctionalInequalities.KLS.IsBorellDensity
