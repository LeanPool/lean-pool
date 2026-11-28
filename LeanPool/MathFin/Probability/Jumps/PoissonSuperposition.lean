/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Jumps.PoissonCounting

/-!
# Superposition of Poisson streams: merging two arrival-time constructions

Two counting processes built from independent families of i.i.d. `Exp(r₁)` and `Exp(r₂)`
interarrival times (`Probability/Jumps/PoissonCounting`) merge into a count with
`Poisson((r₁ + r₂)·t)`
law at every time `t ≥ 0`. The marginal laws are derived by `map_count_eq_poissonMeasure`, and the
independence of the two counts is derived from that of the interarrival families; the
convolution is Mathlib's `IndepFun.hasLaw_add_poissonMeasure` (the sum of independent Poisson
variables is Poisson), consumed directly. This is the one-time marginal of the merged stream;
that the merged count is a Poisson process (independent increments, exponential merged
interarrival times) is not proved.

## Main results

* `PoissonSuperposition.map_add_count_eq_poissonMeasure` — the merged count has
  `Poisson((r₁ + r₂)·t)` law at every time `t ≥ 0`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 3.3.9

## Tags

superposition of Poisson processes, merged arrival stream, sum of independent Poisson,
counting process, interarrival times, MSC 60G55, MSC 60E05
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace PoissonSuperposition

/-! ### Merging two arrival-time constructions -/

/-- A counting process read off its interarrival times is a function of the whole family of
interarrival times: `N t` is measurable for the σ-algebra that family generates. -/
lemma measurable_count_comap {Ω : Type*} {ξ : ℕ → Ω → ℝ}
    {N : ℝ → Ω → ℕ}
    (hcount : ∀ t k ω, N t ω = k ↔
      (∑ i ∈ Finset.range k, ξ i ω) ≤ t ∧ t < ∑ i ∈ Finset.range (k + 1), ξ i ω) (t : ℝ) :
    Measurable[MeasurableSpace.comap (fun ω i ↦ ξ i ω) inferInstance] (N t) := by
  refine @measurable_to_countable' ℕ Ω _ _
    (MeasurableSpace.comap (fun ω i ↦ ξ i ω) inferInstance) (N t) fun k ↦
    ⟨{x : ℕ → ℝ | (∑ i ∈ Finset.range k, x i) ≤ t ∧ t < ∑ i ∈ Finset.range (k + 1), x i},
      ?_, ?_⟩
  · exact (measurableSet_le (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i)
      measurable_const).inter
      (measurableSet_lt measurable_const (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i))
  · ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff, hcount]

/-- **Superposition of two arrival-time constructions.** Let `ξ` and `η` be families of i.i.d.
`Exp(r₁)` and `Exp(r₂)` interarrival times, independent of each other, and `N₁`, `N₂` the
counting processes they generate (`N t = k` iff the `k`-th arrival has happened by `t` but the
`(k+1)`-st has not). Then for every `t ≥ 0` the merged count `N₁ t + N₂ t` has the
`Poisson((r₁ + r₂)·t)` law.

The marginals `Poisson(r₁ t)` and `Poisson(r₂ t)` are derived from the constructions
(`PoissonCounting.map_count_eq_poissonMeasure`); the two counts are independent because each is
a function of its own interarrival family (`measurable_count_comap`); the convolution is
`IndepFun.hasLaw_add_poissonMeasure`. Only the one-time marginal of the merged stream is stated. -/
theorem map_add_count_eq_poissonMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {r₁ r₂ : ℝ≥0} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) {ξ η : ℕ → Ω → ℝ}
    (hξm : ∀ i, Measurable (ξ i)) (hηm : ∀ i, Measurable (η i))
    (hξ0 : ∀ i ω, 0 ≤ ξ i ω) (hη0 : ∀ i ω, 0 ≤ η i ω)
    (hξlaw : ∀ i, μ.map (ξ i) = expMeasure r₁) (hηlaw : ∀ i, μ.map (η i) = expMeasure r₂)
    (hξind : iIndepFun ξ μ) (hηind : iIndepFun η μ)
    (hξη : IndepFun (fun ω i ↦ ξ i ω) (fun ω i ↦ η i ω) μ)
    {N₁ N₂ : ℝ → Ω → ℕ}
    (hN₁ : ∀ t k ω, N₁ t ω = k ↔
      (∑ i ∈ Finset.range k, ξ i ω) ≤ t ∧ t < ∑ i ∈ Finset.range (k + 1), ξ i ω)
    (hN₂ : ∀ t k ω, N₂ t ω = k ↔
      (∑ i ∈ Finset.range k, η i ω) ≤ t ∧ t < ∑ i ∈ Finset.range (k + 1), η i ω)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.map (fun ω ↦ N₁ t ω + N₂ t ω) = poissonMeasure ((r₁ + r₂) * ⟨t, ht⟩) := by
  have hind : IndepFun (N₁ t) (N₂ t) μ :=
    (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
      (indep_of_indep_of_le_left ((IndepFun_iff_Indep _ _ _).1 hξη)
        (measurable_count_comap hN₁ t).comap_le)
      (measurable_count_comap hN₂ t).comap_le)
  have hmeas (ζ : ℕ → Ω → ℝ) (hζ : ∀ i, Measurable (ζ i)) {N : ℝ → Ω → ℕ}
      (hN : ∀ t k ω, N t ω = k ↔
        (∑ i ∈ Finset.range k, ζ i ω) ≤ t ∧ t < ∑ i ∈ Finset.range (k + 1), ζ i ω) :
      Measurable (N t) :=
    (measurable_count_comap hN t).mono
      (show Measurable fun ω i ↦ ζ i ω from measurable_pi_iff.2 hζ).comap_le le_rfl
  have h := hind.hasLaw_add_poissonMeasure
    ⟨(hmeas ξ hξm hN₁).aemeasurable,
      PoissonCounting.map_count_eq_poissonMeasure hr₁ hξm hξ0 hξlaw hξind hN₁ ht⟩
    ⟨(hmeas η hηm hN₂).aemeasurable,
      PoissonCounting.map_count_eq_poissonMeasure hr₂ hηm hη0 hηlaw hηind hN₂ ht⟩
  exact h.map_eq.trans (congrArg _ (add_mul r₁ r₂ _).symm)

end PoissonSuperposition

end MathFin
