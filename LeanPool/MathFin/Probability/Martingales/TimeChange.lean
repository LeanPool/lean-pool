/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import TauCeti.Probability.Martingale.Basic

/-!
# A martingale along a monotone time change

A filtration `𝓕` indexed by `ι` and a monotone map `φ : κ → ι` give a filtration indexed by `κ`,
`t ↦ 𝓕 (φ t)` (`Filtration.comp`). A martingale `f` for `𝓕` read along `φ`, `t ↦ f (φ t)`, is a
martingale for it (`Martingale.comp`). When `φ` has a monotone right inverse `ψ` (`φ (ψ i) = i`),
the converse holds: a process whose reading along `φ` is a martingale is one itself
(`Martingale.of_comp`).

The time change that matters here is the step count of a discrete market seen in continuous time:
`t ↦ ⌊t⌋₊` for unit steps, `t ↦ ⌊t / h⌋₊` for steps of length `h`. The discrete market and the
binomial tree become markets indexed by `ℝ≥0` this way (`Pricing/DiscreteMarket.lean`,
`Models/Binomial/Market.lean`).

## Main definitions

* `MeasureTheory.Filtration.comp`: the filtration `t ↦ 𝓕 (φ t)` along a monotone `φ`.

## Main results

* `MeasureTheory.Martingale.comp`: a martingale read along a monotone time change is a martingale.
* `MeasureTheory.Martingale.of_comp`: the converse, along a time change with a monotone right
  inverse.

## References

* [Rogers and Williams][RogersWilliams]

## Tags

martingale, filtration, time change, reindexing, discrete time in continuous time, MSC 60G42,
MSC 60G44
-/

@[expose] public section

namespace MeasureTheory

variable {Ω ι κ E : Type*} {m : MeasurableSpace Ω} [Preorder ι] [Preorder κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure Ω}

/-- **Conversely, a process whose reading along a time change is a martingale is a martingale**,
when the time change `φ` has a monotone right inverse `ψ`: read the martingale at the times
`ψ i`. -/
theorem Martingale.of_comp {𝓕 : Filtration ι m} {f : ι → Ω → E} {φ : κ → ι} (hφ : Monotone φ)
    {ψ : ι → κ} (hψ : Monotone ψ) (hφψ : ∀ i, φ (ψ i) = i)
    (hf : Martingale (fun t ↦ f (φ t)) (𝓕.comp hφ) μ) : Martingale f 𝓕 μ := by
  refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
  · have h := hf.1 (ψ i)
    beta_reduce at h
    rw [Filtration.comp_apply, hφψ] at h
    exact h
  · have h := hf.2 (ψ i) (ψ j) (hψ hij)
    beta_reduce at h
    rw [Filtration.comp_apply, hφψ, hφψ] at h
    exact h

end MeasureTheory
