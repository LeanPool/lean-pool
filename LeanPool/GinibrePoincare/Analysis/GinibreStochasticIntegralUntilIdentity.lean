/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticIntegralUntilIdentity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousLocalIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticProbabilityRestriction

/-! # Identifying continuous integral limits before a random time

For each deterministic `t`, restrict the two approximation sequences to
`E = {ω | t ≤ σ ω}` by indicators. Their finite sums agree on `E`, and their
indicator limits therefore agree almost everywhere by uniqueness of limits
in measure. The terminal event needs no adaptedness or predictability.

The continuous-identity theorem upgrades these individual deterministic-time
identities to one full-measure event valid for every time up to `σ`. The
bound `σ ≤ T` lets times beyond the horizon be dismissed and ensures the
required sequence limits are available for all relevant times. -/

@[expose] public section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreContinuous_probability_limits_eq_until
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (S Q : ℝ≥0 → ℕ → Ω → ℝ) (I J : ℝ≥0 → Ω → ℝ)
    (hIC : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
    (hJC : ∀ᵐ ω ∂P, Continuous (fun t => J t ω))
    (T : ℝ≥0) (σ : Ω → ℝ≥0) (hσ : ∀ ω, σ ω ≤ T)
    (hS : ∀ t ≤ T, TendstoInMeasure P (S t) atTop (I t))
    (hQ : ∀ t ≤ T, TendstoInMeasure P (Q t) atTop (J t))
    (hEq : ∀ t ≤ T, ∀ k ω, t ≤ σ ω → S t k ω = Q t k ω) :
    ∀ᵐ ω ∂P, ∀ t ≤ σ ω, I t ω=J t ω := by
  classical
  apply ginibre_ae_continuous_identity_until P I J σ hIC hJC
  intro t
  by_cases ht : t ≤ T
  · let E : Set Ω := {ω | t ≤ σ ω}
    have hp := ginibre_tendstoInMeasure_indicator P E (S t) (I t) (hS t ht)
    have hq := ginibre_tendstoInMeasure_indicator P E (Q t) (J t) (hQ t ht)
    have he : (fun k => E.indicator (S t k))=(fun k => E.indicator (Q t k)) := by
      funext k ω
      by_cases hω : ω ∈ E
      · simp only [Set.indicator_of_mem hω]
        exact hEq t ht k ω hω
      · simp only [Set.indicator_of_notMem hω]
    rw [he] at hp
    filter_upwards [tendstoInMeasure_ae_unique hp hq] with ω hω
    intro hts
    have hωE : ω ∈ E := hts
    simpa only [Set.indicator_of_mem hωE] using hω
  · exact Eventually.of_forall (fun ω hts => (ht (hts.trans (hσ ω))).elim)
end
end GinibrePoincare
