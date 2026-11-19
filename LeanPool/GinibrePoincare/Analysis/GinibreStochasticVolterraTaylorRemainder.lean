/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticVolterraTaylorRemainder.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRestrictedTaylorRemainder

/-! Actual Brownian-driven compact Volterra paths have vanishing local C² Taylor remainder. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreCompactVolterra_taylor_remainder_tendstoInProbability
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (X : ℝ≥0 → Ω → Configuration n)
    (hX : StronglyAdapted (ginibreBrownianAugmentedFiltration B P hB) X)
    (hCont : ∀ ω, Continuous (fun t => X t ω))
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hRange : ∀ t ω, X t ω ∈ K) (T : ℝ≥0)
    (b : ℝ → Ω → Configuration n) (hb : ∀ ω, ContinuousOn (fun s => b s ω) (Icc (0 : ℝ) T))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ s ∈ Icc (0 : ℝ) T, ∀ ω, ‖b s ω‖ ≤ M)
    (hVolterra : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T, X t ω = X 0 ω +
      (ginibreConfigurationBrownianNoise n B α ω t - ginibreConfigurationBrownianNoise n B α ω 0) +
      ∫ s in (0 : ℝ)..(t : ℝ), b s ω) :
    TendstoInMeasure P (fun k ω => itoActualPathTaylorRemainderSum f (fun t => X t ω) T k)
      atTop (fun _ => 0) := by
  have h := ginibreCompactVolterra_restricted_taylor_remainder_tendstoInProbability n B P hB hind
    α X hX hCont f U K hU hf hK hKU hRange T b hb M hM hbound univ MeasurableSet.univ
    (by filter_upwards [hVolterra] with ω hω _ using hω)
  simpa only [indicator_univ] using h

end
end GinibrePoincare
