/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionL2Semigroup.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionBoundedOperator
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionMarkovMean

/-! # Chapman–Kolmogorov on the full stochastic L² space

The tested transition means satisfy the semigroup identity by the Brownian
restart and future-independence results. To extend this to L², the proof
first checks equality on bounded continuous representatives, translating
each of the three operators to its transition mean almost everywhere in
the initial Ginibre state.

Bounded continuous functions have dense image in L². Since the stochastic
operators and their compositions are continuous, equality on that dense
image implies equality of the operators. This argument handles arbitrary
L² equivalence classes without choosing pointwise versions of their
transition formulas. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Genuine Chapman–Kolmogorov identity for the actual stochastic L²
operators. The Brownian restart and future independence are derived internally. -/
theorem ginibreOriginalStochasticL2Operator_semigroup {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0) :
    ginibreOriginalStochasticL2Operator hn α P B hB hiB (s+t)=
      (ginibreOriginalStochasticL2Operator hn α P B hB hiB s).comp
        (ginibreOriginalStochasticL2Operator hn α P B hB hiB t) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  let A := ginibreOriginalStochasticL2Operator hn α P B hB hiB
  have he : (fun u => A (s+t) u)=(fun u => A s (A t u)) := by
    apply (BoundedContinuousFunction.toLp_denseRange ℝ (ginibreMeasure n) ℝ (by
        norm_num : (2 : ℝ≥0∞)≠∞)).equalizer
      (A (s+t)).continuous ((A s).continuous.comp (A t).continuous)
    funext v
    let g := BoundedContinuousFunction.toLp 2 (ginibreMeasure n) ℝ v
    have hg := BoundedContinuousFunction.coeFn_toLp (p := 2) (μ := ginibreMeasure n) (𝕜 := ℝ) v
    have hC (z : Configuration n) : ‖v z‖≤‖v‖ := v.norm_coe_le_norm z
    have ht := ginibreOriginalStochasticL2Operator_bounded_representative hn α P B hB hiB t g v hg
        v.continuous.measurable ‖v‖ hC
    have hs := ginibreOriginalStochasticL2Operator_bounded_representative hn α P B hB hiB s (A t g)
      (fun z => ginibreStationaryContinuousTransitionMean α B P v (t : ℝ) z)
      ht.2.2 ht.1 ‖v‖ ht.2.1
    have hst := ginibreOriginalStochasticL2Operator_bounded_representative hn α P B hB hiB (s+t) g v
        hg v.continuous.measurable ‖v‖ hC
    change A (s+t) g=A s (A t g)
    apply Lp.ext
    filter_upwards [ginibre_ae_collisionFree n hn, hst.2.2, hs.2.2] with z hz hleft hright
    change (ginibreOriginalStochasticL2Operator hn α P B hB hiB (s+t) g) z=
      (ginibreOriginalStochasticL2Operator hn α P B hB hiB s (A t g)) z
    rw [hleft, hright]
    exact ginibreStationaryContinuousTransitionMean_semigroup hn α P B hB hiB z hz s t v
        v.continuous.measurable ‖v‖ hC
  apply ContinuousLinearMap.ext
  intro u
  exact congr_fun he u

end
end GinibrePoincare
