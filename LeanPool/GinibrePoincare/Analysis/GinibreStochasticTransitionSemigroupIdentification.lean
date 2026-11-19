/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionSemigroupIdentification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionSymmetricOperator
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionL2Semigroup
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionL2ZeroSpeed
public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticZeroSpeed

/-! # Original stochastic transitions equal the analytic evolution

The operator acts on the full symmetric real L² space. The first theorem
inherits the semigroup law from the unrestricted stochastic L² operator.
For positive speed, equality with `ginibreFullRealPaperEvolution` follows
from the contraction-semigroup identification theorem: continuity,
contractivity, the identity at time zero, and equality of Laplace transforms
are the inputs. Zero speed is handled separately because both evolutions
are the identity.

The last theorem translates operator equality into an almost-everywhere
formula for the original Brownian process when the L² input has a bounded
measurable representative `v`. The equality is almost everywhere in the
initial Ginibre configuration; it does not assert pointwise equality for
every initial configuration or every arbitrary representative. -/

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreOriginalSymmetricStochasticL2Operator_semigroup {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0)
    (u : ginibreFullSymmetricValues n) :
    ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB (s+t) u=
      ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB s
        (ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB t u) := by
  apply Subtype.ext
  change ginibreOriginalStochasticL2Operator hn α P B hB hiB (s+t) u.val=
    ginibreOriginalStochasticL2Operator hn α P B hB hiB s
      (ginibreOriginalStochasticL2Operator hn α P B hB hiB t u.val)
  rw [ginibreOriginalStochasticL2Operator_semigroup]
  rfl

theorem ginibreOriginalSymmetricStochasticL2Operator_eq_paper_positive {Ω : Type*} [MeasurableSpace
    Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (hα : 0 < α) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB T=
      ginibreFullRealPaperEvolution n hn α T := by
  apply ginibreSymmetricContractionSemigroup_eq_paper_evolution hn
    (ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB)
    (ginibreOriginalSymmetricStochasticL2Operator_continuous hn α P B hB hiB)
    (ginibreOriginalSymmetricStochasticL2Operator_norm_le hn α P B hB hiB)
    (ginibreOriginalSymmetricStochasticL2Operator_semigroup hn α P B hB hiB)
    (ginibreOriginalSymmetricStochasticL2Operator_zero hn α P B hB hiB) α hα
  exact ginibreOriginalSymmetricStochasticL2Operator_laplace hn α
    (show 0<(α : ℝ) by exact_mod_cast hα) P B hB hiB

theorem ginibreOriginalSymmetricStochasticL2Operator_eq_paper {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB T=
      ginibreFullRealPaperEvolution n hn α T := by
  by_cases hα : α=0
  · subst α
    rw [ginibreFullRealPaperEvolution_zero_speed hn T]
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    change ginibreOriginalStochasticL2Operator hn 0 P B hB hiB T u.val=u.val
    rw [ginibreOriginalStochasticL2Operator_zero_speed]
    rfl
  · exact ginibreOriginalSymmetricStochasticL2Operator_eq_paper_positive hn α
      (pos_iff_ne_zero.mpr hα) P B hB hiB T

theorem ginibreBrownian_original_transition_eq_paper_ae {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (u : ginibreFullSymmetricValues n) (v : Configuration n → ℝ)
    (hu : (u.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n] v)
    (hv : Measurable v) (C : ℝ) (hC : ∀ z, ‖v z‖ ≤ C) :
    (fun z => ∫ ω, v (ginibreBrownianMaximalProcess n α z B T ω) ∂P)=ᵐ[ginibreMeasure n]
      (ginibreFullRealPaperEvolution n hn α T u).val := by
  obtain ⟨hm, hb, he⟩ := ginibreOriginalStochasticL2Operator_bounded_representative
    hn α P B hB hiB T u.val v hu hv C hC
  have hop : ginibreOriginalStochasticL2Operator hn α P B hB hiB T u.val=
      (ginibreFullRealPaperEvolution n hn α T u).val := by
    rw [← ginibreOriginalSymmetricStochasticL2Operator_eq_paper hn α P B hB hiB T]
    rfl
  rw [hop] at he
  filter_upwards [he, ginibre_ae_collisionFree n hn] with z hz hcf
  rw [hz, ginibreStationaryContinuousTransitionMean_eq_original hn α P B hB hiB v z hcf]
  simp

end
end GinibrePoincare
