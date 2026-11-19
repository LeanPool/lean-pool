/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityTestIntegrability.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreLocalSobolev
public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalClosure
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianIntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSobolevClosure
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# Ginibre transition analytic local regularity test integrability

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_local_compact_test_integrable`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] in
theorem ginibreLocalRegularity_local_compact_test_integrable
    (U : Set E) (u q : E → ℝ) (hu : LocallyIntegrableOn u U (volume : Measure E))
    (hq : Continuous q) (hc : HasCompactSupport q) (hs : tsupport q ⊆ U) :
    Integrable (fun x => u x*q x) volume := by
  have hi : Integrable (tsupport q |>.indicator u) volume := by
    rw [integrable_indicator_iff (isClosed_tsupport q).measurableSet]
    exact hu.integrableOn_compact_subset hs hc
  have hm := hi.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hq hc
  apply hm.congr
  exact ae_of_all volume fun x => by
    dsimp only
    by_cases hx : x ∈ tsupport q
    · simp only [Set.indicator_of_mem hx, smul_eq_mul]
    · simp only [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, smul_eq_mul,
        mul_zero]

end
end GinibrePoincare
