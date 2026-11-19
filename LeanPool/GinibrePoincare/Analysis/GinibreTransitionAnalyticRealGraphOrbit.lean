/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticRealGraphOrbit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticGraphUniqueness
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupPaperSpeed

/-!
# Ginibre transition analytic real graph orbit

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreFullRealEvolution_graph_derivative`,
`ginibreFullRealEvolution_preserves_graph`.
-/

@[expose] public section

open Set
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Actual real full generator-domain orbits have their genuine derivative. -/
theorem ginibreFullRealEvolution_graph_derivative {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hg : ginibreFullSymmetricResolvent n hn (u - v) = u)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ginibreFullRealEvolution n hn s.toNNReal u)
      (ginibreFullRealEvolution n hn t.toNNReal v) t := by
  have hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph := by
    rw [ginibreFullGenerator_graph_iff,← map_sub, ginibreFullComplexResolvent_ofReal, hg]
  have hd := ginibreFullEvolution_hasDerivAt n hn _ _ hgraph ht
  exact (ginibreFullSymmetricRe n).hasFDerivAt.comp_hasDerivAt t hd

/-- The actual real semigroup preserves the full real weak generator graph. -/
theorem ginibreFullRealEvolution_preserves_graph {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hg : ginibreFullSymmetricResolvent n hn (u - v) = u) (t : ℝ≥0) :
    ginibreFullSymmetricResolvent n hn
      (ginibreFullRealEvolution n hn t u-ginibreFullRealEvolution n hn t v)=
      ginibreFullRealEvolution n hn t u := by
  have hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph := by
    rw [ginibreFullGenerator_graph_iff,← map_sub, ginibreFullComplexResolvent_ofReal, hg]
  have hh := resolventCfcEvolution_preserves_generator_graph (ginibreFullComplexResolvent n hn)
    (ginibreFullComplexResolvent_isSelfAdjoint n hn) (ginibreFullComplexResolvent_injective n hn)
    t _ _ hgraph
  exact ((ginibreFullGenerator_graph_iff_real_imag hn _ _).mp hh).1

end
end GinibrePoincare
