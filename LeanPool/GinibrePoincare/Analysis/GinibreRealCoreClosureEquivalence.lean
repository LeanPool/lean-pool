/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreRealCoreClosureEquivalence.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreArbitraryWeakPairClosure
public import LeanPool.GinibrePoincare.Analysis.GinibreGraphNormEquivalence

/-! # Real smooth core closure equivalence

The global and collision-free compact smooth real gradient graphs have exactly
the same closure: the independently defined distributional gradient graph.
This supplies the real part of the core assertion in arXiv v2 Lemma A.2.
-/

@[expose] public section

open MeasureTheory
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- All compact smooth real value-gradient pairs, with no support restriction. -/
def ginibreGlobalRealSmoothPairs (n : ℕ) : Set
    (Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) :=
  {p | ∃ f : Configuration n → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (p.1 : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f ∧
    (p.2 : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
      ginibreEuclideanGradient f}

theorem ginibreRealInteriorCore_closure_eq_distributional (n : ℕ) (hn : 0 < n) :
    closure (ginibreInteriorSmoothPair n) =
      {p | IsGinibreDistributionalGradient n p.1 p.2} := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ (isClosed_ginibre_distributional_gradient_pairs n hn)
    rintro p ⟨f, hs, _, _, hu, hg⟩
    exact ginibre_smooth_distributional_gradient n hn p.1 p.2 f hs hu hg
  · intro p hp
    exact ginibreWeakPair_mem_closure_interiorSmooth hn p.1 p.2 hp

/-- Global and collision-free compact smooth cores have the same real graph closure. -/
theorem ginibreRealSmoothCore_closure_equivalence (n : ℕ) (hn : 0 < n) :
    closure (ginibreGlobalRealSmoothPairs n) = closure (ginibreInteriorSmoothPair n) := by
  apply Set.Subset.antisymm
  · rw [ginibreRealInteriorCore_closure_eq_distributional n hn]
    apply closure_minimal _ (isClosed_ginibre_distributional_gradient_pairs n hn)
    rintro p ⟨f, hs, _, hu, hg⟩
    exact ginibre_smooth_distributional_gradient n hn p.1 p.2 f hs hu hg
  · apply closure_mono
    rintro p ⟨f, hs, hc, _, hu, hg⟩
    exact ⟨f, hs, hc, hu, hg⟩

end
end GinibrePoincare

