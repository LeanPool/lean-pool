/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberCompactGraph.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberForm
public import LeanPool.GinibrePoincare.Analysis.AlternativeBochnerKodairaCompact
/-!
# Correspondence operator number compact graph

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorNumber_compact_graph`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section
/-- The actual differential number operator on every compact C∞ test belongs
to the maximal self-adjoint operator's graph. -/
theorem correspondenceOperatorNumber_compact_graph {n : ℕ} (hn : 0 < n)
    (f : BKCompactTest n) :
    (f.l2, bkCompactNumberL2 f)∈(correspondenceOperatorNumber n hn).graph := by
  rw [correspondenceOperatorNumber_graph_iff_ordinary_form]
  refine ⟨fun j=>(f.dbar j).l2,?_,?_⟩
  · intro j
    exact gaussian_smooth_weak_dbar hn j f.l2 (f.dbar j).l2 f
      (f.smooth.of_le (by simp)) f.l2_coe (f.dbar j).l2_coe
  · intro w E hw
    unfold bkCompactNumberL2
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro j hj
    have h := hw j (f.dbar j) ((f.dbar j).smooth.of_le (by simp)) (f.dbar j).compact
    have he : gaussianDbarAdjointTestL2 j (f.dbar j)
        ((f.dbar j).smooth.of_le (by simp)) (f.dbar j).compact=((f.dbar j).adjoint j).l2 := by
      apply Lp.ext
      filter_upwards [(gaussianDbarAdjointTest_memLp j (f.dbar j)
        ((f.dbar j).smooth.of_le (by simp)) (f.dbar j).compact).coeFn_toLp,
        ((f.dbar j).adjoint j).l2_coe] with z hz hf
      exact hz.trans hf.symm
    rw [he] at h
    exact h.symm
end
end GinibrePoincare
