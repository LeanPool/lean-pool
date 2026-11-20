/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberCompactCore.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberCompactCoreCauchy
/-!
# Correspondence operator number compact core

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorNumber_compact_smooth_core`.
-/

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology
namespace GinibrePoincare
open ComplexHermite
noncomputable section

/-- The literal differential number graph on actual compact C∞ tests. -/
def correspondenceNumberCompactSmoothGraph (n : ℕ) :
    Set (BKGaussianL2 n×BKGaussianL2 n) :=
  range (fun f : BKCompactTest n=>(f.l2, bkCompactNumberL2 f))

/-- Radial cutoffs approximate every finite Hermite polynomial in the actual
number-operator graph norm, not merely in the first-order form norm. -/
theorem correspondenceOperatorNumber_finite_compact_core (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    (finiteHermiteCombination n hn c, finiteGaussianNumberL2 n hn c)∈
      closure (correspondenceNumberCompactSmoothGraph n) := by
  let f:=finiteHermiteFunction n hn c
  let hf:=contDiff_finiteHermiteFunction_smooth n hn c
  let F:=fun m=>correspondenceNumberCutoff f hf m
  obtain ⟨hV, hD, hQ⟩ := correspondenceNumber_finite_cutoff_jets n hn c
  have hC := correspondenceNumber_compact_number_cauchy hn F
    (fun j=>finiteDbarComponentL2 n hn c j)
    (fun j k=>finiteHermiteCombination n hn (loweredCoefficients n (loweredCoefficients n c j) k))
        hD hQ
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hC
  have ht : Tendsto (fun m=>((F m).l2, bkCompactNumberL2 (F m))) atTop
      (𝓝 (finiteHermiteCombination n hn c, v)) := hV.prodMk_nhds hv
  have hgraph : (finiteHermiteCombination n hn c, v)∈(correspondenceOperatorNumber n hn).graph := by
    rw [correspondenceOperatorNumber_graph]
    exact (correspondenceOperatorNumberGraph_isClosed n hn).mem_of_tendsto ht
      (Eventually.of_forall (fun m=>(correspondenceOperatorNumber_graph n hn) ▸
          correspondenceOperatorNumber_compact_graph hn (F m)))
  have he : v=finiteGaussianNumberL2 n hn c :=
    (correspondenceOperatorNumber n hn).mem_graph_snd_inj hgraph
      (correspondenceOperatorNumber_finite_graph n hn c) rfl
  rw [he] at ht
  exact isClosed_closure.mem_of_tendsto ht (Eventually.of_forall (fun m=>subset_closure ⟨F m, rfl⟩))

/-- Genuine compact C∞ operator core for the maximal Gaussian number operator
in Section 6. All cutoff convergence and differential identifications are
proved internally. -/
theorem correspondenceOperatorNumber_compact_smooth_core (n : ℕ) (hn : 0 < n) :
    closure (correspondenceNumberCompactSmoothGraph n)=
      ((correspondenceOperatorNumber n hn).graph : Set (BKGaussianL2 n×BKGaussianL2 n)) := by
  apply Subset.antisymm
  · apply closure_minimal
    · rintro p ⟨f, rfl⟩
      exact correspondenceOperatorNumber_compact_graph hn f
    · rw [correspondenceOperatorNumber_graph]
      exact correspondenceOperatorNumberGraph_isClosed n hn
  · rintro ⟨u, v⟩ huv
    obtain ⟨hU, hV⟩ := correspondenceOperatorNumber_finite_core n hn u v huv
    apply isClosed_closure.mem_of_tendsto (hU.prodMk_nhds hV)
    exact Eventually.of_forall (fun s=>correspondenceOperatorNumber_finite_compact_core n hn _)

end
end GinibrePoincare
