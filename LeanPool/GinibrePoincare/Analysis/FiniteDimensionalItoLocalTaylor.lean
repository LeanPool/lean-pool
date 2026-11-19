/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoLocalTaylor.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoTaylor
public import Mathlib.Topology.MetricSpace.Thickening

/-! # C² Taylor control on an open domain

The segment versions of the Taylor formula and Hessian-oscillation bound
(`itoTaylorRemainder_norm_le_of_segment` and its companions in
`FiniteDimensionalItoTaylor`) require C² regularity only along `x + t • h`,
for `0 ≤ t ≤ 1`. They therefore apply to functions defined smoothly away from
a singular set.

For a compact subset `K` of an open domain `U`, choose a positive closed
thickening of `K` still contained in `U`. Properness makes this thickening
compact, so the Hessian is uniformly continuous there. Taking increments
shorter than both the thickening radius and the continuity threshold keeps
the entire segment in `U` and gives a uniform quadratic remainder estimate.
The domain and `K` need not be convex in this local version. -/

@[expose] public section

open MeasureTheory Metric
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform quadratic remainder on any compact subset of an open C² domain.
The domain need not be convex; short increment segments stay inside it. -/
theorem itoTaylorRemainder_uniform_compact_open [ProperSpace E]
    (f : E → ℝ) (U K : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ h : E, ‖h‖ < δ →
      ‖itoTaylorRemainder f x h‖ ≤ ε * ‖h‖^2 := by
  obtain ⟨η, hη, hth⟩ := hK.exists_cthickening_subset_open hU hKU
  have hc : ContinuousOn (iteratedFDeriv ℝ 2 f) (cthickening η K) :=
    (ContinuousOn.continuousOn_iteratedFDeriv hf hU (by norm_num)).mono hth
  have hu := hK.cthickening.uniformContinuousOn_of_continuous hc
  intro ε hε
  obtain ⟨r, hr, hu⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨min η r, lt_min hη hr, fun x hx h hh => ?_⟩
  have hdist (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : dist (x+t•h) x < min η r := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt hh
  have hseg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : x+t•h ∈ cthickening η K :=
    mem_cthickening_of_dist_le _ x η K hx ((hdist t ht).le.trans (min_le_left _ _))
  apply itoTaylorRemainder_norm_le_of_segment f x h
    (fun t ht => hf.contDiffAt (hU.mem_nhds (hth (hseg t ht)))) ε hε.le
  intro t ht
  simpa only [dist_eq_norm] using (hu _ (hseg t ht) x (self_subset_cthickening K hx)
    ((hdist t ht).trans_le (min_le_right _ _))).le

end
end GinibrePoincare
