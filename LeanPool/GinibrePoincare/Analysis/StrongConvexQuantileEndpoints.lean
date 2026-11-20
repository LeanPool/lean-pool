/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexQuantileEndpoints.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexCDF

/-!
# Strong convex quantile endpoints

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `increasingCDFQuantileOn_tendsto_zero`, `increasingCDFQuantileOn_tendsto_atTop`.
-/

@[expose] public section

open Set Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Positive-support quantiles tend to the left endpoint at probability zero. -/
theorem increasingCDFQuantileOn_tendsto_zero (F : ℝ → ℝ)
    (hm : StrictMonoOn F (Ici 0)) (h0 : F 0 = 0)
    (hr : F '' Ioi 0 = Ioo 0 1) :
    Tendsto (increasingCDFQuantileOn F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr)
      (𝓝[Ioo 0 1] 0) (𝓝 0) := by
  let q := increasingCDFQuantileOn F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr
  apply tendsto_order.2
  constructor
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hq := increasingCDFQuantileOn_mem F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr u hu
    exact lt_trans hb (show 0 < q u from hq)
  · intro b hb
    have hFb : 0 < F b := by
      simpa only [h0] using hm (self_mem_Ici : (0 : ℝ) ∈ Ici 0) hb.le hb
    filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hFb), self_mem_nhdsWithin] with u hu huI
    have hq := increasingCDFQuantileOn_mem F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr u huI
    have he := increasingCDFQuantileOn_right_inverse F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr u
        huI
    change 0 < q u at hq
    change F (q u) = u at he
    by_contra hn
    have h := hm.monotoneOn hb.le (show 0 ≤ q u from hq.le) (le_of_not_gt hn)
    rw [he] at h
    exact (not_le_of_gt hu) h

/-- Positive-support quantiles tend to infinity at probability one. -/
theorem increasingCDFQuantileOn_tendsto_atTop (F : ℝ → ℝ)
    (hm : StrictMonoOn F (Ici 0)) (hr : F '' Ioi 0 = Ioo 0 1) :
    Tendsto (increasingCDFQuantileOn F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr)
      (𝓝[Ioo 0 1] 1) atTop := by
  let q := increasingCDFQuantileOn F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr
  apply tendsto_atTop.2
  intro b
  let B := max b 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hFB : F B < 1 := (hr ▸ Set.mem_image_of_mem F hB).2
  filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hFB), self_mem_nhdsWithin] with u hu huI
  have hq := increasingCDFQuantileOn_mem F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr u huI
  have he := increasingCDFQuantileOn_right_inverse F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr u huI
  change 0 < q u at hq
  change F (q u) = u at he
  have hBq : B < q u := by
    change 0 < q u at hq
    change F (q u) = u at he
    by_contra hn
    have h := hm.monotoneOn (show 0 ≤ q u from hq.le) hB.le (le_of_not_gt hn)
    rw [he] at h
    exact (not_le_of_gt hu) h
  exact (le_max_left b 1).trans hBq.le

end
end GinibrePoincare
