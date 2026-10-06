/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Simplified.Geometry.Charging
import Mathlib.Tactic

/-!
# AcrossArea

Geometry and verified arithmetic for the Conway–Soifer covering theorem at n = 3.
-/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

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

@[expose] public section

noncomputable section
open MeasureTheory
namespace ConwaySoifer.Simplified

/-- A fixed triangular region used in the Across area-budget obstruction. -/
def acrossTop : Set Point := convexHull ℝ {(1, -1), (217 / 240, -217 / 240), (197 / 220, -1)}

theorem acrossTop_mem {p : Point} (hy : 1 ≤ locY p)
    (hh : locY p ≤ 1 + locX p) (hx : locX p ≤ 1 / 80 + locY p / 12) : p ∈ acrossTop := by
  rw [acrossTop, convexHull_triple_eq_image]
  refine ⟨(240 / 23 * (locX p - locY p + 1), 220 / 23 * (locY p - 1)), ?_, ?_⟩
  · change 0 ≤ _ ∧ 0 ≤ _ ∧ _ ≤ 1
    constructor
    · linarith
    constructor <;> linarith
  · ext <;> simp [areaTriMap_apply, areaLinMap_apply, locX, locY] <;> ring

theorem volume_acrossTop : volume acrossTop = ENNReal.ofReal (529 / 105600) := by
  rw [acrossTop, volume_triangle]
  norm_num [cross]

/-- Exact quadrilateral enclosure, split into its lower trapezoid and upper triangle. -/
theorem across_inter_small {T : Configuration} {r s : ℝ} (H : Canonical .Across T r s)
    (hs : s ≤ 1 / 80) (hc : 12 * s ≤ rayLen (T 1) (vertex 0) upDir) :
    2 * (volume ((T 1).carrier ∩ hexagon)).toReal ≤ 2083 / 17600 := by
  have hratio : s / rayLen (T 1) (vertex 0) upDir ≤ 1 / 12 := by
    rw [div_le_iff₀ H.ext_pos]; linarith
  have hsub : (T 1).carrier ∩ hexagon ⊆ wedgeRegion (1 / 80) (1 / 12) 1 ∪ acrossTop := by
    rintro p ⟨hp, hh⟩
    obtain ⟨hy0, _, hx0, hx⟩ := H.across_subset ⟨hp, hh⟩
    have hx' : locX p ≤ 1 / 80 + locY p / 12 := by
      have := mul_le_mul_of_nonneg_right hratio hy0
      linarith
    by_cases hy : locY p ≤ 1
    · exact Or.inl ⟨hy0, hy, hx0, by linarith⟩
    · right
      apply acrossTop_mem (le_of_not_ge hy) _ hx'
      have hb := (abs_le.mp hh.2.1).1
      dsimp [locX, locY]; linarith
  have hv := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
  rw [volume_wedgeRegion _ _ _ (by norm_num) (by norm_num) (by norm_num), volume_acrossTop,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)] at hv
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
  rw [ENNReal.toReal_ofReal (by norm_num)] at ht
  linarith

theorem across_ext_small {T : Configuration} {r s : ℝ} (H : Canonical .Across T r s)
    (hs : s ≤ 1 / 80) : rayLen (T 1) (vertex 0) upDir < 12 * s := by
  by_contra hc
  have hinter := across_inter_small H hs (le_of_not_gt hc)
  have hfinI : volume ((T 1).carrier ∩ hexagon) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt (T 1).volume_carrier_lt_top).ne
  have hfinO : volume ((T 1).carrier \ hexagon) ≠ ⊤ :=
    ((measure_mono Set.sdiff_subset).trans_lt (T 1).volume_carrier_lt_top).ne
  have hsplit : (volume ((T 1).carrier ∩ hexagon)).toReal + (volume ((T 1).carrier \
      hexagon)).toReal = r ^ 2 / 2 := by
    rw [← ENNReal.toReal_add hfinI hfinO, measure_inter_add_sdiff _ measurableSet_hexagon,
      (T 1).volume_carrier, H.common, ENNReal.toReal_ofReal (by positivity)]
  have h0 : r ^ 2 - 2083 / 17600 ≤ sideLoss T 0 := by
    unfold sideLoss
    change r ^ 2 - 2083 / 17600 ≤ 2 * (volume ((T 1).carrier \ hexagon)).toReal
    linarith
  have hD : r ^ 2 / 4 ≤ sideLoss T 1 := by
    have := H.contact.2.2
    rw [extMid0_eq] at this
    exact H.loss_mid 1 0 0 this
  have hsq := H.loss_ge_sq
  have hbudget : ∑ k : Fin 6, sideLoss T k ≤
      7 * r ^ 2 - 6 + ∑ j : Fin 3, H.toMinAt.toAnchored.cornerHelp j :=
          H.toMinAt.toAnchored.area_budget
  have hhelp : ∑ j : Fin 3, H.toMinAt.toAnchored.cornerHelp j < 3 * (r ^ 2 / 23) := by
    have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => H.toMinAt.cornerHelp_lt j)
    simpa using this
  have hsum : ∑ k : Fin 6, sideLoss T k ≥ r ^ 2 - 2083 / 17600 + r ^ 2 / 4 + 4 * s ^ 2 := by
    rw [Fin.sum_univ_six]
    linarith [hsq 2, hsq 3, hsq 4, hsq 5]
  have hr2 : r ^ 2 < 1 := by
    nlinarith [H.r_pos, H.r_lt]
  nlinarith [H.s_pos]

end ConwaySoifer.Simplified
