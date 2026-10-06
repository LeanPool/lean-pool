/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.AownFacts
import Mathlib.Tactic

/-!
# §8.1: the small `Across` regime `s ≤ 1/400`

Let `c` be the full section of `S₀` from `v₀` towards `w₀` (direction `(0, 1)`).  The face
inequality of the internal endpoint together with `(1, c) ∈ S₀` gives `0 ≤ x ≤ s + (s/c) y` on
`S₀ ∩ H` in the local coordinates of `v₀`, and the diameter with `v₀` gives `y < 6/5`; hence
`|S₀ ∩ H| ≤ 6s/5 + 18 s/(25 c)`.  With `M₀ ∈ S₁` the budget forces `c < 16 s`.  The point
`(1, c)` is reached by `A₀` or `S₁` (closedness); `A₀` is excluded since `M₀ ∉ A₀`, so
`(1, c) ∈ S₁`, hence `(1, 16 s) ∈ S₁`, and the four points `v₁`, `(-s, 1)`, `M₀`, `(1, 16 s)`
are excluded by the checker for `s ≤ 1/400`.
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
namespace ConwaySoifer

/-! ### A generic wedge region at `v₀` -/

/-- The image of the local wedge trapezoid in triangular coordinates. -/
def wedgeRegion (A B Y : ℝ) : Set Point :=
  {p | 0 ≤ locY p ∧ locY p ≤ Y ∧ 0 ≤ locX p ∧ locX p ≤ A + B * locY p}

/-- A closed trapezoidal region in local wedge coordinates. -/
def wedgeBox (A B Y : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.2 ∧ q.2 ≤ Y ∧ 0 ≤ q.1 ∧ q.1 ≤ A + B * q.2}

theorem isClosed_wedgeBox (A B Y : ℝ) : IsClosed (wedgeBox A B Y) := by
  simp only [wedgeBox, Set.ofPred_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)) <;>
    exact isClosed_le (by fun_prop) (by fun_prop)

theorem wedgeBox_section (A B Y : ℝ) (y : ℝ) :
    volume ((fun x => (x, y)) ⁻¹' wedgeBox A B Y) =
      Set.indicator (Set.Icc (0 : ℝ) Y) (fun y => ENNReal.ofReal (A + B * y)) y := by
  by_cases hy : y ∈ Set.Icc (0 : ℝ) Y
  · have he : (fun x => (x, y)) ⁻¹' wedgeBox A B Y = Set.Icc 0 (A + B * y) := by
      ext x
      simp only [Set.mem_preimage, wedgeBox, Set.mem_ofPred_eq, Set.mem_Icc]
      constructor
      · rintro ⟨-, -, h3, h4⟩; exact ⟨h3, h4⟩
      · rintro ⟨h3, h4⟩; exact ⟨hy.1, hy.2, h3, h4⟩
    rw [he, Real.volume_Icc, Set.indicator_of_mem hy, sub_zero]
  · have he : (fun x => (x, y)) ⁻¹' wedgeBox A B Y = ∅ := by
      ext x
      simp only [Set.mem_preimage, wedgeBox, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -, -⟩
      exact hy ⟨h1, h2⟩
    rw [he, measure_empty, Set.indicator_of_notMem hy]

theorem integral_wedge (A B Y : ℝ) : ∫ y in (0 : ℝ)..Y, (A + B * y) = A * Y + B * Y ^ 2 / 2 := by
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_id.const_mul B), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id]
  simp
  ring

theorem volume_wedgeBox (A B Y : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hY : 0 ≤ Y) :
    volume (wedgeBox A B Y) = ENNReal.ofReal (A * Y + B * Y ^ 2 / 2) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (isClosed_wedgeBox A B Y).measurableSet]
  simp_rw [wedgeBox_section A B Y]
  rw [lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal (Continuous.integrableOn_Icc (by fun_prop))
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun y hy => by
        simp only [Pi.zero_apply]; nlinarith [hy.1])),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hY, integral_wedge]

theorem wedgeRegion_eq_image (A B Y : ℝ) :
    wedgeRegion A B Y =
      areaTriMap (vertex 0) (sideDirection 0 true) (sideDirection 0 false) '' wedgeBox A B Y := by
  ext p
  constructor
  · intro hp
    refine ⟨(locX p, locY p), hp, ?_⟩
    rw [areaTriMap_apply, areaLinMap_apply, ← add_assoc]
    exact (loc_decomp p).symm
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := hq
    rw [areaTriMap_apply, areaLinMap_apply, ← add_assoc]
    have hx : locX (vertex 0 + q.1 • sideDirection 0 true + q.2 • sideDirection 0 false) = q.1 := by
      simp [locX, vertex, sideDirection, neighbor]
    have hy : locY (vertex 0 + q.1 • sideDirection 0 true + q.2 • sideDirection 0 false) = q.2 := by
      simp [locY, vertex, sideDirection, neighbor]
    exact ⟨by rw [hy]; exact h1, by rw [hy]; exact h2, by rw [hx]; exact h3, by rw [hx, hy]; exact
        h4⟩

theorem volume_wedgeRegion (A B Y : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hY : 0 ≤ Y) :
    volume (wedgeRegion A B Y) = ENNReal.ofReal (A * Y + B * Y ^ 2 / 2) := by
  rw [wedgeRegion_eq_image, areaTriMap_image, volume_image_add_left, volume_image_areaLinMap,
    volume_wedgeBox A B Y hA hB hY]
  have : cross (sideDirection 0 true) (sideDirection 0 false) = 1 := by
    simp [cross, sideDirection, neighbor, vertex]
  rw [this, abs_one, ENNReal.ofReal_one, one_mul]

/-! ### The external section `c` of `S₀` -/

/-- The direction from `v₀` to `w₀`. -/
def upDir : Point := (0, 1)

theorem upDir_unit : sqDist upDir (0, 0) = 1 := by
  simp [upDir, sqDist]

theorem upPt_eq (t : ℝ) : linePoint (vertex 0) upDir t = ((1 : ℝ), t) := by
  apply Prod.ext <;> simp [linePoint, vertex, upDir]

theorem upPt_eq_cornerSeg (t : ℝ) :
    linePoint (vertex 0) upDir t = linePoint (corner 0) (cornerDirection 0 0) (1 - t) := by
  apply Prod.ext <;> simp [linePoint, vertex, upDir, corner, cornerDirection]

theorem sqDist_vertex0 (p : Point) :
    sqDist p (vertex 0) = locX p ^ 2 - locX p * locY p + locY p ^ 2 := by
  rcases p with ⟨a, b⟩; simp [sqDist, vertex, locX, locY]; ring

variable {T : Configuration} {r s : ℝ}

theorem Canonical.across_v0_mem (H : Canonical .Across T r s) : vertex 0 ∈ (T 1).carrier := by
  have := H.anchored 1; simpa [anchor, vertex] using this

/-- The external section is positive: no other owner contains `v₀`. -/
theorem Canonical.ext_pos (H : Canonical .Across T r s) :
    0 < rayLen (T 1) (vertex 0) upDir := by
  refine rayLen_pos_of_unique_owner T H.covers 1 H.across_v0_mem upDir_unit ?_ (b := 1) one_pos ?_
  · intro j hj hmem
    have hmem' : anchor 1 ∈ (T j).carrier := by
      simpa [anchor, vertex] using hmem
    exact hj (H.toMinAt.toAnchored.unique_anchor 1 j hmem').symm
  · intro t ht
    rw [upPt_eq_cornerSeg]
    exact cornerSeg_mem_target 0 0 (by linarith [ht.2]) (by linarith [ht.1])

theorem Canonical.ext_le (H : Canonical .Across T r s) : rayLen (T 1) (vertex 0) upDir ≤ r := by
  have := rayLen_le_side (T 1) H.across_v0_mem upDir_unit
  rwa [H.common] at this

/-- `S₀ ∩ H` lies in the wedge region `0 ≤ x ≤ s + (s/c) y`, `0 ≤ y ≤ 6/5`. -/
theorem Canonical.across_subset (H : Canonical .Across T r s) :
    (T 1).carrier ∩ hexagon ⊆ wedgeRegion s (s / rayLen (T 1) (vertex 0) upDir) (6 / 5) := by
  set c := rayLen (T 1) (vertex 0) upDir with hc
  have hc0 : 0 < c := H.ext_pos
  rintro p ⟨hp, hpH⟩
  obtain ⟨h1, h2, h3⟩ := hpH
  rw [abs_le] at h1 h2 h3
  have hv := H.across_v0_mem
  have hσ : 0 < (T 1).side := by
    rw [H.common]; exact H.r_pos
  obtain ⟨O⟩ := (T 1).exists_orientation hσ
  obtain ⟨j, hj, hface⟩ := O.full_endpoint hv (sideDirection_unit 0 true)
  have hend : rayLen (T 1) (vertex 0) (sideDirection 0 true) = s := H.endpoint
  rw [hend] at hface
  set n := rotPow j O.dir
  set u := sideDirection 0 true
  set v := sideDirection 0 false
  -- the point `(1, c)` lies in `S₀`
  have hq : linePoint (vertex 0) upDir c ∈ (T 1).carrier := rayLen_endpoint_mem (T 1) hv upDir_unit
  have hqdec : linePoint (vertex 0) upDir c =
      vertex 0 + (0 : ℝ) • sideDirection 0 true + (-c) • sideDirection 0 false := by
    apply Prod.ext <;> simp [linePoint, vertex, upDir, sideDirection, neighbor]
  have hfp := hface p hp
  have hfq := hface _ hq
  rw [loc_decomp p] at hfp
  rw [hqdec] at hfq
  simp only [linePoint, cross_add_right, cross_smul_right] at hfp hfq
  set x := locX p
  set y := locY p
  have hx0 : 0 ≤ x := by
    simp only [x, locX]; linarith
  have hy0 : 0 ≤ y := by
    simp only [y, locY]; linarith
  -- face inequality: `cross n v ≥ -(s/c) cross n u`
  have hB : -(s / c) * cross n u ≤ cross n v := by
    have : -c * cross n v ≤ s * cross n u := by
      linarith
    have h' : -(s / c) * cross n u * c ≤ cross n v * c := by
      have : -(s / c) * cross n u * c = -(s * cross n u) := by
        field_simp
      linarith
    exact le_of_mul_le_mul_right h' hc0
  have hxle : x ≤ s + s / c * y := by
    have hyB : y * (-(s / c) * cross n u) ≤ y * cross n v := mul_le_mul_of_nonneg_left hB hy0
    have : x * cross n u ≤ (s + s / c * y) * cross n u := by
      nlinarith
    exact le_of_mul_le_mul_right this hj
  -- diameter with `v₀`
  have hd := (T 1).sqDist_le hp hv
  rw [sqDist_vertex0, H.common] at hd
  have hr2 : r ^ 2 < 1 := by
    nlinarith [H.r_pos, H.r_lt]
  have hy : y ≤ 6 / 5 := by
    nlinarith [sq_nonneg (x - y / 2)]
  exact ⟨hy0, hy, hx0, hxle⟩

theorem Canonical.across_inter_le (H : Canonical .Across T r s) :
    (volume ((T 1).carrier ∩ hexagon)).toReal ≤
      s * (6 / 5) + s / rayLen (T 1) (vertex 0) upDir * (6 / 5) ^ 2 / 2 := by
  have hc0 : 0 < rayLen (T 1) (vertex 0) upDir := H.ext_pos
  have := measure_mono (μ := volume) H.across_subset
  rw [volume_wedgeRegion _ _ _ H.s_pos.le (div_nonneg H.s_pos.le hc0.le) (by norm_num)] at this
  calc (volume ((T 1).carrier ∩ hexagon)).toReal ≤
        (ENNReal.ofReal (s * (6 / 5) + s / rayLen (T 1) (vertex 0) upDir * (6 / 5) ^ 2 / 2)).toReal
            :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top this
    _ = _ := ENNReal.toReal_ofReal (by nlinarith [H.s_pos.le, div_nonneg H.s_pos.le hc0.le])

/-- The budget forces `c < 16 s`. -/
theorem Canonical.ext_lt (H : Canonical .Across T r s) (hs : s ≤ 1 / 400) :
    rayLen (T 1) (vertex 0) upDir < 16 * s := by
  set c := rayLen (T 1) (vertex 0) upDir with hc
  have hc0 : 0 < c := H.ext_pos
  by_contra hcon
  push Not at hcon
  -- loss of `S₀`
  have hfinI : volume ((T 1).carrier ∩ hexagon) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt (T 1).volume_carrier_lt_top).ne
  have hfinO : volume ((T 1).carrier \ hexagon) ≠ ⊤ :=
    ((measure_mono Set.sdiff_subset).trans_lt (T 1).volume_carrier_lt_top).ne
  have hsplit : (volume ((T 1).carrier ∩ hexagon)).toReal + (volume ((T 1).carrier \
      hexagon)).toReal =
      r ^ 2 / 2 := by
    rw [← ENNReal.toReal_add hfinI hfinO, measure_inter_add_sdiff _ measurableSet_hexagon,
      (T 1).volume_carrier, H.common, ENNReal.toReal_ofReal (by positivity)]
  have hinter := H.across_inter_le
  have hsc : s / c ≤ 1 / 16 := by
    rw [div_le_iff₀ hc0]; linarith
  have h0 : r ^ 2 - 12 * s / 5 - 9 / 100 ≤ sideLoss T 0 := by
    unfold sideLoss
    change r ^ 2 - 12 * s / 5 - 9 / 100 ≤ 2 * (volume ((T 1).carrier \ hexagon)).toReal
    have : s / c * (6 / 5) ^ 2 / 2 ≤ 9 / 200 := by
      nlinarith
    linarith
  -- `S₁` contains `M₀`
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
  have hsum : ∑ k : Fin 6, sideLoss T k ≥ r ^ 2 - 12 * s / 5 - 9 / 100 + r ^ 2 / 4 + 4 * s ^ 2 := by
    rw [Fin.sum_univ_six]
    linarith [hsq 2, hsq 3, hsq 4, hsq 5]
  have hr2 : r ^ 2 < 1 := by
    nlinarith [H.r_pos, H.r_lt]
  nlinarith [H.s_pos]

end ConwaySoifer
