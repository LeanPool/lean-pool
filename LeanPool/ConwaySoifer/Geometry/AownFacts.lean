/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Normalization
import Mathlib.Tactic

/-!
# §6: the strengthening of `Aown` for `s ≤ 1/14`

In local coordinates `p = v₀ + x u + y v` (`u` towards `v₁`, `v` towards `v₅`) the owner `S₀`
of an `Aown` cover satisfies `0 ≤ x ≤ 2 s (y + 1/2)` on the hexagon (face inequality of the
full endpoint together with `M₀ = v₀ - v/2 ∈ S₀`) and `y < 3/5` (diameter with `M₀`), hence
`|S₀ ∩ H| ≤ (24/25) s` in volume units.  If another side owner were overfull or contained an
external corner midpoint, the area budget would be violated for `s ≤ 1/14`.
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

/-! ### Local coordinates at `v₀` -/

/-- The first coefficient in local coordinates at the first hexagon vertex. -/
def locX (p : Point) : ℝ := 1 - p.1
/-- The second coefficient in local coordinates at the first hexagon vertex. -/
def locY (p : Point) : ℝ := 1 - p.1 - p.2

theorem loc_decomp (p : Point) :
    p = vertex 0 + locX p • sideDirection 0 true + locY p • sideDirection 0 false := by
  rcases p with ⟨a, b⟩
  apply Prod.ext <;> simp [locX, locY, vertex, sideDirection, neighbor]

theorem extMid0_decomp :
    extMid0 = vertex 0 + (0 : ℝ) • sideDirection 0 true + (-1 / 2 : ℝ) • sideDirection 0 false := by
  apply Prod.ext <;> simp [extMid0, vertex, sideDirection, neighbor]; norm_num

theorem sqDist_extMid0 (p : Point) :
    sqDist p extMid0 = locX p ^ 2 - locX p * (locY p + 1 / 2) + (locY p + 1 / 2) ^ 2 := by
  rcases p with ⟨a, b⟩; simp [sqDist, extMid0, locX, locY]; ring

/-- The region containing `S₀ ∩ H`. -/
def aownRegion (s : ℝ) : Set Point :=
  {p | 0 ≤ locY p ∧ locY p ≤ 3 / 5 ∧ 0 ≤ locX p ∧ locX p ≤ 2 * s * (locY p + 1 / 2)}

/-- The same region in the coordinates `(x, y)`. -/
def aownBox (s : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.2 ∧ q.2 ≤ 3 / 5 ∧ 0 ≤ q.1 ∧ q.1 ≤ 2 * s * (q.2 + 1 / 2)}

theorem isClosed_aownBox (s : ℝ) : IsClosed (aownBox s) := by
  simp only [aownBox, Set.ofPred_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)) <;>
    exact isClosed_le (by fun_prop) (by fun_prop)

theorem aownBox_section (s : ℝ) (y : ℝ) :
    volume ((fun x => (x, y)) ⁻¹' aownBox s) =
      Set.indicator (Set.Icc (0 : ℝ) (3 / 5)) (fun y => ENNReal.ofReal (2 * s * (y + 1 / 2))) y :=
          by
  by_cases hy : y ∈ Set.Icc (0 : ℝ) (3 / 5)
  · have he : (fun x => (x, y)) ⁻¹' aownBox s = Set.Icc 0 (2 * s * (y + 1 / 2)) := by
      ext x
      simp only [Set.mem_preimage, aownBox, Set.mem_ofPred_eq, Set.mem_Icc]
      constructor
      · rintro ⟨-, -, h3, h4⟩; exact ⟨h3, h4⟩
      · rintro ⟨h3, h4⟩; exact ⟨hy.1, hy.2, h3, h4⟩
    rw [he, Real.volume_Icc, Set.indicator_of_mem hy, sub_zero]
  · have he : (fun x => (x, y)) ⁻¹' aownBox s = ∅ := by
      ext x
      simp only [Set.mem_preimage, aownBox, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -, -⟩
      exact hy ⟨h1, h2⟩
    rw [he, measure_empty, Set.indicator_of_notMem hy]

theorem integral_aown (s : ℝ) : ∫ y in (0 : ℝ)..(3 / 5), 2 * s * (y + 1 / 2) = 24 * s / 25 := by
  have h1 : ∫ y in (0 : ℝ)..(3 / 5), 2 * s * (y + 1 / 2) =
      2 * s * ∫ y in (0 : ℝ)..(3 / 5), (y + 1 / 2) := by
    rw [← intervalIntegral.integral_const_mul]
  rw [h1, intervalIntegral.integral_add intervalIntegral.intervalIntegrable_id
    intervalIntegrable_const, integral_id, intervalIntegral.integral_const]
  simp
  ring

theorem volume_aownBox (s : ℝ) (hs : 0 ≤ s) : volume (aownBox s) = ENNReal.ofReal (24 * s / 25) :=
    by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (isClosed_aownBox s).measurableSet]
  simp_rw [aownBox_section s]
  rw [lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal (Continuous.integrableOn_Icc (by fun_prop))
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun y hy => by
        simp only [Pi.zero_apply]; nlinarith [hy.1])),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5),
    integral_aown]

theorem aownRegion_eq_image (s : ℝ) :
    aownRegion s = areaTriMap (vertex 0) (sideDirection 0 true) (sideDirection 0 false) '' aownBox s
        := by
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

theorem volume_aownRegion (s : ℝ) (hs : 0 ≤ s) :
    volume (aownRegion s) = ENNReal.ofReal (24 * s / 25) := by
  rw [aownRegion_eq_image, areaTriMap_image, volume_image_add_left, volume_image_areaLinMap,
    volume_aownBox s hs]
  have : cross (sideDirection 0 true) (sideDirection 0 false) = 1 := by
    simp [cross, sideDirection, neighbor, vertex]
  rw [this, abs_one, ENNReal.ofReal_one, one_mul]

/-! ### `S₀ ∩ H` lies in the region -/

theorem Canonical.toMinAt {c : ContactCase} {T : Configuration} {r s : ℝ} (H : Canonical c T r s) :
    MinAt T r s 0 c.right where
  common := H.common
  covers := H.covers
  r_lt := H.r_lt
  anchored := H.anchored
  s_pos := H.s_pos
  side_min := fun i right => H.side_min i right
  attained := H.endpoint

theorem Canonical.aown_subset {T : Configuration} {r s : ℝ} (H : Canonical .Aown T r s)
    (hs : s ≤ 1 / 10) : (T 1).carrier ∩ hexagon ⊆ aownRegion s := by
  rintro p ⟨hp, hpH⟩
  obtain ⟨h1, h2, h3⟩ := hpH
  rw [abs_le] at h1 h2 h3
  have hv : vertex 0 ∈ (T 1).carrier := by
    have := H.anchored 1; simpa [anchor, vertex] using this
  have hσ : 0 < (T 1).side := by
    rw [H.common]; exact H.r_pos
  obtain ⟨O⟩ := (T 1).exists_orientation hσ
  obtain ⟨j, hj, hface⟩ := O.full_endpoint hv (sideDirection_unit 0 true)
  have hend : rayLen (T 1) (vertex 0) (sideDirection 0 true) = s := H.endpoint
  rw [hend] at hface
  set n := rotPow j O.dir
  set u := sideDirection 0 true
  set v := sideDirection 0 false
  have hM := H.contact.2.2
  have hfp := hface p hp
  have hfM := hface extMid0 hM
  rw [loc_decomp p] at hfp
  rw [extMid0_decomp] at hfM
  simp only [linePoint, cross_add_right, cross_smul_right] at hfp hfM
  set x := locX p
  set y := locY p
  have hx0 : 0 ≤ x := by
    simp only [x, locX]; linarith
  have hy0 : 0 ≤ y := by
    simp only [y, locY]; linarith
  -- face inequality
  have hB : -(2 * s) * cross n u ≤ cross n v := by
    linarith
  have hxle : x ≤ 2 * s * (y + 1 / 2) := by
    have hyB : y * (-(2 * s) * cross n u) ≤ y * cross n v := mul_le_mul_of_nonneg_left hB hy0
    have : x * cross n u ≤ (2 * s * (y + 1 / 2)) * cross n u := by
      nlinarith
    exact le_of_mul_le_mul_right this hj
  -- diameter with `M₀`
  have hd := (T 1).sqDist_le hp hM
  rw [sqDist_extMid0, H.common] at hd
  have hr2 : r ^ 2 < 1 := by
    nlinarith [H.r_pos, H.r_lt]
  have hf : (x - 2 * s * (y + 1 / 2)) * (x + 2 * s * (y + 1 / 2) - (y + 1 / 2)) ≥ 0 := by
    apply mul_nonneg_of_nonpos_of_nonpos <;> nlinarith
  have hcoef : 21 / 25 ≤ 1 - 2 * s + 4 * s ^ 2 := by
    nlinarith [H.s_pos]
  have hw : (y + 1 / 2) ^ 2 < 25 / 21 := by
    nlinarith
  have hy : y ≤ 3 / 5 := by
    nlinarith
  exact ⟨hy0, hy, hx0, hxle⟩

theorem Canonical.aown_inter_le {T : Configuration} {r s : ℝ} (H : Canonical .Aown T r s)
    (hs : s ≤ 1 / 10) : (volume ((T 1).carrier ∩ hexagon)).toReal ≤ 24 * s / 25 := by
  have := measure_mono (μ := volume) (H.aown_subset hs)
  rw [volume_aownRegion s H.s_pos.le] at this
  calc (volume ((T 1).carrier ∩ hexagon)).toReal ≤ (ENNReal.ofReal (24 * s / 25)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top this
    _ = 24 * s / 25 := ENNReal.toReal_ofReal (by linarith [H.s_pos])

/-! ### The budget -/

/-- Normalised loss of side owner `i`. -/
def sideLoss (T : Configuration) (i : Fin 6) : ℝ :=
  2 * (volume ((T (sideIndex i)).carrier \ hexagon)).toReal

theorem Canonical.loss_zero {T : Configuration} {r s : ℝ} (H : Canonical .Aown T r s)
    (hs : s ≤ 1 / 10) : r ^ 2 - 48 * s / 25 ≤ sideLoss T 0 := by
  have hfinI : volume ((T 1).carrier ∩ hexagon) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt (T 1).volume_carrier_lt_top).ne
  have hfinO : volume ((T 1).carrier \ hexagon) ≠ ⊤ :=
    ((measure_mono Set.sdiff_subset).trans_lt (T 1).volume_carrier_lt_top).ne
  have hsplit : (volume ((T 1).carrier ∩ hexagon)).toReal + (volume ((T 1).carrier \
      hexagon)).toReal =
      r ^ 2 / 2 := by
    rw [← ENNReal.toReal_add hfinI hfinO, measure_inter_add_sdiff _ measurableSet_hexagon,
      (T 1).volume_carrier, H.common, ENNReal.toReal_ofReal (by positivity)]
  have := H.aown_inter_le hs
  unfold sideLoss
  change r ^ 2 - 48 * s / 25 ≤ 2 * (volume ((T 1).carrier \ hexagon)).toReal
  linarith

theorem Canonical.loss_ge_sq {c : ContactCase} {T : Configuration} {r s : ℝ} (H : Canonical c T r s)
    (i : Fin 6) : s ^ 2 ≤ sideLoss T i := H.toMinAt.outside_ge i

theorem Canonical.loss_overfull {c : ContactCase} {T : Configuration} {r s : ℝ}
    (H : Canonical c T r s) (i : Fin 6)
    (hover : r < rayLen (T (sideIndex i)) (vertex i) (sideDirection i false) +
      rayLen (T (sideIndex i)) (vertex i) (sideDirection i true)) : r ^ 2 / 4 ≤ sideLoss T i := by
  have hv := H.toMinAt.vertex_mem i
  set L := rayLen (T (sideIndex i)) (vertex i) (sideDirection i false)
  set R := rayLen (T (sideIndex i)) (vertex i) (sideDirection i true)
  have hL0 : 0 ≤ L := rayLen_nonneg _ hv (sideDirection_unit i false)
  have hR0 : 0 ≤ R := rayLen_nonneg _ hv (sideDirection_unit i true)
  have hw := wedge_area_strong i (T (sideIndex i)) (by rw [H.common]; exact H.r_pos) hL0 hR0 hv
    (rayLen_endpoint_mem _ hv (sideDirection_unit i false))
    (rayLen_endpoint_mem _ hv (sideDirection_unit i true)) (by rw [H.common]; exact hover)
  have hmax : r ^ 2 / 4 ≤ max (L ^ 2) (R ^ 2) := by
    rcases le_total L R with h | h
    · apply le_max_of_le_right
      have hR : r / 2 < R := by
        linarith
      nlinarith [H.r_pos, mul_pos (sub_pos.2 hR) (by linarith [H.r_pos] : (0 : ℝ) < R + r / 2)]
    · apply le_max_of_le_left
      have hL : r / 2 < L := by
        linarith
      nlinarith [H.r_pos, mul_pos (sub_pos.2 hL) (by linarith [H.r_pos] : (0 : ℝ) < L + r / 2)]
  unfold sideLoss; linarith

theorem Canonical.loss_mid {c : ContactCase} {T : Configuration} {r s : ℝ} (H : Canonical c T r s)
    (i : Fin 6) (j : Fin 3) (m : Fin 2) (hm : cornerMid j m ∈ (T (sideIndex i)).carrier) :
    r ^ 2 / 4 ≤ sideLoss T i := by
  have hcost := midpointCost_volume (T (sideIndex i)) (by rw [H.common]; exact H.r_pos)
    (by rw [H.common]; exact H.r_lt.le) (cornerLevel j) (cornerLevel_normSq j) hm (cornerLevel_mid j
        m)
  rw [H.common] at hcost
  have hsub : (T (sideIndex i)).carrier ∩ {p | 1 < cross (cornerLevel j) p} ⊆
      (T (sideIndex i)).carrier \ hexagon := by
    rintro p ⟨hp, hl⟩
    refine ⟨hp, fun hH => ?_⟩
    have := hexagon_subset_level j hH
    simp only [Set.mem_ofPred_eq] at hl this
    linarith
  have hfin : volume ((T (sideIndex i)).carrier \ hexagon) ≠ ⊤ :=
    ((measure_mono Set.sdiff_subset).trans_lt (T (sideIndex i)).volume_carrier_lt_top).ne
  have := ENNReal.toReal_mono hfin (measure_mono hsub)
  unfold sideLoss; linarith

/-- The budget of an `Aown` cover with `s ≤ 1/14`: no other side owner can lose `r²/4`. -/
theorem Canonical.aown_budget {T : Configuration} {r s : ℝ} (H : Canonical .Aown T r s)
    (hs : s ≤ 1 / 14) (i : Fin 6) (hi : i ≠ 0) (hD : r ^ 2 / 4 ≤ sideLoss T i) : False := by
  have hbudget := H.toMinAt.toAnchored.area_budget
  have hout : ∀ k, H.toMinAt.toAnchored.outside k = sideLoss T k := fun k => rfl
  have hhelp : ∑ j : Fin 3, H.toMinAt.toAnchored.cornerHelp j < 3 * (r ^ 2 / 23) := by
    have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => H.toMinAt.cornerHelp_lt j)
    simpa using this
  have hs10 : s ≤ 1 / 10 := by
    linarith
  have h0 := H.loss_zero hs10
  have hsq := H.loss_ge_sq
  have hlow : ∀ k : Fin 6,
      (if k = 0 then r ^ 2 - 48 * s / 25 else if k = i then r ^ 2 / 4 else s ^ 2) ≤ sideLoss T k :=
          by
    intro k
    split_ifs with hk0 hki
    · subst hk0; exact h0
    · subst hki; exact hD
    · exact hsq k
  have hsum' := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 6))) => hlow k)
  have hval : ∑ k : Fin 6,
      (if k = 0 then r ^ 2 - 48 * s / 25 else if k = i then r ^ 2 / 4 else s ^ 2) =
        r ^ 2 - 48 * s / 25 + r ^ 2 / 4 + 4 * s ^ 2 := by
    fin_cases i <;> simp [Fin.sum_univ_six] at hi ⊢ <;> ring
  rw [hval] at hsum'
  have hsum : ∑ k : Fin 6, sideLoss T k ≥ r ^ 2 - 48 * s / 25 + r ^ 2 / 4 + 4 * s ^ 2 := hsum'
  have hbudget' : ∑ k : Fin 6, sideLoss T k ≤
      7 * r ^ 2 - 6 + ∑ j : Fin 3, H.toMinAt.toAnchored.cornerHelp j := hbudget
  have hr2 : r ^ 2 < 1 := by
    nlinarith [H.r_pos, H.r_lt]
  have hkey : 0 ≤ (1 / 14 - s) * (6 / 25 - s) := mul_nonneg (by linarith) (by linarith)
  have hkey' : 0 ≤ s ^ 2 - (1 / 14 + 6 / 25) * s + 6 / 350 := by
    nlinarith [hkey]
  linarith [H.s_pos]

end ConwaySoifer
