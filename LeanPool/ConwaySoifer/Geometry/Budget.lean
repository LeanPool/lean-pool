/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.CornerCap
public import LeanPool.ConwaySoifer.Geometry.Normal
public import LeanPool.ConwaySoifer.Geometry.Oblique
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# The area budget with corner help and the bound `s < 11/25`

For an anchored cover with all twelve full side sections at least `s`: every side owner loses
volume at least `s²/2` outside the hexagon (wedge lemma), every corner owner contributes less
than `r²/46` inside the hexagon (corner cap), and the Lebesgue budget `area_budget` gives
`6 s² < 7 r² - 6 + 3 r²/23 < 26/23`, hence `s² < 13/69` and `s < 11/25`.
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

/-! ### Cap lemmas for an equilateral triangle -/

theorem range_eq_triple (Q : EquilateralTriangle) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    ({Q.vertices i, Q.vertices j, Q.vertices k} : Set Point) = Set.range Q.vertices := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨i, rfl⟩
    · exact ⟨j, rfl⟩
    · exact ⟨k, rfl⟩
  · rintro ⟨l, rfl⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all

theorem det_perm_ne_zero (Q : EquilateralTriangle) (hσ : 0 < Q.side) (i j k : Fin 3) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) : triangleDet (Q.vertices i) (Q.vertices j) (Q.vertices k) ≠ 0 := by
  have h := Q.det_ne_zero hσ
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all only [Fin.isValue, ne_eq, Fin.zero_eta,
      not_true_eq_false, Fin.mk_one, zero_ne_one, not_false_eq_true, Fin.reduceFinMk, Fin.reduceEq,
      one_ne_zero] <;>
    first
    | exact h
    | (rw [triangleDet_rotate]; exact h)
    | (rw [← triangleDet_rotate]; exact h)
    | (rw [triangleDet_swap]; exact neg_ne_zero.mpr h)
    | (rw [triangleDet_swap, triangleDet_rotate]; exact neg_ne_zero.mpr h)
    | (rw [triangleDet_swap, ← triangleDet_rotate]; exact neg_ne_zero.mpr h)

theorem carrier_eq_hull_perm (Q : EquilateralTriangle) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : Q.carrier = convexHull ℝ {Q.vertices i, Q.vertices j, Q.vertices k} := by
  rw [EquilateralTriangle.carrier, range_eq_triple Q i j k hij hik hjk]

theorem volume_hull_perm (Q : EquilateralTriangle) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    volume (convexHull ℝ {Q.vertices i, Q.vertices j, Q.vertices k}) =
      ENNReal.ofReal (Q.side ^ 2 / 2) := by
  rw [← carrier_eq_hull_perm Q i j k hij hik hjk, Q.volume_carrier]

/-- The other two indices of a vertex, in some order. -/
theorem other_indices (i : Fin 3) : ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  fin_cases i
  · exact ⟨1, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩

/-- Universal corner cap: a triangle of side `σ ≤ 1` containing a point of level `2` has
volume `< σ²/46` at levels `≤ 1`. -/
theorem cornerCap_volume (Q : EquilateralTriangle) (hσ : 0 < Q.side) (hσ1 : Q.side ≤ 1)
    (u : Point) (hu : normSq u = 1) {w : Point} (hw : w ∈ Q.carrier) (hw2 : cross u w = 2) :
    (volume (Q.carrier ∩ {p | cross u p ≤ 1})).toReal < Q.side ^ 2 / 46 := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu; simp [normSq] at hu
  obtain ⟨i, hi, hwi⟩ := cross_le_max_vertex Q u hw
  obtain ⟨j, k, hij, hik, hjk⟩ := other_indices i
  have hc2 : 2 ≤ cross u (Q.vertices i) := hw2 ▸ hwi
  rcases le_total (cross u (Q.vertices j)) (cross u (Q.vertices k)) with hjk' | hjk'
  · rw [carrier_eq_hull_perm Q j k i hjk hij.symm hik.symm]
    exact cornerCap_aux hσ hσ1 u hu0 (det_perm_ne_zero Q hσ j k i hjk hij.symm hik.symm)
      (volume_hull_perm Q j k i hjk hij.symm hik.symm)
      (level_identity Q hσ u hu j k i hjk hij.symm hik.symm) hjk' (hi k) hc2
  · rw [carrier_eq_hull_perm Q k j i hjk.symm hik.symm hij.symm]
    exact cornerCap_aux hσ hσ1 u hu0 (det_perm_ne_zero Q hσ k j i hjk.symm hik.symm hij.symm)
      (volume_hull_perm Q k j i hjk.symm hik.symm hij.symm)
      (level_identity Q hσ u hu k j i hjk.symm hik.symm hij.symm) hjk' (hi j) hc2

/-- Midpoint cost: a triangle of side `σ ≤ 1` containing a point of level `3/2` has volume
`≥ σ²/8` at levels `> 1`. -/
theorem midpointCost_volume (Q : EquilateralTriangle) (hσ : 0 < Q.side) (hσ1 : Q.side ≤ 1)
    (u : Point) (hu : normSq u = 1) {w : Point} (hw : w ∈ Q.carrier) (hw2 : cross u w = 3 / 2) :
    Q.side ^ 2 / 8 ≤ (volume (Q.carrier ∩ {p | 1 < cross u p})).toReal := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu; simp [normSq] at hu
  obtain ⟨i, hi, hwi⟩ := cross_le_max_vertex Q u hw
  obtain ⟨j, k, hij, hik, hjk⟩ := other_indices i
  have hc2 : 3 / 2 ≤ cross u (Q.vertices i) := hw2 ▸ hwi
  rcases le_total (cross u (Q.vertices j)) (cross u (Q.vertices k)) with hjk' | hjk'
  · rw [carrier_eq_hull_perm Q j k i hjk hij.symm hik.symm]
    exact midpointCost_aux hσ hσ1 u hu0 (det_perm_ne_zero Q hσ j k i hjk hij.symm hik.symm)
      (volume_hull_perm Q j k i hjk hij.symm hik.symm)
      (level_identity Q hσ u hu j k i hjk hij.symm hik.symm) hjk' (hi k) hc2
  · rw [carrier_eq_hull_perm Q k j i hjk.symm hik.symm hij.symm]
    exact midpointCost_aux hσ hσ1 u hu0 (det_perm_ne_zero Q hσ k j i hjk.symm hik.symm hij.symm)
      (volume_hull_perm Q k j i hjk.symm hik.symm hij.symm)
      (level_identity Q hσ u hu k j i hjk.symm hik.symm hij.symm) hjk' (hi j) hc2

/-! ### Level forms of the corner cells -/

/-- `cross (cornerLevel j) p` is `a + b`, `-a`, `-b` for `j = 0, 1, 2`. -/
def cornerLevel : Fin 3 → Point := ![(1, -1), (0, 1), (-1, 0)]

theorem cornerLevel_normSq (j : Fin 3) : normSq (cornerLevel j) = 1 := by
  fin_cases j <;> simp [cornerLevel, normSq]

theorem cornerLevel_corner (j : Fin 3) : cross (cornerLevel j) (corner j) = 2 := by
  fin_cases j <;> simp [cornerLevel, corner, cross]; norm_num

theorem cornerLevel_mid (j : Fin 3) (m : Fin 2) : cross (cornerLevel j) (cornerMid j m) = 3 / 2 :=
    by
  fin_cases j <;> fin_cases m <;>
    simp [cornerLevel, cornerMid, cornerDirection, corner, vertex, cross] <;> norm_num

theorem hexagon_subset_level (j : Fin 3) : hexagon ⊆ {p | cross (cornerLevel j) p ≤ 1} := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  rw [abs_le] at h1 h2 h3
  fin_cases j <;> simp [cornerLevel, cross] <;> linarith

/-! ### The budget -/

/-- Forget the attained-minimum data while retaining the relabeled subunit cover. -/
def MinAt.toAnchored {T : Configuration} {r s : ℝ} {i₀ : Fin 6} {r₀ : Bool}
    (h : MinAt T r s i₀ r₀) : AnchoredCover r :=
  ⟨T, h.common, h.covers, h.r_lt, h.anchored⟩

theorem MinAt.r_pos {T : Configuration} {r s : ℝ} {i₀ : Fin 6} {r₀ : Bool}
    (h : MinAt T r s i₀ r₀) : 0 < r := h.toAnchored.pos

theorem MinAt.side_eq {T : Configuration} {r s : ℝ} {i₀ : Fin 6} {r₀ : Bool}
    (h : MinAt T r s i₀ r₀) (i : Fin 10) : (T i).side = r := h.common i

/-- The side point at parameter `t ≤ s` lies in `S_i`. -/
theorem MinAt.sidePt_mem {T : Configuration} {r s : ℝ} {i₀ : Fin 6} {r₀ : Bool}
    (h : MinAt T r s i₀ r₀) (i : Fin 6) (right : Bool) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ s) :
    linePoint (vertex i) (sideDirection i right) t ∈ (T (sideIndex i)).carrier := by
  have hv : vertex i ∈ (T (sideIndex i)).carrier := by
    have := h.anchored (sideIndex i); rwa [anchor_sideIndex] at this
  exact (linePoint_mem_iff_le_rayLen _ hv (sideDirection_unit i right) ht0).mpr
    (ht.trans (h.side_min i right))

/-- Each side owner loses at least `s²` (normalised area) outside the hexagon. -/
theorem MinAt.outside_ge {T : Configuration} {r s : ℝ} {i₀ : Fin 6} {r₀ : Bool}
    (h : MinAt T r s i₀ r₀) (i : Fin 6) : s ^ 2 ≤ h.toAnchored.outside i := by
  have hv : vertex i ∈ (T (sideIndex i)).carrier := by
    have := h.anchored (sideIndex i); rwa [anchor_sideIndex] at this
  have hw := wedge_area_weak i (T (sideIndex i)) (by rw [h.side_eq]; exact h.r_pos) h.s_pos.le
    h.s_pos.le hv (h.sidePt_mem i false h.s_pos.le le_rfl) (h.sidePt_mem i true h.s_pos.le le_rfl)
  rw [min_self] at hw
  change s ^ 2 ≤ 2 * (volume ((T (sideIndex i)).carrier \ hexagon)).toReal
  linarith

/-- Each corner owner helps less than `r²/23` inside the hexagon. -/
theorem MinAt.cornerHelp_lt {T : Configuration} {r s : ℝ} {i₀ : Fin 6} {r₀ : Bool}
    (h : MinAt T r s i₀ r₀) (j : Fin 3) : h.toAnchored.cornerHelp j < r ^ 2 / 23 := by
  have hw : corner j ∈ (T (cornerIndex j)).carrier := by
    have := h.anchored (cornerIndex j); rwa [anchor_cornerIndex] at this
  have hcap := cornerCap_volume (T (cornerIndex j)) (by rw [h.side_eq]; exact h.r_pos)
    (by rw [h.side_eq]; exact h.r_lt.le) (cornerLevel j) (cornerLevel_normSq j) hw
    (cornerLevel_corner j)
  rw [h.side_eq] at hcap
  have hsub : (T (cornerIndex j)).carrier ∩ hexagon ⊆
      (T (cornerIndex j)).carrier ∩ {p | cross (cornerLevel j) p ≤ 1} :=
    Set.inter_subset_inter_right _ (hexagon_subset_level j)
  have hfin : volume ((T (cornerIndex j)).carrier ∩ {p | cross (cornerLevel j) p ≤ 1}) ≠ ⊤ :=
    ne_top_of_le_ne_top (T (cornerIndex j)).volume_carrier_lt_top.ne
      (measure_mono Set.inter_subset_left)
  have hle := ENNReal.toReal_mono hfin (measure_mono hsub)
  change 2 * (volume ((T (cornerIndex j)).carrier ∩ hexagon)).toReal < r ^ 2 / 23
  linarith

/-- The parameter bound `s < 11/25`. -/
theorem MinAt.s_lt {T : Configuration} {r s : ℝ} {i₀ : Fin 6} {r₀ : Bool}
    (h : MinAt T r s i₀ r₀) : s < 11 / 25 := by
  have hbudget := h.toAnchored.area_budget
  have hout : 6 * s ^ 2 ≤ ∑ i : Fin 6, h.toAnchored.outside i := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 6))) => h.outside_ge i)
    simpa using this
  have hhelp : ∑ j : Fin 3, h.toAnchored.cornerHelp j < 3 * (r ^ 2 / 23) := by
    have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => h.cornerHelp_lt j)
    simpa using this
  have hr2 : r ^ 2 < 1 := by
    nlinarith [h.r_pos, h.r_lt]
  have hs2 : s ^ 2 < 13 / 69 := by
    linarith
  nlinarith [h.s_pos]

end ConwaySoifer
