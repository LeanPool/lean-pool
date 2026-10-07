/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Geometry.Budget
public import LeanPool.ConwaySoifer.Geometry.Locality
public import LeanPool.ConwaySoifer.Geometry.Canonical
import Mathlib.Tactic

/-!
# Geometric normalization: every subunit cover is a canonical contact case

From a cover with the minimal full side section at `vertex 0` (`MinAt T r s 0 right`):

* the adaptive core `K_s` lies in the centre owner (Lemma A and the distance of the core
  vertices from the corner anchors);
* the bridge (Lemma B at `u = s/2`) keeps the minimal endpoint `p` out of the centre owner;
* `p` is reached by another owner (closedness), which by locality is the neighbouring side owner
  (external side) or the neighbouring side owner or corner owner (internal side);
* every corner section is at least `s` (the neighbouring side owners cannot continue the cover
  immediately after a shorter corner section);
* in the corner branch the external midpoint `M₀` is not in `A₀` (Lemma 4.2), so it belongs to
  `S₀` (`Aown`) or `S₁` (`Across`).
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
namespace ConwaySoifer

/-- Geometric interface for the adaptive-core obstruction. -/
def CoreObstruction : Prop :=
  ∀ {u : ℝ}, 0 < u → u ≤ 1 / 2 → ∀ i j : Fin 6,
    ∀ {Q : EquilateralTriangle}, 0 < Q.side → Q.side < 1 → vertex i ∈ Q.carrier →
    linePoint (vertex i) (sideDirection i false) u ∈ Q.carrier →
    linePoint (vertex i) (sideDirection i true) u ∈ Q.carrier →
    coreVertex u j ∈ Q.carrier → False

/-- Geometric interface for the bridge at the minimum endpoint. -/
def BridgeObstruction : Prop :=
  ∀ {u : ℝ}, 0 < u → u ≤ 1 / 3 → ∀ right : Bool,
    ∀ {Q : EquilateralTriangle}, 0 < Q.side → Q.side < 1 →
    (∀ j, coreVertex u j ∈ Q.carrier) →
    linePoint (vertex 0) (sideDirection 0 right) (2 * u) ∈ Q.carrier → False

/-- Geometric interface for the forbidden own midpoint in a corner branch. -/
def MidpointObstruction : Prop :=
  ∀ {u : ℝ}, 0 < u → u ≤ 1 / 2 →
    ∀ {Q : EquilateralTriangle}, 0 < Q.side → Q.side < 1 → corner 0 ∈ Q.carrier →
    linePoint (corner 0) (cornerDirection 0 1) u ∈ Q.carrier →
    linePoint (vertex 0) (sideDirection 0 true) u ∈ Q.carrier → extMid0 ∈ Q.carrier → False

variable {T : Configuration} {r s : ℝ} {right : Bool}

/-! ### Index bookkeeping -/

theorem owner_cases (k : Fin 10) : k = 0 ∨ (∃ i : Fin 6, k = sideIndex i) ∨ ∃ j : Fin 3, k =
    cornerIndex j := by
  fin_cases k
  · left; rfl
  · right; left; exact ⟨0, rfl⟩
  · right; left; exact ⟨1, rfl⟩
  · right; left; exact ⟨2, rfl⟩
  · right; left; exact ⟨3, rfl⟩
  · right; left; exact ⟨4, rfl⟩
  · right; left; exact ⟨5, rfl⟩
  · right; right; exact ⟨0, rfl⟩
  · right; right; exact ⟨1, rfl⟩
  · right; right; exact ⟨2, rfl⟩

theorem MinAt.side_pos' (h : MinAt T r s 0 right) (k : Fin 10) : 0 < (T k).side := by
  rw [h.side_eq]; exact h.r_pos
theorem MinAt.side_lt' (h : MinAt T r s 0 right) (k : Fin 10) : (T k).side < 1 := by
  rw [h.side_eq]; exact h.r_lt
theorem MinAt.vertex_mem (h : MinAt T r s 0 right) (i : Fin 6) :
    vertex i ∈ (T (sideIndex i)).carrier := by
  have := h.anchored (sideIndex i); rwa [anchor_sideIndex] at this
theorem MinAt.corner_mem (h : MinAt T r s 0 right) (j : Fin 3) :
    corner j ∈ (T (cornerIndex j)).carrier := by
  have := h.anchored (cornerIndex j); rwa [anchor_cornerIndex] at this
theorem MinAt.zero_mem (h : MinAt T r s 0 right) : (0 : Point) ∈ (T 0).carrier := by
  change (0, 0) ∈ (T 0).carrier
  simpa [anchor] using h.anchored 0
theorem MinAt.s_half (h : MinAt T r s 0 right) : s ≤ 1 / 2 := by
  linarith [h.s_lt]

/-! ### The adaptive core -/

theorem coreVertex_mem_hexagon {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) (j : Fin 6) :
    coreVertex u j ∈ hexagon := by
  have hg0 : 0 ≤ u * (1 - u) := mul_nonneg hu0 (by linarith)
  have hg1 : u * (1 - u) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (u - 1 / 2)]
  fin_cases j <;> simp only [hexagon, abs_le, coreVertex, coreDir, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero, Prod.smul_mk, smul_eq_mul, mul_one, Set.mem_ofPred_eq, and_self_left,
      Fin.mk_one, Matrix.cons_val_one, mul_neg, neg_le_neg_iff, le_neg_add_iff_add_le,
      add_neg_le_iff_le_add, neg_add_le_iff_le_add, Fin.reduceFinMk, Matrix.cons_val,
      le_add_neg_iff_add_le] <;>
    (repeat' constructor) <;> nlinarith

theorem sqDist_corner_coreVertex {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) (k : Fin 3) (j : Fin 6) :
    1 ≤ sqDist (corner k) (coreVertex u j) := by
  have hg0 : 0 ≤ u * (1 - u) := mul_nonneg hu0 (by linarith)
  have hg1 : u * (1 - u) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (u - 1 / 2)]
  fin_cases k <;> fin_cases j <;> simp [coreVertex, coreDir, corner, sqDist] <;> nlinarith

theorem MinAt.core_of_geometry (h : MinAt T r s 0 right) (hcore : CoreObstruction) (j : Fin 6) :
    coreVertex s j ∈ (T 0).carrier := by
  obtain ⟨k, hk⟩ := h.covers _ (hexagon_subset_target (coreVertex_mem_hexagon h.s_pos.le h.s_half
      j))
  rcases owner_cases k with rfl | ⟨i, rfl⟩ | ⟨m, rfl⟩
  · exact hk
  · exact (hcore h.s_pos h.s_half i j (h.side_pos' _) (h.side_lt' _) (h.vertex_mem i)
      (h.sidePt_mem i false h.s_pos.le le_rfl) (h.sidePt_mem i true h.s_pos.le le_rfl) hk).elim
  · exact ((T (cornerIndex m)).cannot_contain_unit_chord (h.side_lt' _)
      (sqDist_corner_coreVertex h.s_pos.le h.s_half m j) (h.corner_mem m) hk).elim

theorem coreVertex_half_mem {C : Set Point} (hC : Convex ℝ C) (h0 : (0 : Point) ∈ C)
    (hK : ∀ j, coreVertex s j ∈ C) (hs0 : 0 < s) (hs : s ≤ 1 / 2) (j : Fin 6) :
    coreVertex (s / 2) j ∈ C := by
  have hpos : 0 < s * (1 - s) := mul_pos hs0 (by linarith)
  have hlam : (s / 2 * (1 - s / 2)) / (s * (1 - s)) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (mul_nonneg (by linarith) (by linarith)) hpos.le
    · rw [div_le_one hpos]; nlinarith
  have := hC.smul_mem_of_zero_mem h0 (hK j) hlam
  convert this using 1
  rw [coreVertex, coreVertex, smul_smul]
  congr 1
  have h1 : (1 - s) ≠ 0 := by
    linarith
  field_simp

theorem MinAt.endpoint_not_centre_of_geometry (h : MinAt T r s 0 right) (hcore : CoreObstruction)
    (hbridge : BridgeObstruction) :
    linePoint (vertex 0) (sideDirection 0 right) s ∉ (T 0).carrier := by
  intro hp
  refine hbridge (u := s / 2) (by linarith [h.s_pos]) (by linarith [h.s_lt]) right
    (h.side_pos' 0) (h.side_lt' 0)
    (coreVertex_half_mem (T 0).convex_carrier h.zero_mem (h.core_of_geometry hcore) h.s_pos
        h.s_half) ?_
  rwa [show 2 * (s / 2) = s by ring]

/-! ### Transfer of the minimal endpoint -/

theorem MinAt.endpoint_owner (h : MinAt T r s 0 right) :
    ∃ k, k ≠ 1 ∧ linePoint (vertex 0) (sideDirection 0 right) s ∈ (T k).carrier := by
  have hlen : rayLen (T 1) (vertex 0) (sideDirection 0 right) < 1 := by
    have := h.attained
    rw [sideLenC] at this
    change rayLen (T 1) (vertex 0) (sideDirection 0 right) = s at this
    rw [this]; linarith [h.s_lt]
  have hs : linePoint (vertex 0) (sideDirection 0 right) s =
      linePoint (vertex 0) (sideDirection 0 right) (rayLen (T 1) (vertex 0) (sideDirection 0 right))
          := by
    have := h.attained
    rw [sideLenC] at this
    change rayLen (T 1) (vertex 0) (sideDirection 0 right) = s at this
    rw [this]
  rw [hs]
  exact rayLen_transfers T h.covers 1 (h.vertex_mem 0) (sideDirection_unit 0 right) hlen
    (fun t ht => sidePoint_mem_target 0 right ht)

theorem endpoint_ext_eq (s : ℝ) :
    linePoint (vertex 0) (sideDirection 0 false) s = linePoint (vertex 5) (sideDirection 5 true) (1
        - s) := by
  apply Prod.ext <;> simp [linePoint, sideDirection, neighbor, vertex]; ring

/-- External side: the endpoint belongs to `S₅`. -/
theorem MinAt.ext_contact_of_geometry (h : MinAt T r s 0 false) (hcore : CoreObstruction)
    (hbridge : BridgeObstruction) :
    linePoint (vertex 0) (sideDirection 0 false) s ∈ (T 6).carrier := by
  obtain ⟨k, hk1, hk⟩ := h.endpoint_owner
  have hnot0 := h.endpoint_not_centre_of_geometry hcore hbridge
  have hallow : sideAllowed 5 k = true := by
    rw [endpoint_ext_eq] at hk
    exact side_owner_allowed h.common h.r_lt h.anchored 5 (by linarith [h.s_lt]) (by linarith
        [h.s_pos]) hk
  fin_cases k <;> simp [sideAllowed, sideIndex] at hallow <;> first
    | exact hk
    | exact absurd hk hnot0
    | exact absurd rfl hk1

/-- Internal side: the endpoint belongs to `S₁` or to `A₀`. -/
theorem MinAt.int_contact_of_geometry (h : MinAt T r s 0 true) (hcore : CoreObstruction)
    (hbridge : BridgeObstruction) :
    linePoint (vertex 0) (sideDirection 0 true) s ∈ (T 2).carrier ∨
      linePoint (vertex 0) (sideDirection 0 true) s ∈ (T 7).carrier := by
  obtain ⟨k, hk1, hk⟩ := h.endpoint_owner
  have hnot0 := h.endpoint_not_centre_of_geometry hcore hbridge
  have hallow : sideAllowed 0 k = true :=
    side_owner_allowed h.common h.r_lt h.anchored 0 h.s_pos.le (by linarith [h.s_lt]) hk
  fin_cases k <;> simp [sideAllowed, sideIndex] at hallow <;> first
    | exact Or.inl hk
    | exact Or.inr hk
    | exact absurd hk hnot0
    | exact absurd rfl hk1

/-! ### Corner sections are at least `s` -/

/-- The continuation of the corner ray beyond `vertex (2j+m)` is a side point of `S_{2j+m}`. -/
theorem cornerCont_eq (j : Fin 3) (m : Fin 2) (t : ℝ) :
    linePoint (corner j) (cornerDirection j m) (1 + t) =
      linePoint (vertex ⟨2 * j.val + m.val, by omega⟩)
        (sideDirection ⟨2 * j.val + m.val, by omega⟩ (decide (m = 1))) t := by
  fin_cases j <;> fin_cases m <;> apply Prod.ext <;>
    simp [linePoint, cornerDirection, sideDirection, neighbor, corner, vertex] <;> ring

theorem sqDist_cornerRay_same (j : Fin 3) (m : Fin 2) (x t : ℝ) :
    sqDist (linePoint (corner j) (cornerDirection j m) x)
      (linePoint (corner j) (cornerDirection j m) t) = (x - t) ^ 2 := by
  fin_cases j <;> fin_cases m <;> simp [linePoint, cornerDirection, corner, vertex, sqDist] <;> ring

theorem sqDist_cornerRay_other (j : Fin 3) (m : Fin 2) (x t : ℝ) :
    sqDist (linePoint (corner j) (cornerDirection j m) x)
      (linePoint (corner j) (cornerDirection j (1 - m)) t) = x ^ 2 - x * t + t ^ 2 := by
  fin_cases j <;> fin_cases m <;> simp [linePoint, cornerDirection, corner, vertex, sqDist] <;> ring

theorem MinAt.contPt_mem (h : MinAt T r s 0 right) (j : Fin 3) (m : Fin 2) :
    linePoint (corner j) (cornerDirection j m) (1 + s) ∈
      (T (sideIndex ⟨2 * j.val + m.val, by omega⟩)).carrier := by
  rw [cornerCont_eq]
  exact h.sidePt_mem _ _ h.s_pos.le le_rfl

theorem cornerAllowed_cases (j : Fin 3) (k : Fin 10) (hk : cornerAllowed j k = true) :
    k = cornerIndex j ∨ k = sideIndex ⟨2 * j.val, by omega⟩ ∨ k = sideIndex ⟨2 * j.val + 1, by
        omega⟩ := by
  fin_cases j <;> fin_cases k <;> simp [cornerAllowed, cornerIndex, sideIndex] at hk ⊢

theorem MinAt.corner_min (h : MinAt T r s 0 right) (j : Fin 3) (m : Fin 2) :
    s ≤ rayLen (T (cornerIndex j)) (corner j) (cornerDirection j m) := by
  by_contra hlt
  push Not at hlt
  set x := rayLen (T (cornerIndex j)) (corner j) (cornerDirection j m) with hx
  have hx0 : 0 ≤ x := rayLen_nonneg _ (h.corner_mem j) (cornerDirection_unit j m)
  have hx1 : x < 1 := by
    linarith [h.s_lt]
  set S₀ := T (sideIndex ⟨2 * j.val, by omega⟩)
  set S₁ := T (sideIndex ⟨2 * j.val + 1, by omega⟩)
  -- immediately after the corner section, only the two side owners can cover the segment
  have hcov : ∀ t ∈ Set.Ioo x 1,
      linePoint (corner j) (cornerDirection j m) t ∈ S₀.carrier ∪ S₁.carrier := by
    intro t ht
    obtain ⟨k, hk⟩ := h.covers _ (cornerSeg_mem_target j m (by linarith [ht.1]) ht.2.le)
    have hallow := cornerSeg_owner_allowed h.common h.r_lt h.anchored j m (by linarith [ht.1])
      ht.2.le hk
    rcases cornerAllowed_cases j k hallow with rfl | rfl | rfl
    · exact absurd hk (not_mem_after_rayLen _ (h.corner_mem j) (cornerDirection_unit j m) ht.1)
    · exact Or.inl hk
    · exact Or.inr hk
  have hend := closed_cover_endpoint (S₀.isClosed_carrier.union S₁.isClosed_carrier)
    (continuous_linePoint _ _) hx1 hcov
  -- the two continuation points
  have hc0 := h.contPt_mem j 0
  have hc1 := h.contPt_mem j 1
  have hxs : x ≤ s := hlt.le
  rcases hend with hS | hS
  · -- in `S_{2j}`: compare with the continuation along `e_0`
    fin_cases m
    · simp only [Fin.zero_eta, Fin.isValue] at hS
      have hd := sqDist_cornerRay_same j 0 x (1 + s)
      exact S₀.cannot_contain_unit_chord (h.side_lt' _) (by rw [hd]; nlinarith) hS hc0
    · simp only [Fin.mk_one, Fin.isValue] at hS
      have hd := sqDist_cornerRay_other j 1 x (1 + s)
      have e : (1 : Fin 2) - 1 = 0 := rfl
      rw [e] at hd
      exact S₀.cannot_contain_unit_chord (h.side_lt' _) (by rw [hd]; nlinarith) hS hc0
  · fin_cases m
    · simp only [Fin.zero_eta, Fin.isValue] at hS
      have hd := sqDist_cornerRay_other j 0 x (1 + s)
      have e : (1 : Fin 2) - 0 = 1 := rfl
      rw [e] at hd
      exact S₁.cannot_contain_unit_chord (h.side_lt' _) (by rw [hd]; nlinarith) hS hc1
    · simp only [Fin.mk_one, Fin.isValue] at hS
      have hd := sqDist_cornerRay_same j 1 x (1 + s)
      exact S₁.cannot_contain_unit_chord (h.side_lt' _) (by rw [hd]; nlinarith) hS hc1

/-! ### The corner branch -/

theorem extMid0_eq_linePoint : extMid0 = linePoint (corner 0) (cornerDirection 0 0) (1 / 2) := by
  apply Prod.ext <;> simp [extMid0, linePoint, corner, cornerDirection, vertex]; norm_num

theorem MinAt.mid_owner (h : MinAt T r s 0 right) :
    extMid0 ∈ (T 7).carrier ∨ extMid0 ∈ (T 1).carrier ∨ extMid0 ∈ (T 2).carrier := by
  rw [extMid0_eq_linePoint]
  obtain ⟨k, hk⟩ := h.covers (linePoint (corner 0) (cornerDirection 0 0) (1 / 2))
    (cornerSeg_mem_target 0 0 (t := 1 / 2) (by norm_num) (by norm_num))
  have hallow := cornerSeg_owner_allowed h.common h.r_lt h.anchored 0 0 (t := 1 / 2) (by norm_num)
    (by norm_num) hk
  rcases cornerAllowed_cases 0 k hallow with rfl | rfl | rfl
  · exact Or.inl hk
  · exact Or.inr (Or.inl hk)
  · exact Or.inr (Or.inr hk)

theorem MinAt.mid_not_corner_of_geometry (h : MinAt T r s 0 true) (hmid : MidpointObstruction)
    (hp : linePoint (vertex 0) (sideDirection 0 true) s ∈ (T 7).carrier) :
    extMid0 ∉ (T 7).carrier := by
  intro hm
  refine hmid h.s_pos h.s_half (h.side_pos' 7) (h.side_lt' 7) (h.corner_mem 0) ?_ hp hm
  exact (linePoint_mem_iff_le_rayLen _ (h.corner_mem 0) (cornerDirection_unit 0 1) h.s_pos.le).mpr
    (h.corner_min 0 1)

/-! ### Assembly -/

theorem MinAt.endpoint_eq (h : MinAt T r s 0 right) :
    rayLen (T 1) (vertex 0) (sideDirection 0 right) = s := by
  have := h.attained; rw [sideLenC] at this; exact this

/-- The normalized cover in case `c` (with `c.right = right`). -/
theorem MinAt.canonical_of_geometry (h : MinAt T r s 0 right) (hcore : CoreObstruction)
    (c : ContactCase) (hc : c.right = right) (hcontact : BranchHolds c T s) :
    Canonical c T r s where
  common := h.common
  covers := h.covers
  r_pos := h.r_pos
  r_lt := h.r_lt
  anchored := h.anchored
  s_pos := h.s_pos
  s_lt := h.s_lt
  side_min := fun i right' => h.side_min i right'
  corner_min := h.corner_min
  core := h.core_of_geometry hcore
  endpoint := by
    rw [hc]; exact h.endpoint_eq
  contact := hcontact

/-- Every subunit full cover is a canonical contact case. -/
theorem exists_canonical_of_geometry (hcore : CoreObstruction) (hbridge : BridgeObstruction)
    (hmid : MidpointObstruction) (r : ℝ) (T : Configuration) (hside : CommonSide T r)
    (hcover : Covers T) (hr : r < 1) :
    ∃ (c : ContactCase) (U : Configuration) (s : ℝ), Canonical c U r s := by
  obtain ⟨U, s, right, h⟩ := exists_minAt_zero r T hside hcover hr
  cases right with
  | false =>
    exact ⟨.Sext, U, s, h.canonical_of_geometry hcore .Sext rfl (h.ext_contact_of_geometry hcore
        hbridge)⟩
  | true =>
    rcases h.int_contact_of_geometry hcore hbridge with hp2 | hp7
    · exact ⟨.Sint, U, s, h.canonical_of_geometry hcore .Sint rfl hp2⟩
    · by_cases hp2 : linePoint (vertex 0) (sideDirection 0 true) s ∈ (U 2).carrier
      · exact ⟨.Sint, U, s, h.canonical_of_geometry hcore .Sint rfl hp2⟩
      · rcases h.mid_owner with hm7 | hm1 | hm2
        · exact absurd hm7 (h.mid_not_corner_of_geometry hmid hp7)
        · exact ⟨.Aown, U, s, h.canonical_of_geometry hcore .Aown rfl ⟨hp7, hp2, hm1⟩⟩
        · exact ⟨.Across, U, s, h.canonical_of_geometry hcore .Across rfl ⟨hp7, hp2, hm2⟩⟩

end ConwaySoifer
