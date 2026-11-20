/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Oct9Data

/-! # Oct9 Quad -/

@[expose] public section

namespace RupertMinimality

/-!
# Lemma 9.3: good quad edges

For an edge `x → y` of an octahedron at which `x'` is hidden (the two face
inequalities saying that `x` lies strictly farther than `y` from the planes of
both faces at the antipodal edge `x' y'`), view along `u = y - x`.  The
shadow is the quadrilateral `q, P, Y', P'`; tilting gives the silhouettes `(y, p, y', p')`
(tilt `y' - x`) and `(x, p, y', p')` (tilt `x - y'`), Lemma 8.0.  Unless the
edge is *bad* or *touching*, one of them is robustly unimodal (Cor. 8.0′).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

theorem det3_shift_xy (p w x y : ℝ³) :
    det3 (p - x) (w - x) (y - x) = det3 (p - y) (w - y) (y - x) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem det3_tilt_y (p x y y' : ℝ³) :
    det3 (p - y) (x - y) (y' - x) = det3 (p - y) (y' - y) (y - x) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem det3_tilt_p' (p' x y y' : ℝ³) :
    det3 (y - p') (x - p') (y' - x) = det3 (y - p') (y' - p') (y - x) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem det3_tilt_x (p x y y' : ℝ³) :
    det3 (p - x) (y - x) (x - y') = det3 (p - y) (y' - y) (y - x) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem det3_tilt_x' (p' x y y' : ℝ³) :
    det3 (x - p') (y - p') (x - y') = det3 (y - p') (y' - p') (y - x) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem det3_shift_p' (p' w x y : ℝ³) :
    det3 (x - p') (w - p') (y - x) = det3 (y - p') (w - p') (y - x) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem det3_self_u (a x y : ℝ³) : det3 a (y - x) (y - x) = 0 := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem det3_xy_zero (p x y : ℝ³) : det3 (p - y) (x - y) (y - x) = 0 := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem det3_xy_zero' (p' x y : ℝ³) : det3 (y - p') (x - p') (y - x) = 0 := by
  simp only [det3_expand, PiLp.sub_apply]; ring

/-- A far edge `PQ` of the edge view along `y - x`, between a lower facet
`x Q P` and an upper facet `x' Q P`. -/
theorem far_edge_pos {V : Finset ℝ³} {x x' y P Q : ℝ³} (G : FacetFn V x Q P)
    (H : FacetFn V x' Q P) (hx : x ∈ V) (hx' : x' ∈ V) (hxx' : x ≠ x') (hxP : x ≠ P)
    (hxQ : x ≠ Q) (hx'P : x' ≠ P) (hx'Q : x' ≠ Q) (hGy : G.f y < 0) (hq : H.f x < H.f y)
    {r w : ℝ³} (hr : r ∈ V) (hrP : r ≠ P) (hrQ : r ≠ Q) (hw : w ∈ V) (hwP : w ≠ P)
    (hwQ : w ≠ Q) (href : 0 < det3 (Q - P) (r - P) (y - x)) :
    0 < det3 (Q - P) (w - P) (y - x) := by
  have key : ∀ z ∈ V, z ≠ P → z ≠ Q →
      (H.f y - H.f x) * G.f z + (-(G.f y - G.f x)) * H.f z < 0 := by
    intro z hz hzP hzQ
    have hα : 0 < H.f y - H.f x := by linarith
    have hβ : 0 < -(G.f y - G.f x) := by rw [G.hP]; linarith
    by_cases hzx : z = x
    · subst hzx; rw [G.hP]; nlinarith [H.neg z hz hxx' hzQ hzP]
    by_cases hzx' : z = x'
    · subst hzx'; rw [H.hP]; nlinarith [G.neg z hz (Ne.symm hxx') hzQ hzP]
    nlinarith [G.neg z hz hzx hzQ hzP, H.neg z hz hzx' hzQ hzP]
  refine det3_pos_of_combo G.hN H.hN G.hR G.hQ H.hR H.hQ ?_ href (key r hr hrP hrQ)
    (key w hw hwP hwQ)
  rw [← G.hN, ← H.hN]; ring

/-- A vertical facet `x y P` (containing the view `y - x`) gives an edge `y → P`
of the shadow. -/
theorem vert_edge_pos {V : Finset ℝ³} {x y P : ℝ³} (G : FacetFn V x y P) {r w : ℝ³}
    (hr : r ∈ V) (hrx : r ≠ x) (hry : r ≠ y) (hrP : r ≠ P) (hw : w ∈ V) (hwx : w ≠ x)
    (hwy : w ≠ y) (hwP : w ≠ P) (href : 0 < det3 (P - y) (r - y) (y - x)) :
    0 < det3 (P - y) (w - y) (y - x) := by
  refine det3_pos_of_combo G.hN G.hN G.hQ G.hR G.hQ G.hR (α := 1) (β := 0) ?_ href
    (by have := G.neg r hr hrx hry hrP; linarith) (by have := G.neg w hw hwx hwy hwP; linarith)
  rw [← G.hN, G.hQ, G.hP]; ring

theorem vert_edge_pos' {V : Finset ℝ³} {x y P : ℝ³} (G : FacetFn V x y P) {r w : ℝ³}
    (hr : r ∈ V) (hrx : r ≠ x) (hry : r ≠ y) (hrP : r ≠ P) (hw : w ∈ V) (hwx : w ≠ x)
    (hwy : w ≠ y) (hwP : w ≠ P) (href : 0 < det3 (y - P) (r - P) (y - x)) :
    0 < det3 (y - P) (w - P) (y - x) := by
  refine det3_pos_of_combo G.hN G.hN G.hR G.hQ G.hR G.hQ (α := 1) (β := 0) ?_ href
    (by have := G.neg r hr hrx hry hrP; linarith) (by have := G.neg w hw hwx hwy hwP; linarith)
  rw [← G.hN, G.hQ, G.hP]; ring

/-- The determinant tests at the edge view of a quad edge `x → y`, with the
orientation `det3 (p - y) (p' - y) (y - x) > 0`. -/
theorem quad_edge_tests {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hor : 0 < det3 (p - y) (p' - y) (y - x)) :
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ y → w ≠ p → w ≠ x →
      0 < det3 (p - y) (w - y) (y - x)) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ p → w ≠ y' →
      0 < det3 (y' - p) (w - p) (y - x)) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ y' → w ≠ p' →
      0 < det3 (p' - y') (w - y') (y - x)) ∧
    (∀ w ∈ ({x, x', y, y', p, p'} : Finset ℝ³), w ≠ p' → w ≠ y → w ≠ x →
      0 < det3 (y - p') (w - p') (y - x)) := by
  set V : Finset ℝ³ := {x, x', y, y', p, p'}
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  have mx : x ∈ V := by simp [V]
  have mx' : x' ∈ V := by simp [V]
  have my : y ∈ V := by simp [V]
  have my' : y' ∈ V := by simp [V]
  have mp : p ∈ V := by simp [V]
  have mp' : p' ∈ V := by simp [V]
  have E1 : ∀ w ∈ V, w ≠ y → w ≠ p → w ≠ x → 0 < det3 (p - y) (w - y) (y - x) :=
    fun w hw hwy hwp hwx => vert_edge_pos F.abc mp' (Ne.symm hxp') (Ne.symm hyp')
      (Ne.symm hpp') hw hwx hwy hwp hor
  have E2 : ∀ w ∈ V, w ≠ p → w ≠ y' → 0 < det3 (y' - p) (w - p) (y - x) :=
    fun w hw hwp hwy' => far_edge_pos F.ab'c F.a'b'c mx mx' hxx' hxp hxy' hx'p hx'y'
      (F.ab'c.neg y my (Ne.symm hxy) hyy' hyp) hq₁ my hyp hyy' hw hwp hwy'
      (by rw [det3_cyc y p y']; exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy'))
  have E3 : ∀ w ∈ V, w ≠ y' → w ≠ p' → 0 < det3 (p' - y') (w - y') (y - x) :=
    fun w hw hwy' hwp' => far_edge_pos F.ab'c'.p23 F.a'b'c'.p23 mx mx' hxx' hxy' hxp'
      hx'y' hx'p' (F.ab'c'.neg y my (Ne.symm hxy) hyy' hyp') hq₂ mp (Ne.symm hy'p) hpp' hw
      hwy' hwp' (by rw [det3_cyc p y' p']; exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p'))
  have E4 : ∀ w ∈ V, w ≠ p' → w ≠ y → w ≠ x → 0 < det3 (y - p') (w - p') (y - x) := by
    intro w hw hwp' hwy hwx
    exact vert_edge_pos' F.abc' mp (Ne.symm hxp) (Ne.symm hyp) hpp' hw hwx hwy hwp'
      (by rw [← det3_cyc p' y p]; exact hor)
  exact ⟨E1, E2, E3, E4⟩

theorem det3_self_left (a b : ℝ³) : det3 a a b = 0 := by
  simp only [det3_expand]; ring

/-- The convexity of the lower boundary over the edge view (the claim in
Lemma 9.3): a point of the edge `x y'` lies strictly below the point of the
segment `p p'` over the crossing of the diagonals of the shadow. -/
theorem quad_edge_lower {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (_ : 0 < det3 (y' - p) (p' - p) (y - x)) (_ : 0 < det3 (y' - x) (p' - x) (y - x))
    (_ : 0 < det3 (p - x) (p' - x) (y - x)) (hS₄ : 0 < det3 (p - x) (y' - x) (y - x)) :
    det3 (y' - p) (p' - p) (y - x) * ⟪x, y - x⟫ + det3 (p - x) (p' - x) (y - x) * ⟪y', y - x⟫ <
      det3 (y' - x) (p' - x) (y - x) * ⟪p, y - x⟫ + det3 (p - x) (y' - x) (y - x) * ⟪p', y - x⟫ :=
        by
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  set u := y - x
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  set S₁ := det3 (y' - p) (p' - p) u
  set S₂ := det3 (y' - x) (p' - x) u
  set S₃ := det3 (p - x) (p' - x) u
  set S₄ := det3 (p - x) (y' - x) u
  have hpar := four_point_parallel x p y' p' u hu
  have hsum := four_point_sum x p y' p' u
  set L := S₁ • x - S₂ • p + S₃ • y' - S₄ • p'
  set lam := ⟪L, u⟫ / ⟪u, u⟫
  have hL : L = -S₂ • (p - x) + S₃ • (y' - x) - S₄ • (p' - x) := by
    have : S₁ = S₂ - S₃ + S₄ := by linarith
    simp only [L, this]; module
  have hGL : ⟪F.ab'c.N, L⟫ = -S₄ * F.ab'c.f p' := by
    rw [hL, inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, ← F.ab'c.hN, ← F.ab'c.hN, ← F.ab'c.hN, F.ab'c.hP, F.ab'c.hQ,
      F.ab'c.hR]
    ring
  have hGp' := F.ab'c.neg p' (by simp) (Ne.symm hxp') (Ne.symm hy'p') (Ne.symm hpp')
  have hGy := F.ab'c.neg y (by simp) (Ne.symm hxy) hyy' hyp
  have hGu : ⟪F.ab'c.N, u⟫ = F.ab'c.f y := by rw [← F.ab'c.hN, F.ab'c.hP, sub_zero]
  have hlam : lam < 0 := by
    have e : ⟪F.ab'c.N, L⟫ = lam * F.ab'c.f y := by
      rw [← hGu, ← real_inner_smul_right, ← hpar]
    rw [hGL] at e
    nlinarith
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  have hLu : ⟪L, u⟫ < 0 := by
    have : ⟪L, u⟫ = lam * ⟪u, u⟫ := by
      conv_lhs => rw [hpar]
      rw [real_inner_smul_left]
    rw [this]; nlinarith
  simp only [L, inner_sub_left, inner_add_left, real_inner_smul_left] at hLu
  linarith

/-- **Lemma 9.3, oriented.** -/
theorem isRupert_quad_edge_core {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hor : 0 < det3 (p - y) (p' - y) (y - x))
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (htouch : ¬ (⟪p, y - x⟫ = ⟪p', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫ ∧
      ⟪y', y - x⟫ < ⟪y, y - x⟫)) :
    IsRupert {x, x', y, y', p, p'} := by
  classical
  obtain ⟨E1, E2, E3, E4⟩ := quad_edge_tests F hq₁ hq₂ hor
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  set V : Finset ℝ³ := {x, x', y, y', p, p'} with hV
  have mx : x ∈ V := by simp [V]
  have mx' : x' ∈ V := by simp [V]
  have my : y ∈ V := by simp [V]
  have my' : y' ∈ V := by simp [V]
  have mp : p ∈ V := by simp [V]
  have mp' : p' ∈ V := by simp [V]
  have hmemV : ∀ z ∈ V, z = x ∨ z = x' ∨ z = y ∨ z = y' ∨ z = p ∨ z = p' := by
    intro z hz; simpa [V] using hz
  set u := y - x with hu_def
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  by_cases hN : NWS4 (quad ⟪y, u⟫ ⟪p, u⟫ ⟪y', u⟫ ⟪p', u⟫)
  · -- closing by `y` (tilt `y' - x`)
    refine isRupert_of_tilted_unimodal V u (y' - x) hu (by norm_num) (quad y p y' p') ?_ ?_ ?_
      NWS4 isOpen_NWS4 (fun z c hc hz => hz.mul hc.ne') ?_
      (fun z hz hQ => isCyclicUnimodal_of_NWS4 hz hQ)
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] <;> refine Or.inl ?_
      · exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
      · exact E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
      · exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
      · exact E2 y my hyp hyy'
      · exact E3 y my hyy' hyp'
      · exact E3 p mp (Ne.symm hy'p) hpp'
      · exact E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
      · exact E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
    · intro z hz hzx i
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      have t1 : 0 < det3 (p - y) (y' - y) u := E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
      have t4 : 0 < det3 (y - p') (y' - p') u := E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
      rcases hmemV z hz with h | h | h | h | h | h
      · rw [h]
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · exact Or.inr ⟨det3_xy_zero p x y, by rw [det3_tilt_y]; exact t1⟩
        · exact Or.inl (E2 x mx hxp hxy')
        · exact Or.inl (E3 x mx hxy' hxp')
        · exact Or.inr ⟨det3_xy_zero' p' x y, by rw [det3_tilt_p']; exact t4⟩
      · rw [h]
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] <;> refine Or.inl ?_
        · exact E1 x' mx' hx'y hx'p (Ne.symm hxx')
        · exact E2 x' mx' hx'p hx'y'
        · exact E3 x' mx' hx'y' hx'p'
        · exact E4 x' mx' hx'p' hx'y (Ne.symm hxx')
      · exact absurd h h0
      · exact absurd h h2
      · exact absurd h h1
      · exact absurd h h3
    · convert hN using 1; funext i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  · -- closing by `x` (tilt `x - y'`)
    have hS₁ := E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
    have hS₂ : 0 < det3 (y' - x) (p' - x) u := by
      rw [← det3_cyc x y' p']; exact E3 x mx hxy' hxp'
    have hS₃ : 0 < det3 (p - x) (p' - x) u := by rw [det3_shift_xy]; exact hor
    have hS₄ : 0 < det3 (p - x) (y' - x) u := by
      rw [det3_shift_xy]; exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
    have hlow := quad_edge_lower F hS₁ hS₂ hS₃ hS₄
    have hsum := four_point_sum x p y' p' u
    have hN' : NWS4 (quad ⟪x, u⟫ ⟪p, u⟫ ⟪y', u⟫ ⟪p', u⟫) := by
      simp only [NWS4, quad_0, quad_1, quad_2, quad_3] at hN ⊢
      simp only [max_le_iff, le_min_iff, not_and_or, not_le] at hgood
      have hY : ⟪p, u⟫ ≤ ⟪y, u⟫ ∧ ⟪p', u⟫ ≤ ⟪y, u⟫ ∧ ⟪p, u⟫ ≤ ⟪y', u⟫ ∧ ⟪p', u⟫ ≤ ⟪y', u⟫ := by
        by_contra hc
        apply hN
        constructor
        · simp only [not_and_or, not_le] at hc; exact hc
        · rcases hgood with (h | h) | (h | h) <;> simp only [h, true_or, or_true]
      obtain ⟨hY1, hY2, hY3, hY4⟩ := hY
      have hx_lt : ⟪x, u⟫ < ⟪p, u⟫ ∨ ⟪x, u⟫ < ⟪p', u⟫ := by
        by_contra hc; push Not at hc
        obtain ⟨c1, c2⟩ := hc
        rcases le_total ⟪p, u⟫ ⟪p', u⟫ with hpp | hpp
        · nlinarith [mul_le_mul_of_nonneg_left c2 hS₁.le, mul_le_mul_of_nonneg_left hY4 hS₃.le,
            mul_le_mul_of_nonneg_left hpp hS₂.le, mul_eq_zero_of_left hsum ⟪p', u⟫]
        · nlinarith [mul_le_mul_of_nonneg_left c1 hS₁.le, mul_le_mul_of_nonneg_left hY3 hS₃.le,
            mul_le_mul_of_nonneg_left hpp hS₄.le, mul_eq_zero_of_left hsum ⟪p, u⟫]
      refine ⟨by rcases hx_lt with h | h; exacts [Or.inl h, Or.inr (Or.inl h)], ?_⟩
      by_contra hc
      simp only [not_or, not_lt] at hc
      obtain ⟨-, -, c3, c4⟩ := hc
      apply htouch
      refine ⟨by linarith, by linarith, ?_⟩
      rcases hgood with (h | h) | (h | h) <;> linarith
    refine isRupert_of_tilted_unimodal V u (x - y') hu (by norm_num) (quad x p y' p') ?_ ?_ ?_
      NWS4 isOpen_NWS4 (fun z c hc hz => hz.mul hc.ne') ?_
      (fun z hz hQ => isCyclicUnimodal_of_NWS4 hz hQ)
    · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [V, quad_0, quad_1, quad_2, quad_3]
    · intro i j hi hj
      rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] <;> refine Or.inl ?_
      · rw [det3_shift_xy]; exact E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
      · rw [det3_shift_xy]; exact E1 p' mp' (Ne.symm hyp') (Ne.symm hpp') (Ne.symm hxp')
      · exact E2 p' mp' (Ne.symm hpp') (Ne.symm hy'p')
      · exact E2 x mx hxp hxy'
      · exact E3 x mx hxy' hxp'
      · exact E3 p mp (Ne.symm hy'p) hpp'
      · rw [det3_shift_p']; exact E4 p mp hpp' (Ne.symm hyp) (Ne.symm hxp)
      · rw [det3_shift_p']; exact E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
    · intro z hz hzx i
      have h0 := hzx 0; have h1 := hzx 1; have h2 := hzx 2; have h3 := hzx 3
      simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
      have t1 : 0 < det3 (p - y) (y' - y) u := E1 y' my' (Ne.symm hyy') hy'p (Ne.symm hxy')
      have t4 : 0 < det3 (y - p') (y' - p') u := E4 y' my' hy'p' (Ne.symm hyy') (Ne.symm hxy')
      rcases hmemV z hz with h | h | h | h | h | h
      · exact absurd h h0
      · rw [h]
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> refine Or.inl ?_ <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · rw [det3_shift_xy]; exact E1 x' mx' hx'y hx'p (Ne.symm hxx')
        · exact E2 x' mx' hx'p hx'y'
        · exact E3 x' mx' hx'y' hx'p'
        · rw [det3_shift_p']; exact E4 x' mx' hx'p' hx'y (Ne.symm hxx')
      · rw [h]
        rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
          simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
        · exact Or.inr ⟨det3_self_u _ x y, by rw [det3_tilt_x]; exact t1⟩
        · exact Or.inl (E2 y my hyp hyy')
        · exact Or.inl (E3 y my hyy' hyp')
        · exact Or.inr ⟨by rw [det3_shift_p', det3_self_left], by rw [det3_tilt_x']; exact t4⟩
      · exact absurd h h2
      · exact absurd h h1
      · exact absurd h h3
    · convert hN' using 1; funext i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl

theorem det3_plane_xy (p x x' y : ℝ³) :
    det3 (p - y) (x' - y) (y - x) = det3 (y - x) (p - x) (x' - x) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

/-- The edge view of an edge `x y` is not degenerate. -/
theorem quad_orient_ne {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p') :
    det3 (p - y) (p' - y) (y - x) ≠ 0 := by
  intro h0
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hxx', hxy, hxy', hxp, hxp'⟩, ⟨hx'y, hx'y', hx'p, hx'p'⟩, ⟨hyy', hyp, hyp'⟩,
    ⟨hy'p, hy'p'⟩, hpp', -⟩ := hnd
  have G := F.abc
  have hGp' := F.abc.neg p' (by simp) (Ne.symm hxp') (Ne.symm hyp') (Ne.symm hpp')
  have hD := det3_zero_of_combo_ref F.abc.hN F.abc.hN F.abc.hQ F.abc.hR F.abc.hQ F.abc.hR
    (α := 1) (β := 0) (by rw [← F.abc.hN, F.abc.hQ, F.abc.hP]; ring) (r := p') (w := x') h0
    (by linarith)
  rw [det3_plane_xy] at hD
  have hc := cross_ne_zero_of_affine F.abc'.hN hxy F.abc'.hP F.abc'.hQ
    (F.abc'.neg p (by simp) (Ne.symm hxp) (Ne.symm hyp) hpp')
  have := affine_zero_of_coplanar F.abc.hN F.abc.hP F.abc.hQ F.abc.hR hc hD
  have := F.abc.neg x' (by simp) (Ne.symm hxx') hx'y hx'p
  linarith

/-- **Lemma 9.3 (good quad edges).**  A quad edge `x → y` (`x'` hidden along
`y - x`) that is neither bad nor touching gives a passage. -/
theorem isRupert_quad_edge {x x' y y' p p' : ℝ³} (F : OctFacets x x' y y' p p')
    (hq₁ : F.a'b'c.f x < F.a'b'c.f y) (hq₂ : F.a'b'c'.f x < F.a'b'c'.f y)
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (htouch : ¬ (⟪p, y - x⟫ = ⟪p', y - x⟫ ∧ ⟪p', y - x⟫ = ⟪y', y - x⟫ ∧
      ⟪y', y - x⟫ < ⟪y, y - x⟫)) :
    IsRupert {x, x', y, y', p, p'} := by
  rcases lt_or_gt_of_ne (quad_orient_ne F) with hneg | hpos
  · have := isRupert_quad_edge_core F.swap₃ hq₂ hq₁
      (by rw [det3_swap12]; linarith) (by rwa [min_comm]) (by
        rintro ⟨h1, h2, h3⟩; exact htouch ⟨h1.symm, by linarith, h3⟩)
    convert this using 1
    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · exact isRupert_quad_edge_core F hq₁ hq₂ hpos hgood htouch

end Minimality

end RupertMinimality
