/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.OctaTools

/-! # Oct9 Axis -/

@[expose] public section

namespace RupertMinimality

/-!
# Axis views of an octahedron (L9: planar equators, Lemma 9.4)

At the view along an axis `t' - t`, the equator `x y x' y'` is the silhouette
and the poles are hidden (strict determinant tests).  So any depth condition
that eventually holds at tilted views gives a passage
(`isRupert_axis_tilted`).  Consequences:
* `isRupert_axis_NWS`: the diagonals' depth intervals along the axis are not
  weakly separated (Corollary 7.8, proved again with the tilt tests);
* `isRupert_planar_equator`: a planar equator (Corollary 5.4 in L9);
* `isRupert_of_touching_pair` (Lemma 9.4): two touching quad edges.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- All determinant tests of the axis view are strictly positive (the equator
is a strictly convex counterclockwise silhouette, the poles inside). -/
theorem axis_tests {t t' x x' y y' : ℝ³} (h : IsOctahedron t t' x x' y y')
    (hor : 0 < det3 (y - x) (x' - x) (t' - t)) :
    (∀ w ∈ ({t, t', x, x', y, y'} : Finset ℝ³), w ≠ x → w ≠ y → 0 < det3 (y - x) (w - x) (t' - t)) ∧
    (∀ w ∈ ({t, t', x, x', y, y'} : Finset ℝ³), w ≠ y → w ≠ x' →
      0 < det3 (x' - y) (w - y) (t' - t)) ∧
    (∀ w ∈ ({t, t', x, x', y, y'} : Finset ℝ³), w ≠ x' → w ≠ y' →
      0 < det3 (y' - x') (w - x') (t' - t)) ∧
    (∀ w ∈ ({t, t', x, x', y, y'} : Finset ℝ³), w ≠ y' → w ≠ x →
      0 < det3 (x - y') (w - y') (t' - t)) := by
  have hnd := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨htt, htx, htx', hty, hty'⟩, ⟨ht'x, ht'x', ht'y, ht'y'⟩, ⟨hxx', hxy, hxy'⟩,
    ⟨hx'y, hx'y'⟩, hyy', -⟩ := hnd
  have mt : t ∈ ({t, t', x, x', y, y'} : Finset ℝ³) := by simp
  have mt' : t' ∈ ({t, t', x, x', y, y'} : Finset ℝ³) := by simp
  have mx : x ∈ ({t, t', x, x', y, y'} : Finset ℝ³) := by simp
  have mx' : x' ∈ ({t, t', x, x', y, y'} : Finset ℝ³) := by simp
  have my : y ∈ ({t, t', x, x', y, y'} : Finset ℝ³) := by simp
  have my' : y' ∈ ({t, t', x, x', y, y'} : Finset ℝ³) := by simp
  have E1 : ∀ w ∈ ({t, t', x, x', y, y'} : Finset ℝ³), w ≠ x → w ≠ y →
    0 < det3 (y - x) (w - x) (t' - t) :=
    fun w hw hwx hwy => axis_edge_pos h.facet_abc h.facet_a'bc mt mt' htt htx hty ht'x
    ht'y mx' (Ne.symm hxx') hx'y hw hwx hwy hor
  have r2 : 0 < det3 (x' - y) (x - y) (t' - t) := by rw [det3_cyc]; exact hor
  have E2 : ∀ w ∈ ({t, t', x, x', y, y'} : Finset ℝ³), w ≠ y → w ≠ x' →
    0 < det3 (x' - y) (w - y) (t' - t) :=
    fun w hw hwy hwx' => axis_edge_pos h.facet_ab'c.perm₂₃ h.facet_a'b'c.perm₂₃ mt mt'
    htt hty htx' ht'y ht'x' mx hxy hxx' hw hwy hwx' r2
  have r3 : 0 < det3 (y' - x') (y - x') (t' - t) := by
    rw [det3_cyc]; exact E2 y' my' (Ne.symm hyy') (Ne.symm hx'y')
  have E3 : ∀ w ∈ ({t, t', x, x', y, y'} : Finset ℝ³), w ≠ x' → w ≠ y' →
    0 < det3 (y' - x') (w - x') (t' - t) :=
    fun w hw hwx' hwy' => axis_edge_pos h.facet_ab'c' h.facet_a'b'c' mt mt' htt htx'
    hty' ht'x' ht'y' my (Ne.symm hx'y) hyy' hw hwx' hwy' r3
  have r4 : 0 < det3 (x - y') (x' - y') (t' - t) := by
    rw [det3_cyc]; exact E3 x mx hxx' hxy'
  have E4 : ∀ w ∈ ({t, t', x, x', y, y'} : Finset ℝ³), w ≠ y' → w ≠ x →
    0 < det3 (x - y') (w - y') (t' - t) :=
    fun w hw hwy' hwx => axis_edge_pos h.facet_abc'.perm₂₃ h.facet_a'bc'.perm₂₃ mt mt'
    htt hty' htx ht'y' ht'x mx' hx'y' (Ne.symm hxx') hw hwy' hwx r4
  exact ⟨E1, E2, E3, E4⟩

/-- **Axis views with a tilt.**  If the depth condition `NWS4` on the equator
holds at all small tilts `t' - t + εv`, the octahedron is Rupert. -/
theorem isRupert_axis_tilted {t t' x x' y y' : ℝ³} (h : IsOctahedron t t' x x' y y') (v : ℝ³)
    (hor : 0 < det3 (y - x) (x' - x) (t' - t))
    (hQ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), NWS4 fun i => ⟪quad x y x' y' i, (t' - t) + ε • v⟫) :
    IsRupert {t, t', x, x', y, y'} := by
  classical
  obtain ⟨E1, E2, E3, E4⟩ := axis_tests h hor
  have hnd := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨htt, htx, htx', hty, hty'⟩, ⟨ht'x, ht'x', ht'y, ht'y'⟩, ⟨hxx', hxy, hxy'⟩,
    ⟨hx'y, hx'y'⟩, hyy', -⟩ := hnd
  have hu : t' - t ≠ 0 := sub_ne_zero.mpr (Ne.symm htt)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine isRupert_of_tilted_unimodal' _ (t' - t) v hu (by norm_num) (quad x y x' y') ?_ ?_ ?_
    NWS4 isOpen_NWS4 (fun z c hc hz => hz.mul hc.ne') hQ
    (fun z hz hQ => isCyclicUnimodal_of_NWS4 hz hQ)
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp [quad_0, quad_1, quad_2, quad_3]
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] <;> refine Or.inl ?_
    · exact E1 x' (by simp) (Ne.symm hxx') hx'y
    · exact E1 y' (by simp) (Ne.symm hxy') (Ne.symm hyy')
    · exact E2 y' (by simp) (Ne.symm hyy') (Ne.symm hx'y')
    · exact E2 x (by simp) hxy hxx'
    · exact E3 x (by simp) hxx' hxy'
    · exact E3 y (by simp) (Ne.symm hx'y) hyy'
    · exact E4 y (by simp) hyy' (Ne.symm hxy)
    · exact E4 x' (by simp) hx'y' (Ne.symm hxx')
  · intro w hw hwx i
    have h0 := hwx 0; have h1 := hwx 1; have h2 := hwx 2; have h3 := hwx 3
    simp only [quad_0, quad_1, quad_2, quad_3] at h0 h1 h2 h3
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] <;> refine Or.inl ?_
    · exact E1 w hw h0 h1
    · exact E2 w hw h1 h2
    · exact E3 w hw h2 h3
    · exact E4 w hw h3 h0

theorem det3_neg_right (a b c : ℝ³) : det3 a b (-c) = -det3 a b c := by
  simp only [det3_expand, PiLp.neg_apply]; ring

theorem det3_swap12 (a b c : ℝ³) : det3 b a c = -det3 a b c := by
  simp only [det3_expand]; ring

theorem NWS4_quad_swap {z₀ z₁ z₂ z₃ : ℝ} (h : NWS4 (quad z₀ z₁ z₂ z₃)) :
    NWS4 (quad z₀ z₃ z₂ z₁) := by
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3] at h ⊢
  obtain ⟨h1, h2⟩ := h
  exact ⟨by tauto, by tauto⟩

/-- The axis view is not degenerate: the projected triangle `x y x'` has
nonzero area. -/
theorem axis_orient_ne {t t' x x' y y' : ℝ³} (h : IsOctahedron t t' x x' y y') :
    det3 (y - x) (x' - x) (t' - t) ≠ 0 := by
  intro h0
  have hnd := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨htt, htx, htx', hty, hty'⟩, ⟨ht'x, ht'x', ht'y, ht'y'⟩, ⟨hxx', hxy, hxy'⟩,
    ⟨hx'y, hx'y'⟩, hyy', -⟩ := hnd
  obtain ⟨f₁, f₁t, f₁x, f₁y, hf₁⟩ := h.facet_abc
  obtain ⟨f₂, f₂t', f₂x, f₂y, hf₂⟩ := h.facet_a'bc
  obtain ⟨N₁, hN₁⟩ := exists_normal_of_affine f₁
  obtain ⟨N₂, hN₂⟩ := exists_normal_of_affine f₂
  have f₁t' := hf₁ t' (by simp) (Ne.symm htt) ht'x ht'y
  have f₂t := hf₂ t (by simp) htt htx hty
  have f₁x' := hf₁ x' (by simp) (Ne.symm htx') (Ne.symm hxx') hx'y
  have f₂x' := hf₂ x' (by simp) (Ne.symm ht'x') (Ne.symm hxx') hx'y
  have hDt := det3_zero_of_combo_ref (fun y z => hN₁ y z) (fun y z => hN₂ y z) f₁x f₁y f₂x f₂y
    (α := -f₂ t) (β := -f₁ t') (by rw [← hN₁, ← hN₂, f₁t, f₂t']; ring) (r := x') (w := t) h0
    (by nlinarith)
  rw [det3_sub_left_eq] at hDt
  have hc := cross_ne_zero_of_affine (fun y z => hN₂ y z) hxy f₂x f₂y f₂t
  have := affine_zero_of_coplanar (fun y z => hN₁ y z) f₁x f₁y f₁t hc hDt
  linarith

/-- **Axis views with a tilt, either orientation.** -/
theorem isRupert_axis {t t' x x' y y' : ℝ³} (h : IsOctahedron t t' x x' y y') (v : ℝ³)
    (hQ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), NWS4 fun i => ⟪quad x y x' y' i, (t' - t) + ε • v⟫) :
    IsRupert {t, t', x, x', y, y'} := by
  rcases lt_or_gt_of_ne (axis_orient_ne h) with hneg | hpos
  · have hor' : 0 < det3 (y' - x) (x' - x) (t' - t) := by
      have h2 := (axis_tests h.swap₁ (by rw [← neg_sub t' t, det3_neg_right]; linarith)).2.2.2
      have hnd := h.nodup
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        not_or, List.nodup_nil, and_true] at hnd
      obtain ⟨-, -, ⟨hxx', -, -⟩, ⟨-, hx'y'⟩, -, -⟩ := hnd
      have := h2 x' (by simp) hx'y' (Ne.symm hxx')
      rw [← neg_sub t' t, det3_neg_right] at this
      rw [← det3_cyc x y' x', det3_swap12]; linarith
    have hQ' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), NWS4 fun i => ⟪quad x y' x' y i, (t' - t) + ε • v⟫ := by
      filter_upwards [hQ] with ε hε
      have := NWS4_quad_swap (z₀ := ⟪x, (t' - t) + ε • v⟫) (z₁ := ⟪y, (t' - t) + ε • v⟫)
        (z₂ := ⟪x', (t' - t) + ε • v⟫) (z₃ := ⟪y', (t' - t) + ε • v⟫) (by
          convert hε using 1; funext i
          rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl)
      convert this using 1; funext i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
    have := isRupert_axis_tilted h.swap₃ v hor' hQ'
    convert this using 1
    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · exact isRupert_axis_tilted h v hpos hQ

/-- **Corollary 7.8, via the axis view.**  If the depth intervals of
the equator's diagonals along the axis are not weakly separated, the
octahedron is Rupert. -/
theorem isRupert_axis_NWS {t t' x x' y y' : ℝ³} (h : IsOctahedron t t' x x' y y')
    (hN : NWS4 (quad ⟪x, t' - t⟫ ⟪y, t' - t⟫ ⟪x', t' - t⟫ ⟪y', t' - t⟫)) :
    IsRupert {t, t', x, x', y, y'} := by
  refine isRupert_axis h 0 ?_
  filter_upwards with ε
  simp only [smul_zero, add_zero]
  convert hN using 1; funext i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl

/-- Two diagonals crossing at a common point give non-separated intervals. -/
theorem NWS4_of_crossing {z₀ z₁ z₂ z₃ a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hab : a + b = c + d) (hz : a * z₀ + b * z₂ = c * z₁ + d * z₃)
    (hne : z₀ ≠ z₂) : NWS4 (quad z₀ z₁ z₂ z₃) := by
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3]
  rcases lt_or_gt_of_ne hne with h | h
  · constructor
    · by_contra hcon; push Not at hcon
      obtain ⟨h1, h2, -, -⟩ := hcon
      nlinarith [mul_le_mul_of_nonneg_left h1 hc, mul_le_mul_of_nonneg_left h2 hd,
        mul_lt_mul_of_pos_left h hb, mul_lt_mul_of_pos_left h ha,
        (by rw [hab] : (a + b) * z₀ = (c + d) * z₀), (by rw [hab] : (a + b) * z₂ = (c + d) * z₂)]
    · by_contra hcon; push Not at hcon
      obtain ⟨-, -, h3, h4⟩ := hcon
      nlinarith [mul_le_mul_of_nonneg_left h3 hc, mul_le_mul_of_nonneg_left h4 hd,
        mul_lt_mul_of_pos_left h hb, mul_lt_mul_of_pos_left h ha,
        (by rw [hab] : (a + b) * z₀ = (c + d) * z₀), (by rw [hab] : (a + b) * z₂ = (c + d) * z₂)]
  · constructor
    · by_contra hcon; push Not at hcon
      obtain ⟨-, -, h3, h4⟩ := hcon
      nlinarith [mul_le_mul_of_nonneg_left h3 hc, mul_le_mul_of_nonneg_left h4 hd,
        mul_lt_mul_of_pos_left h hb, mul_lt_mul_of_pos_left h ha,
        (by rw [hab] : (a + b) * z₀ = (c + d) * z₀), (by rw [hab] : (a + b) * z₂ = (c + d) * z₂)]
    · by_contra hcon; push Not at hcon
      obtain ⟨h1, h2, -, -⟩ := hcon
      nlinarith [mul_le_mul_of_nonneg_left h1 hc, mul_le_mul_of_nonneg_left h2 hd,
        mul_lt_mul_of_pos_left h hb, mul_lt_mul_of_pos_left h ha,
        (by rw [hab] : (a + b) * z₀ = (c + d) * z₀), (by rw [hab] : (a + b) * z₂ = (c + d) * z₂)]

theorem det3_L_identity (x y x' y' w : ℝ³) :
    det3 (y - x) (x' - x) (det3 (x' - y) (y' - y) w • x - det3 (x' - x) (y' - x) w • y +
      det3 (y - x) (y' - x) w • x' - det3 (y - x) (x' - x) w • y') =
      -(det3 (y - x) (x' - x) w * det3 (y - x) (x' - x) (y' - x)) := by
  simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **Planar equator** (Corollary 5.4 in L9). -/
theorem isRupert_planar_equator {t t' x x' y y' : ℝ³} (h : IsOctahedron t t' x x' y y')
    (hpl : det3 (y - x) (x' - x) (y' - x) = 0) : IsRupert {t, t', x, x', y, y'} := by
  have hnd := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨htt, htx, htx', hty, hty'⟩, ⟨ht'x, ht'x', ht'y, ht'y'⟩, ⟨hxx', hxy, hxy'⟩,
    ⟨hx'y, hx'y'⟩, hyy', -⟩ := hnd
  set u := t' - t with hu
  set v := x - x' with hv
  set w : ℝ → ℝ³ := fun ε => u + ε • v with hw
  have hu0 : u ≠ 0 := sub_ne_zero.mpr (Ne.symm htt)
  -- the four corner areas at the tilted views have one strict sign
  have hS : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (0 < det3 (x' - y) (y' - y) (w ε) ∧ 0 < det3 (x' - x) (y' - x) (w ε) ∧
        0 < det3 (y - x) (y' - x) (w ε) ∧ 0 < det3 (y - x) (x' - x) (w ε)) ∨
      (det3 (x' - y) (y' - y) (w ε) < 0 ∧ det3 (x' - x) (y' - x) (w ε) < 0 ∧
        det3 (y - x) (y' - x) (w ε) < 0 ∧ det3 (y - x) (x' - x) (w ε) < 0) := by
    have ev : ∀ {a b : ℝ³}, 0 < det3 a b u → ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 a b (w ε) :=
      fun {a b} h0 => by simp only [hw, det3_add_smul]; exact eventually_pos_affine (Or.inl h0)
    have ev' : ∀ {a b : ℝ³}, det3 a b u < 0 → ∀ᶠ ε in 𝓝[>] (0 : ℝ), det3 a b (w ε) < 0 :=
      fun {a b} h0 => by
        have := eventually_pos_affine (A := -det3 a b u) (B := -det3 a b v) (Or.inl (by linarith))
        filter_upwards [this] with ε hε
        simp only [hw, det3_add_smul]; linarith
    rcases lt_or_gt_of_ne (axis_orient_ne h) with hneg | hpos
    · obtain ⟨E1, E2, E3, -⟩ := axis_tests h.swap₁ (by
        rw [← neg_sub t' t, det3_neg_right]
        linarith)
      have n : ∀ {a b : ℝ³}, 0 < det3 a b (t - t') → det3 a b u < 0 := fun h0 => by
        rw [← neg_sub t' t, det3_neg_right] at h0; linarith
      filter_upwards [ev' (n (E2 y' (by simp) (Ne.symm hyy') (Ne.symm hx'y'))),
        ev' (n (by rw [← det3_cyc x x' y']; exact E3 x (by simp) hxx' hxy')),
        ev' (n (E1 y' (by simp) (Ne.symm hxy') (Ne.symm hyy'))),
        ev' (n (E1 x' (by simp) (Ne.symm hxx') hx'y))] with ε h1 h2 h3 h4
      exact Or.inr ⟨h1, h2, h3, h4⟩
    · obtain ⟨E1, E2, E3, -⟩ := axis_tests h hpos
      filter_upwards [ev (E2 y' (by simp) (Ne.symm hyy') (Ne.symm hx'y')),
        ev (by rw [← det3_cyc x x' y']; exact E3 x (by simp) hxx' hxy'),
        ev (E1 y' (by simp) (Ne.symm hxy') (Ne.symm hyy')),
        ev (E1 x' (by simp) (Ne.symm hxx') hx'y)] with ε h1 h2 h3 h4
      exact Or.inl ⟨h1, h2, h3, h4⟩
  -- the diagonal `x x'` is not level
  have hlev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪x, w ε⟫ ≠ ⟪x', w ε⟫ := by
    have hvv : 0 < ⟪v, v⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hxx')
    have e : ∀ ε, ⟪x, w ε⟫ - ⟪x', w ε⟫ = ⟪v, u⟫ + ε * ⟪v, v⟫ := by
      intro ε; simp only [hw, hv, inner_add_right, real_inner_smul_right, inner_sub_left]; ring
    rcases le_or_gt 0 ⟪v, u⟫ with h0 | h0
    · filter_upwards [eventually_pos_affine (A := ⟪v, u⟫) (B := ⟪v, v⟫)
        (by rcases h0.lt_or_eq with h0 | h0; exacts [Or.inl h0, Or.inr ⟨h0.symm, hvv⟩])] with ε hε
      intro h1; have := e ε; linarith
    · filter_upwards [eventually_pos_affine (A := -⟪v, u⟫) (B := -⟪v, v⟫)
        (Or.inl (by linarith))] with ε hε
      intro h1; have := e ε; linarith
  have hw0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), w ε ≠ 0 := by
    have hc : Continuous w := by rw [hw]; fun_prop
    exact (hc.continuousAt.eventually_ne (by simpa [hw] using hu0)).filter_mono nhdsWithin_le_nhds
  refine isRupert_axis h v ?_
  filter_upwards [hS, hlev, hw0] with ε hε hl hw0ε
  -- the diagonals cross: `S₁ x + S₃ x' = S₂ y + S₄ y'`
  set S₁ := det3 (x' - y) (y' - y) (w ε)
  set S₂ := det3 (x' - x) (y' - x) (w ε)
  set S₃ := det3 (y - x) (y' - x) (w ε)
  set S₄ := det3 (y - x) (x' - x) (w ε)
  have hpar := four_point_parallel x y x' y' (w ε) hw0ε
  set L := S₁ • x - S₂ • y + S₃ • x' - S₄ • y'
  set lam := ⟪L, w ε⟫ / ⟪w ε, w ε⟫
  have hS4 : S₄ ≠ 0 := by
    rcases hε with ⟨-, -, -, h4⟩ | ⟨-, -, -, h4⟩
    · exact h4.ne'
    · exact h4.ne
  have hlam : lam = 0 := by
    have e1 := det3_L_identity x y x' y' (w ε)
    rw [hpl, mul_zero, neg_zero] at e1
    have e2 : det3 (y - x) (x' - x) L = lam * S₄ := by
      rw [hpar]; simp only [det3_expand, PiLp.smul_apply, smul_eq_mul, S₄]; ring
    have : lam * S₄ = 0 := by rw [← e2]; exact e1
    exact (mul_eq_zero.mp this).resolve_right hS4
  have hL : L = 0 := by rw [hpar, hlam, zero_smul]
  have hz : S₁ * ⟪x, w ε⟫ + S₃ * ⟪x', w ε⟫ = S₂ * ⟪y, w ε⟫ + S₄ * ⟪y', w ε⟫ := by
    have := congrArg (fun z => ⟪z, w ε⟫) hL
    simp only [L, inner_sub_left, inner_add_left, real_inner_smul_left, inner_zero_left] at this
    linarith
  have hsum := four_point_sum x y x' y' (w ε)
  have hQ : NWS4 (quad ⟪x, w ε⟫ ⟪y, w ε⟫ ⟪x', w ε⟫ ⟪y', w ε⟫) := by
    rcases hε with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact NWS4_of_crossing h1 h3 h2.le h4.le (by linarith) hz hl
    · exact NWS4_of_crossing (a := -S₁) (b := -S₃) (c := -S₂) (d := -S₄) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hl
  convert hQ using 1; funext i
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl

theorem det3_eq_zero_of_perp {a b c d : ℝ³} (hd : d ≠ 0) (ha : ⟪a, d⟫ = 0) (hb : ⟪b, d⟫ = 0)
    (hc : ⟪c, d⟫ = 0) : det3 a b c = 0 := by
  have hcr : cross d (cross a b) = 0 := by
    have e : cross d (cross a b) = ⟪d, b⟫ • a - ⟪d, a⟫ • b := by
      ext i; fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cross_apply_zero, cross_apply_one,
          cross_apply_two, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply,
          Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] <;> ring
    rw [e, real_inner_comm, hb, real_inner_comm, ha, zero_smul, zero_smul, sub_zero]
  have := eq_smul_of_cross_eq_zero hd hcr
  change ⟪cross a b, c⟫ = 0
  rw [this, real_inner_smul_left, real_inner_comm c d, hc, mul_zero]

/-- **Lemma 9.4 (two touching edges).**  If `p'- p` is perpendicular to `y - x`
and to `x' - y'`, the octahedron is Rupert (axis `pp'`). -/
theorem isRupert_of_touching_pair {p p' x x' y y' : ℝ³} (h : IsOctahedron p p' x x' y y')
    (h₁ : ⟪p' - p, y - x⟫ = 0) (h₂ : ⟪p' - p, x' - y'⟫ = 0) : IsRupert {p, p', x, x', y, y'} := by
  have e₁ : ⟪x, p' - p⟫ = ⟪y, p' - p⟫ := by
    rw [inner_sub_right] at h₁
    rw [real_inner_comm (p' - p) x, real_inner_comm (p' - p) y]
    linarith only [h₁]
  have e₂ : ⟪x', p' - p⟫ = ⟪y', p' - p⟫ := by
    rw [inner_sub_right] at h₂
    rw [real_inner_comm (p' - p) x', real_inner_comm (p' - p) y']
    linarith only [h₂]
  by_cases hne : ⟪x, p' - p⟫ = ⟪x', p' - p⟫
  · have hnd := h.nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
    have hd : p' - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hnd.1.1)
    refine isRupert_planar_equator h (det3_eq_zero_of_perp hd ?_ ?_ ?_)
    · rw [inner_sub_left]; linarith
    · rw [inner_sub_left]; linarith
    · rw [inner_sub_left]; linarith
  · refine isRupert_axis_NWS h ?_
    simp only [NWS4, quad_0, quad_1, quad_2, quad_3]
    rw [← e₁, ← e₂]
    rcases lt_or_gt_of_ne hne with h3 | h3
    · exact ⟨Or.inr (Or.inl h3), Or.inr (Or.inr (Or.inl h3))⟩
    · exact ⟨Or.inr (Or.inr (Or.inl h3)), Or.inr (Or.inl h3)⟩

end Minimality

end RupertMinimality
