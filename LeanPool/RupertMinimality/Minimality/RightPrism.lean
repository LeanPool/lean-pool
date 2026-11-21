/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Tilt

/-! # Right Prism -/

@[expose] public section

namespace RupertMinimality

/-!
# Theorem 8.1: right prisms

Every right prism over a strictly convex polygon is Rupert, by an explicit
first-order motion at the views `e_z + εv` next to the axis (L7 is not
used).  With Theorem 7.7 this covers every translation prism over a
triangle.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

open Classical in
/-- The right prism over the polygon `p` (in the plane `z = 0`) of height `h`. -/
noncomputable def rightPrism {k : ℕ} [NeZero k] (p : ZMod k → ℝ²) (h : ℝ) : Finset ℝ³ :=
  (univ.image fun i => liftPt (p i) 0) ∪ (univ.image fun i => liftPt (p i) h)

open Classical in
theorem mem_rightPrism {k : ℕ} [NeZero k] (p : ZMod k → ℝ²) (h : ℝ) (x : ℝ³) :
    x ∈ rightPrism p h ↔ (∃ j, liftPt (p j) 0 = x) ∨ ∃ j, liftPt (p j) h = x := by
  simp [rightPrism]

theorem det3_tilt (a b : ℝ³) (v : ℝ²) (ε : ℝ) :
    det3 a b (ez + ε • liftPt v 0) = cross2 (projXy a) (projXy b) +
      ε * (a 2 * cross2 (projXy b) v - b 2 * cross2 (projXy a) v) := by
  simp [det3, cross, cross2, ez, liftPt, projXy, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem tilt_test {a b : ℝ³} (v : ℝ²)
    (h : 0 < cross2 (projXy a) (projXy b) ∨ (cross2 (projXy a) (projXy b) = 0 ∧
      0 < a 2 * cross2 (projXy b) v - b 2 * cross2 (projXy a) v)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 a b (ez + ε • liftPt v 0) := by
  simp only [det3_tilt]; exact eventually_pos_affine h

theorem proj_liftPt_sub (q₁ q₂ : ℝ²) (z₁ z₂ : ℝ) :
    projXy (liftPt q₁ z₁ - liftPt q₂ z₂) = q₁ - q₂ := by
  rw [proj_xy_sub', proj_xy_liftPt, proj_xy_liftPt]

theorem liftPt_sub_two (q₁ q₂ : ℝ²) (z₁ z₂ : ℝ) :
    (liftPt q₁ z₁ - liftPt q₂ z₂) 2 = z₁ - z₂ := by
  rw [PiLp.sub_apply, liftPt_two, liftPt_two]

theorem finite_affine_zero {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) : {t : ℝ | a * t + b = 0}.Finite := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := h.resolve_left (not_not.mpr ha)
    simp [ha, hb]
  · refine (Set.finite_singleton (-b / a)).subset fun t ht => ?_
    simp only [Set.mem_ofPred_eq] at ht
    simp only [Set.mem_singleton_iff]
    field_simp; linarith

/-- A direction parallel to none of finitely many vectors and perpendicular to
none of finitely many others. -/
theorem exists_generic_dir {ι κ : Type*} [Finite ι] [Finite κ] (E : ι → ℝ²) (hE : ∀ i, E i ≠ 0)
    (D : κ → ℝ²) (hD : ∀ i, D i ≠ 0) :
    ∃ v : ℝ², (∀ i, cross2 (E i) v ≠ 0) ∧ ∀ i, ⟪v, D i⟫ ≠ 0 := by
  have hne : ∀ q : ℝ², q ≠ 0 → q 0 ≠ 0 ∨ q 1 ≠ 0 := by
    intro q hq
    by_contra hc; push Not at hc
    apply hq; ext i; fin_cases i
    · exact hc.1
    · exact hc.2
  have hfin : ((⋃ i, {t : ℝ | E i 0 * t + -E i 1 = 0}) ∪
      ⋃ i, {t : ℝ | D i 1 * t + D i 0 = 0}).Finite := by
    refine (Set.finite_iUnion fun i => finite_affine_zero ?_).union
      (Set.finite_iUnion fun i => finite_affine_zero ?_)
    · rcases hne _ (hE i) with h | h
      · exact Or.inl h
      · exact Or.inr (neg_ne_zero.mpr h)
    · exact (hne _ (hD i)).symm
  obtain ⟨t, ht⟩ := hfin.exists_notMem
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists] at ht
  refine ⟨!₂[1, t], fun i h => ht.1 i ?_, fun i h => ht.2 i ?_⟩
  · simp [cross2] at h; linarith
  · simp [PiLp.inner_apply, Fin.sum_univ_two] at h; linarith

theorem eventually_atTop_pos (A B : ℝ) (hB : 0 < B) : ∀ᶠ t in atTop, 0 < A + t * B := by
  filter_upwards [eventually_gt_atTop (-A / B)] with t ht
  rw [div_lt_iff₀ hB] at ht; linarith

theorem liftPt_sub_liftPt (q₁ q₂ : ℝ²) (z₁ z₂ : ℝ) :
    liftPt q₁ z₁ - liftPt q₂ z₂ = liftPt (q₁ - q₂) (z₁ - z₂) := by
  ext i; fin_cases i <;> simp [liftPt]

/-- One determinant test at the tilted view, for a lifted first vector. -/
theorem tt (v q : ℝ²) (z : ℝ) (b : ℝ³)
    (h : 0 < cross2 q (projXy b) ∨
      (cross2 q (projXy b) = 0 ∧ 0 < z * cross2 (projXy b) v - b 2 * cross2 q v)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < det3 (liftPt q z) b (ez + ε • liftPt v 0) := by
  apply tilt_test v
  rwa [proj_xy_liftPt, liftPt_two]

section certs

variable (V : Finset ℝ³) (v : ℝ²) (ω τ : ℝ³)

/-- A corner between two points at its own height. -/
theorem cert_flat {q qm qp : ℝ²} {z : ℝ} (hm : liftPt qm z ∈ V) (hp : liftPt qp z ∈ V)
    (hE : 0 < cross2 (q - qm) (qp - q))
    (h1 : 0 < cross2 (qp - q) (projXy (cross ω (liftPt q z) + τ)))
    (h2 : 0 < cross2 (q - qm) (projXy (cross ω (liftPt q z) + τ))) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (ez + ε • liftPt v 0) ω τ (liftPt q z) := by
  have T1 := tt v (qp - q) 0 (liftPt (qm - q) 0) (Or.inl (by
    rw [proj_xy_liftPt]
    have : cross2 (qp - q) (qm - q) = cross2 (q - qm) (qp - q) := by simp [cross2]; ring
    rw [this]; exact hE))
  have T2 := tt v (qp - q) 0 _ (Or.inl h1)
  have T3 := tt v (q - qm) 0 _ (Or.inl h2)
  filter_upwards [T1, T2, T3] with ε t1 t2 t3
  refine Or.inl ⟨_, hm, _, hp, ?_, ?_, ?_⟩ <;> rw [liftPt_sub_liftPt] <;>
    simp only [liftPt_sub_liftPt, sub_self] at * <;> assumption

/-- A corner `x` between a point `qm` at its height (before) and the point
above or below it (after), at height difference `d`. -/
theorem cert_up {q qm : ℝ²} {z d : ℝ} (hm : liftPt qm z ∈ V) (hu : liftPt q (z + d) ∈ V)
    (h0 : 0 < d * cross2 (qm - q) v)
    (h1 : 0 < d * cross2 (projXy (cross ω (liftPt q z) + τ)) v)
    (h2 : 0 < cross2 (q - qm) (projXy (cross ω (liftPt q z) + τ))) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (ez + ε • liftPt v 0) ω τ (liftPt q z) := by
  have T1 := tt v 0 d (liftPt (qm - q) 0) (Or.inr ⟨by simp [cross2],
    by rw [proj_xy_liftPt, liftPt_two]; simpa [cross2] using h0⟩)
  have T2 := tt v 0 d (cross ω (liftPt q z) + τ) (Or.inr ⟨by simp [cross2],
    by simpa [cross2] using h1⟩)
  have T3 := tt v (q - qm) 0 _ (Or.inl h2)
  filter_upwards [T1, T2, T3] with ε t1 t2 t3
  refine Or.inl ⟨_, hm, _, hu, ?_, ?_, ?_⟩
  · rw [liftPt_sub_liftPt, liftPt_sub_liftPt, sub_self, sub_self, add_sub_cancel_left]; exact t1
  · rw [liftPt_sub_liftPt, sub_self, add_sub_cancel_left]; exact t2
  · rw [liftPt_sub_liftPt, sub_self]; exact t3

/-- A corner `x` between the point above or below it (before, at height
difference `d`) and a point `qp` at its height (after). -/
theorem cert_down {q qp : ℝ²} {z d : ℝ} (hu : liftPt q (z + d) ∈ V) (hp : liftPt qp z ∈ V)
    (h0 : 0 < -(d * cross2 (qp - q) v))
    (h1 : 0 < cross2 (qp - q) (projXy (cross ω (liftPt q z) + τ)))
    (h2 : 0 < -(d * cross2 (projXy (cross ω (liftPt q z) + τ)) v)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (ez + ε • liftPt v 0) ω τ (liftPt q z) := by
  have T1 := tt v (qp - q) 0 (liftPt 0 d) (Or.inr ⟨by simp [cross2, proj_xy_liftPt],
    by rw [proj_xy_liftPt, liftPt_two]; simpa [cross2] using h0⟩)
  have T2 := tt v (qp - q) 0 _ (Or.inl h1)
  have T3 := tt v 0 (-d) (cross ω (liftPt q z) + τ) (Or.inr ⟨by simp [cross2],
    by simpa [cross2] using h2⟩)
  filter_upwards [T1, T2, T3] with ε t1 t2 t3
  refine Or.inl ⟨_, hu, _, hp, ?_, ?_, ?_⟩
  · rw [liftPt_sub_liftPt, liftPt_sub_liftPt, sub_self, sub_self, add_sub_cancel_left]; exact t1
  · rw [liftPt_sub_liftPt, sub_self]; exact t2
  · rw [liftPt_sub_liftPt, sub_self, show z - (z + d) = -d by ring]; exact t3

/-- A hidden point, strictly inside the triangle `qm q qp` shifted by `d`. -/
theorem cert_hidden {q qm qp : ℝ²} {z d : ℝ} (hm : liftPt qm (z + d) ∈ V)
    (h0 : liftPt q (z + d) ∈ V) (hp : liftPt qp (z + d) ∈ V)
    (hE : 0 < cross2 (q - qm) (qp - q))
    (h1 : 0 < d * cross2 (q - qm) v) (h2 : 0 < d * cross2 (qp - q) v) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), TiltCert V (ez + ε • liftPt v 0) ω τ (liftPt q z) := by
  have T0 := tt v (q - qm) 0 (liftPt (qp - qm) 0) (Or.inl (by
    rw [proj_xy_liftPt]
    have : cross2 (q - qm) (qp - qm) = cross2 (q - qm) (qp - q) := by simp [cross2]; ring
    rw [this]; exact hE))
  have T1 := tt v (q - qm) 0 (liftPt (q - qm) (-d)) (Or.inr ⟨by
    rw [proj_xy_liftPt, cross2_self], by rw [proj_xy_liftPt, liftPt_two]; simpa using h1⟩)
  have T2 := tt v (qp - q) 0 (liftPt 0 (-d)) (Or.inr ⟨by simp [cross2, proj_xy_liftPt],
    by rw [proj_xy_liftPt, liftPt_two]; simpa [cross2] using h2⟩)
  have T3 := tt v (qm - qp) 0 (liftPt (q - qp) (-d)) (Or.inl (by
    rw [proj_xy_liftPt]
    have : cross2 (qm - qp) (q - qp) = cross2 (q - qm) (qp - q) := by simp [cross2]; ring
    rw [this]; exact hE))
  filter_upwards [T0, T1, T2, T3] with ε t0 t1 t2 t3
  refine Or.inr ⟨_, hm, _, h0, _, hp, ?_, ?_, ?_, ?_⟩
  · rw [liftPt_sub_liftPt, liftPt_sub_liftPt, sub_self]; exact t0
  · rw [liftPt_sub_liftPt, liftPt_sub_liftPt, sub_self, show z - (z + d) = -d by ring]; exact t1
  · rw [liftPt_sub_liftPt, liftPt_sub_liftPt, sub_self, sub_self,
      show z - (z + d) = -d by ring]; exact t2
  · rw [liftPt_sub_liftPt, liftPt_sub_liftPt, sub_self, show z - (z + d) = -d by ring]; exact t3

end certs

theorem isCcwPolygon_tri {a b c : ℝ²} (h0 : 0 < cross2 (b - a) (c - a)) :
    IsCcwPolygon (tri a b c) := by
  have e1 : cross2 (c - b) (a - b) = cross2 (b - a) (c - a) := by simp [cross2]; ring
  have e2 : cross2 (a - c) (b - c) = cross2 (b - a) (c - a) := by simp [cross2]; ring
  refine ⟨le_refl _, fun i j hi hj => ?_⟩
  have hcase : ∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 →
      (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by decide
  rcases hcase i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h0
  · change 0 < cross2 (c - b) (a - b); rw [e1]; exact h0
  · change 0 < cross2 (a - c) (b - c); rw [e2]; exact h0

theorem exists_zmod3 {P : ZMod 3 → Prop} : (∃ j, P j) ↔ P 0 ∨ P 1 ∨ P 2 := by
  constructor
  · rintro ⟨j, hj⟩
    have : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases this j with rfl | rfl | rfl
    exacts [Or.inl hj, Or.inr (Or.inl hj), Or.inr (Or.inr hj)]
  · rintro (h | h | h) <;> exact ⟨_, h⟩

theorem rightPrism_tri (a b c : ℝ²) (h : ℝ) :
    rightPrism (tri a b c) h =
      {liftPt a 0, liftPt b 0, liftPt c 0, liftPt a h, liftPt b h, liftPt c h} := by
  ext x
  rw [mem_rightPrism, exists_zmod3, exists_zmod3]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ((h | h | h) | (h | h | h)) <;> rw [← h] <;> simp [tri]
  · rintro (h | h | h | h | h | h) <;> subst h <;> simp [tri]

/-- **Theorem 8.1, general form.**  The right prism `rightPrism p h` inside a larger finite set `V`
is Rupert provided the extra points of `V` have tilt certificates at the chosen (generic) direction
and spin, `hex`, whatever the direction `v` and the data `ω, τ` are. -/
theorem isRupert_rightPrism_gen {k : ℕ} [NeZero k] (p : ZMod k → ℝ²) (hp : IsCcwPolygon p) {h : ℝ}
    (hh : 0 < h) (V : Finset ℝ³) (hV : rightPrism p h ⊆ V)
    (hex : ∀ (v : ℝ²) (ω τ : ℝ³), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ V \ rightPrism p h,
      TiltCert V (ez + ε • liftPt v 0) ω τ y) : IsRupert V := by
  classical
  have hk := hp.1
  -- a generic tilt direction
  obtain ⟨v, hv1, hv2⟩ := exists_generic_dir (ι := ZMod k)
    (κ := {q : ZMod k × ZMod k // q.1 ≠ q.2}) (fun i => p (i + 1) - p i)
    (fun i => hp.edge_ne_zero i) (fun q => p q.1.1 - p q.1.2)
    (fun q => sub_ne_zero.mpr (hp.injective.ne q.2))
  have hsm : ∀ j, cross2 (p j - p (j - 1)) v ≠ 0 := fun j => by
    simpa using hv1 (j - 1)
  set m : ℝ² := rot90 v with hm
  have hme : ∀ q : ℝ², ⟪m, q⟫ = -cross2 q v := by
    intro q; simp [hm, rot90, cross2, PiLp.inner_apply, Fin.sum_univ_two]; ring
  have hv0 : v ≠ 0 := by rintro rfl; exact hv1 0 (by simp [cross2])
  have hm0 : m ≠ 0 := by
    intro h0; apply hv0
    have e0 := congrArg (· 0) h0; have e1 := congrArg (· 1) h0
    simp [hm, rot90] at e0 e1
    ext i; fin_cases i <;> simp [e0, e1]
  obtain ⟨a, -, ha⟩ := exists_max_image univ (fun i => ⟪m, p i⟫) ⟨0, mem_univ _⟩
  obtain ⟨b, -, hb⟩ := exists_min_image univ (fun i => ⟪m, p i⟫) ⟨0, mem_univ _⟩
  -- the unique local maximum and minimum of `⟪m, ·⟫`
  have hloc : ∀ j, cross2 (p j - p (j - 1)) v < 0 → 0 < cross2 (p (j + 1) - p j) v →
      ∀ l, l ≠ j → ⟪m, p l⟫ < ⟪m, p j⟫ := by
    intro j h1 h2 l hl
    have i1 : 0 < ⟪m, p j - p (j - 1)⟫ := by rw [hme]; linarith
    have i2 : ⟪m, p (j + 1) - p j⟫ < 0 := by rw [hme]; linarith
    by_cases l1 : l = j - 1
    · subst l1; rw [inner_sub_right] at i1; linarith
    by_cases l3 : l = j + 1
    · subst l3; rw [inner_sub_right] at i2; linarith
    exact hp.lt_of_localMax hm0 i1.le i2.le l1 hl l3
  have hloc' : ∀ j, 0 < cross2 (p j - p (j - 1)) v → cross2 (p (j + 1) - p j) v < 0 →
      ∀ l, l ≠ j → ⟪m, p j⟫ < ⟪m, p l⟫ := by
    intro j h1 h2 l hl
    have i1 : 0 ≤ ⟪-m, p j - p (j - 1)⟫ := by rw [inner_neg_left, hme]; linarith
    have i2 : ⟪-m, p (j + 1) - p j⟫ ≤ 0 := by rw [inner_neg_left, hme]; linarith
    have hm0' : -m ≠ 0 := neg_ne_zero.mpr hm0
    by_cases l1 : l = j - 1
    · subst l1; rw [inner_neg_left, hme] at i1
      have := hme (p j - p (j - 1)); rw [inner_sub_right] at this; linarith
    by_cases l3 : l = j + 1
    · subst l3
      have := hme (p (j + 1) - p j); rw [inner_sub_right] at this; linarith
    have := hp.lt_of_localMax hm0' i1 i2 l1 hl l3
    rw [inner_neg_left, inner_neg_left] at this; linarith
  have hX : ∀ j, cross2 (p j - p (j - 1)) v < 0 → 0 < cross2 (p (j + 1) - p j) v → j = a := by
    intro j h1 h2; by_contra hne
    linarith [hloc j h1 h2 a (Ne.symm hne), ha j (mem_univ _)]
  have hY : ∀ j, 0 < cross2 (p j - p (j - 1)) v → cross2 (p (j + 1) - p j) v < 0 → j = b := by
    intro j h1 h2; by_contra hne
    linarith [hloc' j h1 h2 b (Ne.symm hne), hb j (mem_univ _)]
  have hab : a ≠ b := by
    intro hab
    have h1 := ha 1 (mem_univ _); have h2 := hb 1 (mem_univ _)
    have h3 := ha 0 (mem_univ _); have h4 := hb 0 (mem_univ _)
    rw [← hab] at h2 h4
    apply hv1 0
    have := hme (p (0 + 1) - p 0)
    rw [inner_sub_right, zero_add] at this
    simp only [zero_add]; linarith
  set X := p a with hXdef
  set Y := p b with hYdef
  have hXY : ⟪v, Y - X⟫ ≠ 0 := hv2 ⟨(b, a), hab.symm⟩
  set ψ : ℝ := if 0 < ⟪v, Y - X⟫ then 1 else -1 with hψ
  have hψT : 0 < ψ * ⟪v, Y - X⟫ := by
    rw [hψ]; split_ifs with hc
    · linarith
    · have := lt_of_le_of_ne (not_lt.mp hc) hXY; linarith
  have hψ2 : ψ * ψ = 1 := by rw [hψ]; split_ifs <;> norm_num
  set M : ℝ² := (1 / 2 : ℝ) • (X + Y) with hM
  set A : ZMod k → ZMod k → ℝ := fun i j => ψ * cross2 (p (i + 1) - p i) (rot90 (p j - M))
  set s : ZMod k → ℝ := fun i => cross2 (p (i + 1) - p i) v
  -- the constants `λ` (spin centre) and `κ` (tilt of the inner copy)
  obtain ⟨lam, hlam⟩ := (show ∀ᶠ t in atTop, ∀ i j, s i < 0 → 0 < A i j + t * (-s i) from
    eventually_all.2 fun i => eventually_all.2 fun j => by
      by_cases hi : s i < 0
      · exact (eventually_atTop_pos _ _ (by linarith)).mono fun _ h _ => h
      · exact Eventually.of_forall fun _ h => absurd h hi).exists
  obtain ⟨κ, hκ⟩ := (show ∀ᶠ t in atTop, ∀ i j, 0 < s i →
      0 < (A i j - lam * s i) + t * (h * s i) from
    eventually_all.2 fun i => eventually_all.2 fun j => by
      by_cases hi : 0 < s i
      · exact (eventually_atTop_pos _ _ (by positivity)).mono fun _ h _ => h
      · exact Eventually.of_forall fun _ h => absurd h hi).exists
  set ω : ℝ³ := !₂[-(κ * v 1), κ * v 0, ψ] with hω
  set τ : ℝ³ := !₂[ψ * M 1 - lam * v 0, -(ψ * M 0) - lam * v 1, 0] with hτ
  have hν : ∀ q z, projXy (cross ω (liftPt q z) + τ) =
      ψ • rot90 (q - M) - lam • v + (z * κ) • v := by
    intro q z; ext i; fin_cases i <;> simp [cross, liftPt, projXy, rot90, ω, τ] <;> ring
  have hνe : ∀ i j z, cross2 (p (i + 1) - p i) (projXy (cross ω (liftPt (p j) z) + τ)) =
      A i j + (z * κ - lam) * s i := by
    intro i j z; rw [hν]
    simp only [A, s, cross2_add_right, cross2_sub_right, cross2_smul_right]; ring
  have hνv : ∀ q z, cross2 (projXy (cross ω (liftPt q z) + τ)) v = -(ψ * ⟪q - M, v⟫) := by
    intro q z; rw [hν]; simp [cross2, rot90, PiLp.inner_apply, Fin.sum_univ_two]; ring
  have hνX : ∀ z, 0 < cross2 (projXy (cross ω (liftPt X z) + τ)) v := by
    intro z; rw [hνv]
    have : ⟪X - M, v⟫ = -(1 / 2) * ⟪v, Y - X⟫ := by
      rw [hM, real_inner_comm]; simp only [inner_sub_right, inner_smul_right, inner_add_right]
      simp; ring
    rw [this]; nlinarith
  have hνY : ∀ z, cross2 (projXy (cross ω (liftPt Y z) + τ)) v < 0 := by
    intro z; rw [hνv]
    have : ⟪Y - M, v⟫ = (1 / 2) * ⟪v, Y - X⟫ := by
      rw [hM, real_inner_comm]; simp only [inner_sub_right, inner_smul_right, inner_add_right]
      simp; ring
    rw [this]; nlinarith
  -- edge constraints at the bottom (`B⁺`) and at the top (`B⁻`)
  have hbot : ∀ i j, s i < 0 →
      0 < cross2 (p (i + 1) - p i) (projXy (cross ω (liftPt (p j) 0) + τ)) := by
    intro i j hi; rw [hνe]; have := hlam i j hi; nlinarith
  have htop : ∀ i j, 0 < s i →
      0 < cross2 (p (i + 1) - p i) (projXy (cross ω (liftPt (p j) h) + τ)) := by
    intro i j hi; rw [hνe]; have := hκ i j hi; nlinarith
  have hmemb : ∀ j, liftPt (p j) 0 ∈ V := fun j =>
    hV ((mem_rightPrism p h _).mpr (Or.inl ⟨j, rfl⟩))
  have hmemt : ∀ j, liftPt (p j) h ∈ V := fun j =>
    hV ((mem_rightPrism p h _).mpr (Or.inr ⟨j, rfl⟩))
  have hmemt' : ∀ j, liftPt (p j) (0 + h) ∈ V := fun j => by
    rw [zero_add]; exact hmemt j
  have hmemb' : ∀ j, liftPt (p j) (h + -h) ∈ V := fun j => by
    rw [add_neg_cancel]; exact hmemb j
  have hsj : ∀ j, s (j - 1) = cross2 (p j - p (j - 1)) v := fun j => by simp [s]
  -- certificates at every vertex
  have key : ∀ j, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      TiltCert V (ez + ε • liftPt v 0) ω τ (liftPt (p j) 0) ∧
      TiltCert V (ez + ε • liftPt v 0) ω τ (liftPt (p j) h) := by
    intro j
    have hE := hp.cross2_edge_pos j
    have bm : ∀ z, cross2 (p j - p (j - 1)) (projXy (cross ω (liftPt (p j) z) + τ)) =
        A (j - 1) j + (z * κ - lam) * s (j - 1) := by
      intro z; rw [← hνe]; simp
    have hbm : cross2 (p j - p (j - 1)) v < 0 →
        0 < cross2 (p j - p (j - 1)) (projXy (cross ω (liftPt (p j) 0) + τ)) := by
      intro hc; rw [bm]; have := hlam (j - 1) j (by rw [hsj]; exact hc); nlinarith
    have htm : 0 < cross2 (p j - p (j - 1)) v →
        0 < cross2 (p j - p (j - 1)) (projXy (cross ω (liftPt (p j) h) + τ)) := by
      intro hc; rw [bm]; have := hκ (j - 1) j (by rw [hsj]; exact hc); nlinarith
    rcases lt_or_gt_of_ne (hsm j) with h1 | h1 <;>
      rcases lt_or_gt_of_ne (hv1 j) with h2 | h2
    · -- both edges in `B⁺`
      refine (cert_flat _ v ω τ (hmemb _) (hmemb _) hE (hbot j j h2) (hbm h1)).and ?_
      refine cert_hidden _ v ω τ (hmemb' _) (hmemb' _) (hmemb' _) hE ?_ ?_
      · nlinarith
      · nlinarith
    · -- `X`: the maximum of `⟪m, ·⟫`
      have hj := hX j h1 h2
      refine (cert_up _ v ω τ (hmemb _) (hmemt' _) ?_ ?_ (hbm h1)).and
        (cert_down _ v ω τ (hmemb' _) (hmemt _) ?_ (htop j j h2) ?_)
      · have : cross2 (p (j - 1) - p j) v = -cross2 (p j - p (j - 1)) v := by
          simp [cross2]; ring
        rw [this]; nlinarith
      · rw [hj]; nlinarith [hνX 0]
      · nlinarith
      · rw [hj]; nlinarith [hνX h]
    · -- `Y`: the minimum of `⟪m, ·⟫`
      have hj := hY j h1 h2
      refine (cert_down _ v ω τ (hmemt' _) (hmemb _) ?_ (hbot j j h2) ?_).and
        (cert_up _ v ω τ (hmemt _) (hmemb' _) ?_ ?_ (htm h1))
      · nlinarith
      · rw [hj]; nlinarith [hνY 0]
      · have : cross2 (p (j - 1) - p j) v = -cross2 (p j - p (j - 1)) v := by
          simp [cross2]; ring
        rw [this]; nlinarith
      · rw [hj]; nlinarith [hνY h]
    · -- both edges in `B⁻`
      refine (cert_hidden _ v ω τ (hmemt' _) (hmemt' _) (hmemt' _) hE ?_ ?_).and
        (cert_flat _ v ω τ (hmemt _) (hmemt _) hE (htop j j h2) (htm h1))
      · nlinarith
      · nlinarith
  obtain ⟨ε, hε, hεy⟩ := ((eventually_all.2 key).and (hex v ω τ)).exists
  refine isRupert_of_tiltCert _ (ez + ε • liftPt v 0) ?_ ω τ fun x hx => ?_
  · intro h0
    have := congrArg (· 2) h0
    simp [ez, liftPt] at this
  · by_cases hxp : x ∈ rightPrism p h
    · rcases (mem_rightPrism p h x).mp hxp with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact (hε j).1
      · exact (hε j).2
    · exact hεy x (Finset.mem_sdiff.mpr ⟨hx, hxp⟩)

/-- **Theorem 8.1.**  Every right prism over a strictly convex polygon is
Rupert. -/
theorem isRupert_rightPrism {k : ℕ} [NeZero k] (p : ZMod k → ℝ²) (hp : IsCcwPolygon p) {h : ℝ}
    (hh : 0 < h) : IsRupert (rightPrism p h) :=
  isRupert_rightPrism_gen p hp hh _ subset_rfl fun _ _ _ =>
    Eventually.of_forall fun _ _y hy => absurd (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2

/-- Right translation prisms over a triangle, in any position. -/
theorem isRupert_translationPrism_right (A B C w : ℝ³)
    (hind : AffineIndependent ℝ ![A, B, C, A + w]) (hB : ⟪w, B - A⟫ = 0) (hC : ⟪w, C - A⟫ = 0) :
    IsRupert {A, B, C, A + w, B + w, C + w} := by
  classical
  have hD : det3 (B - A) (C - A) w ≠ 0 := by
    intro h0
    exact not_coplanar_of_affineIndependent hind
      (coplanar_of_det4_eq_zero (by rw [det4, add_sub_cancel_left]; exact h0))
  have hw0 : w ≠ 0 := by rintro rfl; simp [det3] at hD
  obtain ⟨R, hR, lam, hlam, hRw⟩ := exists_rotation_to_ez_pos w hw0
  set L := R.toEuclideanLin
  have hz : ∀ u, ⟪w, u⟫ = 0 → (L u) 2 = 0 := by
    intro u hu
    have : lam * (L u) 2 = ⟪w, u⟫ := by
      rw [← inner_ez, ← real_inner_smul_right, ← hRw, inner_toEuclideanLin_SO3 hR,
        real_inner_comm]
    rw [hu] at this
    exact (mul_eq_zero.mp this).resolve_left hlam.ne'
  set b := projXy (L (B - A))
  set c := projXy (L (C - A))
  have hLB : L (B - A) = liftPt b 0 := by rw [← hz _ hB, liftPt_proj_xy]
  have hLC : L (C - A) = liftPt c 0 := by rw [← hz _ hC, liftPt_proj_xy]
  have hlift : ∀ q : ℝ², liftPt q 0 + lam • ez = liftPt q lam := by
    intro q; ext i; fin_cases i <;> simp [liftPt, ez]
  have hcr : lam * cross2 b c = det3 (B - A) (C - A) w := cross2_proj_rot hR hRw _ _
  -- move the prism to standard position
  apply isRupert_of_isRupert_image_rotation R hR
  apply isRupert_of_isRupert_image_add (-L A)
  have himg : ((({A, B, C, A + w, B + w, C + w} : Finset ℝ³).image L).image
      fun x => -L A + x) = {liftPt 0 0, liftPt b 0, liftPt c 0, liftPt 0 lam, liftPt b lam,
        liftPt c lam} := by
    simp only [Finset.image_insert, Finset.image_singleton, map_add, hRw]
    have e1 : -L A + L A = liftPt 0 0 := by ext i; fin_cases i <;> simp [liftPt]
    have e2 : -L A + L B = liftPt b 0 := by rw [← hLB, map_sub]; abel
    have e3 : -L A + L C = liftPt c 0 := by rw [← hLC, map_sub]; abel
    have e4 : -L A + (L A + lam • ez) = liftPt 0 lam := by
      rw [← hlift, ← e1]; abel
    have e5 : -L A + (L B + lam • ez) = liftPt b lam := by
      rw [← hlift, ← e2]; abel
    have e6 : -L A + (L C + lam • ez) = liftPt c lam := by
      rw [← hlift, ← e3]; abel
    rw [e1, e2, e3, e4, e5, e6]
  rw [himg]
  rcases lt_or_gt_of_ne (show cross2 b c ≠ 0 by
    intro h0; apply hD; rw [← hcr, h0, mul_zero]) with hneg | hpos
  · have hp : IsCcwPolygon (tri 0 c b) := isCcwPolygon_tri (by
      have : cross2 (c - 0) (b - 0) = -cross2 b c := by simp [cross2]; ring
      rw [this]; linarith)
    have := isRupert_rightPrism (tri 0 c b) hp hlam
    rw [rightPrism_tri] at this
    convert this using 1
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · have hp : IsCcwPolygon (tri 0 b c) := isCcwPolygon_tri (by simpa using hpos)
    have := isRupert_rightPrism (tri 0 b c) hp hlam
    rwa [rightPrism_tri] at this

/-- **Every translation prism over a triangle is Rupert** (Theorems 7.7 and
8.1). -/
theorem isRupert_translationPrism_all (A B C w : ℝ³)
    (hind : AffineIndependent ℝ ![A, B, C, A + w]) : IsRupert {A, B, C, A + w, B + w, C + w} := by
  by_cases h : ⟪w, B - A⟫ ≠ 0 ∨ ⟪w, C - A⟫ ≠ 0
  · rcases h with h | h
    · exact isRupert_translationPrism A B C w hind (Or.inl h)
    · exact isRupert_translationPrism A B C w hind (Or.inr (Or.inl h))
  · push Not at h
    exact isRupert_translationPrism_right A B C w hind h.1 h.2

end Minimality

end RupertMinimality
