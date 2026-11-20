/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.CycSeq

/-! # Polygon -/

@[expose] public section

namespace RupertMinimality

/-!
# Strictly convex polygons with cyclically indexed corners

`IsCcwPolygon p` (`p : ZMod k → ℝ²`): every corner lies strictly to the left
of every directed edge not containing it.  Facts used by Theorem 7.3:
* `IsCcwPolygon.cross2_edge_pos`: consecutive edges turn strictly left;
* `IsCcwPolygon.lt_of_localMax`: a weak local maximum of a linear functional
  along the corner cycle is a strict global maximum (except at its neighbours);
* `IsCcwPolygon.pattern_from_max`: from a maximising corner the increments of a
  linear functional are `≤ 0` on an initial run and `≥ 0` afterwards;
* `IsCcwPolygon.normalCone_decomp`: the normal cone at a corner is spanned by
  the outward normals of its two edges.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-- The normal cone of `S` at `p`. -/
def normalConeAt (S : Set ℝ²) (p : ℝ²) : Set ℝ² := {n | ∀ q ∈ S, ⟪n, q - p⟫ ≤ 0}

/-- `p` lists the corners of a strictly convex polygon counterclockwise: every
corner lies strictly to the left of every directed edge not containing it. -/
def IsCcwPolygon {k : ℕ} (p : ZMod k → ℝ²) : Prop :=
  3 ≤ k ∧ ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < cross2 (p (i + 1) - p i) (p j - p i)

/-- Outward normal of the edge from `a` to `b` of a counterclockwise polygon. -/
noncomputable def outNormal (a b : ℝ²) : ℝ² := !₂[(b - a) 1, -((b - a) 0)]

theorem zmod_add_ne {k : ℕ} {a b : ℕ} (ha : a < k) (hb : b < k) (hab : a ≠ b) (i : ZMod k) :
    i + (a : ZMod k) ≠ i + (b : ZMod k) := by
  intro h
  have := add_left_cancel h
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact hab this

theorem zmod_natCast_pred {k : ℕ} (hk : 1 ≤ k) : ((k - 1 : ℕ) : ZMod k) = -1 := by
  rw [Nat.cast_sub hk, ZMod.natCast_self]; simp

theorem zmod_ne_add_one {k : ℕ} (hk : 2 ≤ k) (i : ZMod k) : i ≠ i + 1 := by
  have := zmod_add_ne (k := k) (a := 0) (b := 1) (by omega) (by omega) (by omega) i
  simpa using this

theorem zmod_sub_one_ne_add_one {k : ℕ} (hk : 3 ≤ k) (i : ZMod k) : i - 1 ≠ i + 1 := by
  have := zmod_add_ne (k := k) (a := k - 1) (b := 1) (by omega) (by omega) (by omega) i
  rwa [zmod_natCast_pred (by omega), ← sub_eq_add_neg, Nat.cast_one] at this

/-- `cross2 a b • w = cross2 a w • b - cross2 b w • a` in the plane. -/
theorem cross2_decomp (a b w : ℝ²) : cross2 a b • w = cross2 a w • b - cross2 b w • a := by
  ext i; fin_cases i <;> simp [cross2] <;> ring

namespace IsCcwPolygon

variable {k : ℕ} {p : ZMod k → ℝ²}

/-- Consecutive edges turn strictly left. -/
theorem cross2_edge_pos (hp : IsCcwPolygon p) (i : ZMod k) :
    0 < cross2 (p i - p (i - 1)) (p (i + 1) - p i) := by
  have h := hp.2 (i - 1) (i + 1) (zmod_sub_one_ne_add_one hp.1 i).symm
    (by rw [sub_add_cancel]; exact (zmod_ne_add_one (by have := hp.1; omega) i).symm)
  rw [sub_add_cancel] at h
  have e : p (i + 1) - p (i - 1) = (p i - p (i - 1)) + (p (i + 1) - p i) := by abel
  rwa [e, cross2_add_right, cross2_self, zero_add] at h

/-- A weak local maximum of `⟪ν, ·⟫` along the corner cycle is a strict global
maximum, except at its two neighbours. -/
theorem lt_of_localMax (hp : IsCcwPolygon p) {ν : ℝ²} (hν : ν ≠ 0) {s : ZMod k}
    (h1 : 0 ≤ ⟪ν, p s - p (s - 1)⟫) (h2 : ⟪ν, p (s + 1) - p s⟫ ≤ 0) {j : ZMod k}
    (hj1 : j ≠ s - 1) (hj2 : j ≠ s) (hj3 : j ≠ s + 1) : ⟪ν, p j⟫ < ⟪ν, p s⟫ := by
  set a := p s - p (s - 1)
  set b := p (s + 1) - p s
  set w := p j - p s
  have hD := hp.cross2_edge_pos s
  have hα : 0 < cross2 a w := by
    have := hp.2 (s - 1) j hj1 (by rwa [sub_add_cancel])
    rw [sub_add_cancel] at this
    have e : w = (p j - p (s - 1)) - a := by simp only [w, a]; abel
    rwa [e, cross2_sub_right, cross2_self, sub_zero]
  have hβ : 0 < cross2 b w := hp.2 s j hj2 hj3
  have hdec := cross2_decomp a b w
  have hinner : cross2 a b * ⟪ν, w⟫ = cross2 a w * ⟪ν, b⟫ - cross2 b w * ⟪ν, a⟫ := by
    have := congrArg (fun v => ⟪ν, v⟫) hdec
    simpa [inner_sub_right, real_inner_smul_right] using this
  -- `⟪ν, w⟫ < 0` unless both increments vanish, which forces `ν = 0`
  have hle : ⟪ν, w⟫ ≤ 0 := by
    have : cross2 a b * ⟪ν, w⟫ ≤ 0 := by
      rw [hinner]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hα.le h2, mul_nonneg hβ.le h1]
    by_contra hc; push Not at hc; nlinarith
  rcases lt_or_eq_of_le hle with hlt | heq
  · simp only [w, inner_sub_right] at hlt; linarith
  · exfalso
    have : cross2 a w * ⟪ν, b⟫ - cross2 b w * ⟪ν, a⟫ = 0 := by rw [← hinner, heq, mul_zero]
    have hb0 : ⟪ν, b⟫ = 0 := by
      by_contra hc
      have : cross2 a w * ⟪ν, b⟫ < 0 :=
        mul_neg_of_pos_of_neg hα (lt_of_le_of_ne h2 hc)
      nlinarith [mul_nonneg hβ.le h1]
    have ha0 : ⟪ν, a⟫ = 0 := by
      rw [hb0, mul_zero, zero_sub, neg_eq_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hβ.ne'
    apply hν
    have hD' : cross2 a b ≠ 0 := hD.ne'
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial] at ha0 hb0
    simp only [cross2] at hD'
    have e0 : ν 0 * (a 0 * b 1 - a 1 * b 0) = 0 := by
      linear_combination b 1 * ha0 - a 1 * hb0
    have e1 : ν 1 * (a 0 * b 1 - a 1 * b 0) = 0 := by
      linear_combination -(b 0) * ha0 + a 0 * hb0
    have h0 := (mul_eq_zero.mp e0).resolve_right hD'
    have h1 := (mul_eq_zero.mp e1).resolve_right hD'
    ext i; fin_cases i <;> simp [h0, h1]

theorem ne_add_natCast {k : ℕ} {s : ℕ} (hs0 : 0 < s) (hsk : s < k) (B : ZMod k) :
    B ≠ B + (s : ZMod k) := by
  have := zmod_add_ne (k := k) (a := 0) (b := s) (by omega) hsk (by omega) B
  simpa using this

/-- **Increments from a maximising corner.**  If `p B` maximises `⟪ν, ·⟫`, the
increments of `⟪ν, p (B + n)⟫` are `≤ 0` for `n < t` and `≥ 0` for
`t ≤ n < k`. -/
theorem pattern_from_max (hp : IsCcwPolygon p) (ν : ℝ²) (B : ZMod k)
    (hB : ∀ i, ⟪ν, p i⟫ ≤ ⟪ν, p B⟫) :
    ∃ t, t ≤ k ∧ (∀ n, n < t → ⟪ν, p (B + ((n + 1 : ℕ) : ZMod k)) - p (B + (n : ZMod k))⟫ ≤ 0) ∧
      (∀ n, t ≤ n → n < k → 0 ≤ ⟪ν, p (B + ((n + 1 : ℕ) : ZMod k)) - p (B + (n : ZMod k))⟫) := by
  classical
  have hk := hp.1
  set v : ℕ → ℝ := fun n => ⟪ν, p (B + (n : ZMod k))⟫ with hv
  set x : ℕ → ℝ := fun n => v (n + 1) - v n with hx
  have hxeq : ∀ n, ⟪ν, p (B + ((n + 1 : ℕ) : ZMod k)) - p (B + (n : ZMod k))⟫ = x n := fun n => by
    simp only [hx, hv, inner_sub_right]
  simp only [hxeq]
  by_cases hν : ν = 0
  · exact ⟨0, by omega, fun n hn => by omega, fun n _ _ => by simp [hx, hv, hν]⟩
  have hclaim : ¬ ∃ n1 n2, n1 < n2 ∧ n2 < k ∧ 0 < x n1 ∧ x n2 < 0 := by
    rintro ⟨n1, n2, h12, h2k, hx1, hx2⟩
    obtain ⟨s, hsR, hsmax⟩ := (Finset.Icc (n1 + 1) n2).exists_max_image v
      ⟨n2, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩⟩
    rw [Finset.mem_Icc] at hsR
    have hl : v (s - 1) ≤ v s := by
      by_cases h : n1 + 1 ≤ s - 1
      · exact hsmax (s - 1) (Finset.mem_Icc.mpr ⟨h, by omega⟩)
      · have : s = n1 + 1 := by omega
        subst this
        simp only [hx] at hx1
        rw [show n1 + 1 - 1 = n1 by omega]; linarith
    have hr : v (s + 1) ≤ v s := by
      by_cases h : s + 1 ≤ n2
      · exact hsmax (s + 1) (Finset.mem_Icc.mpr ⟨by omega, h⟩)
      · have : s = n2 := by omega
        subst this
        simp only [hx] at hx2; linarith
    have hcast1 : ((s - 1 : ℕ) : ZMod k) = (s : ZMod k) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hlm : 0 ≤ ⟪ν, p (B + (s : ZMod k)) - p (B + (s : ZMod k) - 1)⟫ := by
      have : v (s - 1) = ⟪ν, p (B + (s : ZMod k) - 1)⟫ := by
        simp only [hv, hcast1, add_sub_assoc]
      rw [inner_sub_right]; simp only [hv] at hl this; linarith
    have hrm : ⟪ν, p (B + (s : ZMod k) + 1) - p (B + (s : ZMod k))⟫ ≤ 0 := by
      have : v (s + 1) = ⟪ν, p (B + (s : ZMod k) + 1)⟫ := by
        simp only [hv, Nat.cast_succ, add_assoc]
      rw [inner_sub_right]; simp only [hv] at hr this; linarith
    by_cases hs1 : s = 1
    · subst hs1
      have : n1 = 0 := by omega
      subst this
      have h := hB (B + ((0 + 1 : ℕ) : ZMod k))
      simp only [hx, hv, Nat.cast_zero, add_zero] at hx1 h
      linarith
    by_cases hsk : s = k - 1
    · have : n2 = k - 1 := by omega
      subst this
      have h := hB (B + ((k - 1 : ℕ) : ZMod k))
      simp only [hx, hv] at hx2 h
      rw [show k - 1 + 1 = k by omega, ZMod.natCast_self, add_zero] at hx2
      linarith
    have hj1 : B ≠ B + (s : ZMod k) - 1 := by
      rw [add_sub_assoc, ← hcast1]
      exact ne_add_natCast (by omega) (by omega) B
    have hj2 : B ≠ B + (s : ZMod k) := ne_add_natCast (by omega) (by omega) B
    have hj3 : B ≠ B + (s : ZMod k) + 1 := by
      rw [add_assoc, ← Nat.cast_succ]
      exact ne_add_natCast (by omega) (by omega) B
    have := hp.lt_of_localMax hν hlm hrm hj1 hj2 hj3
    linarith [hB (B + (s : ZMod k))]
  by_cases hex : ∃ n, n < k ∧ 0 < x n
  · refine ⟨Nat.find hex, (Nat.find_spec hex).1.le, fun n hn => ?_, fun n hn1 hn2 => ?_⟩
    · have := Nat.find_min hex hn
      push Not at this
      by_cases hnk : n < k
      · exact this hnk
      · exact absurd (lt_of_lt_of_le hn (Nat.find_spec hex).1.le) hnk
    · by_contra hc; push Not at hc
      rcases eq_or_lt_of_le hn1 with h | h
      · rw [← h] at hc; linarith [(Nat.find_spec hex).2]
      · exact hclaim ⟨_, n, h, hn2, (Nat.find_spec hex).2, hc⟩
  · push Not at hex
    exact ⟨k, le_rfl, fun n hn => hex n hn, fun n h1 h2 => by omega⟩

/-- The normal cone at a corner is spanned by the outward normals of its two
edges. -/
theorem normalCone_decomp (hp : IsCcwPolygon p) (i : ZMod k) {f : ℝ²}
    (hf : f ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i)) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      f = a • outNormal (p (i - 1)) (p i) + b • outNormal (p i) (p (i + 1)) := by
  set A := p i - p (i - 1)
  set Bv := p (i + 1) - p i
  have hD := hp.cross2_edge_pos i
  set D := cross2 A Bv
  have hrot : cross2 (outNormal (p (i - 1)) (p i)) (outNormal (p i) (p (i + 1))) = D := by
    simp [outNormal, cross2, D, A, Bv]; ring
  have hdec := cross2_decomp (outNormal (p (i - 1)) (p i)) (outNormal (p i) (p (i + 1))) f
  rw [hrot] at hdec
  have hA : 0 ≤ cross2 (outNormal (p (i - 1)) (p i)) f := by
    have := hf (p (i - 1)) (subset_convexHull ℝ _ ⟨_, rfl⟩)
    have e : cross2 (outNormal (p (i - 1)) (p i)) f = -⟪f, p (i - 1) - p i⟫ := by
      simp [outNormal, cross2, PiLp.inner_apply, Fin.sum_univ_two]; ring
    rw [e]; linarith
  have hB : cross2 (outNormal (p i) (p (i + 1))) f ≤ 0 := by
    have := hf (p (i + 1)) (subset_convexHull ℝ _ ⟨_, rfl⟩)
    have e : cross2 (outNormal (p i) (p (i + 1))) f = ⟪f, p (i + 1) - p i⟫ := by
      simp [outNormal, cross2, PiLp.inner_apply, Fin.sum_univ_two]; ring
    rw [e]; exact this
  refine ⟨-cross2 (outNormal (p i) (p (i + 1))) f / D, cross2 (outNormal (p (i - 1)) (p i)) f / D,
    div_nonneg (by linarith) hD.le, div_nonneg hA hD.le, ?_⟩
  apply smul_right_injective ℝ² hD.ne'
  simp only [smul_add, smul_smul]
  rw [hdec]
  rw [mul_div_cancel₀ _ hD.ne', mul_div_cancel₀ _ hD.ne']
  module

/-- Maximisers of a nonzero linear functional among the corners are pairwise
adjacent. -/
theorem max_adjacent (hp : IsCcwPolygon p) {e : ℝ²} (he : e ≠ 0) {i j : ZMod k}
    (hi : ∀ l, ⟪e, p l⟫ ≤ ⟪e, p i⟫) (hj : ⟪e, p j⟫ = ⟪e, p i⟫) :
    j = i - 1 ∨ j = i ∨ j = i + 1 := by
  by_contra h
  push Not at h
  have := hp.lt_of_localMax he (s := i)
    (by rw [inner_sub_right]; linarith [hi (i - 1)])
    (by rw [inner_sub_right]; linarith [hi (i + 1)]) h.1 h.2.1 h.2.2
  linarith

/-- Three consecutive corners cannot all maximise a nonzero linear functional. -/
theorem not_three_max (hp : IsCcwPolygon p) {e : ℝ²} (he : e ≠ 0) (i : ZMod k)
    (h1 : ⟪e, p (i - 1)⟫ = ⟪e, p i⟫) (h2 : ⟪e, p (i + 1)⟫ = ⟪e, p i⟫) : False := by
  have hD := (hp.cross2_edge_pos i).ne'
  set a := p i - p (i - 1)
  set b := p (i + 1) - p i
  have ha0 : ⟪e, a⟫ = 0 := by simp only [a, inner_sub_right]; linarith
  have hb0 : ⟪e, b⟫ = 0 := by simp only [b, inner_sub_right]; linarith
  apply he
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial] at ha0 hb0
  simp only [cross2] at hD
  have e0 : e 0 * (a 0 * b 1 - a 1 * b 0) = 0 := by
    linear_combination b 1 * ha0 - a 1 * hb0
  have e1 : e 1 * (a 0 * b 1 - a 1 * b 0) = 0 := by
    linear_combination -(b 0) * ha0 + a 0 * hb0
  have h0 := (mul_eq_zero.mp e0).resolve_right hD
  have h1 := (mul_eq_zero.mp e1).resolve_right hD
  ext l; fin_cases l <;> simp [h0, h1]

end IsCcwPolygon

end Minimality

end RupertMinimality
