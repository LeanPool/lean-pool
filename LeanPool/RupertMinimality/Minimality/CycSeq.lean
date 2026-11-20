/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Basic

/-! # Cyc Seq -/

@[expose] public section

namespace RupertMinimality

/-!
# Sequences for the force-polygon argument (Theorem 7.3, Steps 1–4)

The proof of Theorem 7.3 (⇒) (`hasHorizontalDoubleNormal_of_forces`,
`Unimodal.lean`) runs in five steps, cited here and in `Thm73.lean`:
1. the nonzero corner forces, in cyclic order, turn monotonically through one
   full turn, so their partial sums bound a convex *force polygon*;
2. summation by parts turns "zero depth moment" into a weighted balance of
   the partial sums;
3. unimodality of the depths fixes the signs of the weights (positive on the
   rising run, negative on the falling run);
4. hence the force polygon has empty interior: (i) generic case, (ii) the
   case where the two separating edges lie on one line;
5. so all forces are parallel, and parallel forces give a horizontal double
   normal.

Pure statements about finite real and planar sequences, indexed by `ℕ`
(only indices `< m` matter):
* `SSlin x m`: the sign pattern of `x` on `[0, m)` is a cyclic arc of `≥ 0`
  values and the complementary arc of `≤ 0` values (one sign switch each way).
* `sign_lemma`: the partial sums of such a sequence, measured from the
  midpoint of the first edge, have strict opposite signs on the two arcs
  between the midpoints of edges `0` and `T` (Step 4(i)).
* `abel_identity`: summation by parts (Step 2).
* `deg_lemma`: the degenerate case where the separating line contains an edge
  (Step 4(ii)).
* `forces_parallel`: Steps 2–4: forces with zero sum and zero depth moment,
  at depths rising from `0` to `T` and falling back, with the sign-switch
  properties of an angularly sorted sequence, are all parallel.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-- The 2D cross product `a × b = a₀ b₁ - a₁ b₀`. -/
def cross2 (a b : ℝ²) : ℝ := a 0 * b 1 - a 1 * b 0

theorem cross2_self (a : ℝ²) : cross2 a a = 0 := by simp [cross2]; ring

theorem cross2_add_right (a b c : ℝ²) : cross2 a (b + c) = cross2 a b + cross2 a c := by
  simp [cross2]; ring

theorem cross2_sub_right (a b c : ℝ²) : cross2 a (b - c) = cross2 a b - cross2 a c := by
  simp [cross2]; ring

theorem cross2_smul_right (a b : ℝ²) (r : ℝ) : cross2 a (r • b) = r * cross2 a b := by
  simp [cross2]; ring

theorem cross2_smul_left (a b : ℝ²) (r : ℝ) : cross2 (r • a) b = r * cross2 a b := by
  simp [cross2]; ring

theorem cross2_neg_right (a b : ℝ²) : cross2 a (-b) = -cross2 a b := by simp [cross2]; ring

theorem cross2_comm (a b : ℝ²) : cross2 a b = -cross2 b a := by simp [cross2]; ring

theorem cross2_sum_right {ι : Type*} (a : ℝ²) (s : Finset ι) (g : ι → ℝ²) :
    cross2 a (∑ i ∈ s, g i) = ∑ i ∈ s, cross2 a (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cross2]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, cross2_add_right, ih]

/-- Two vectors parallel to a nonzero one are parallel. -/
theorem cross2_trans {u v w : ℝ²} (hu : u ≠ 0) (hv : cross2 u v = 0) (hw : cross2 u w = 0) :
    cross2 v w = 0 := by
  have h0 : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
    by_contra h; push Not at h; apply hu; ext i; fin_cases i <;> simp [h.1, h.2]
  simp only [cross2] at hv hw ⊢
  rcases h0 with h | h
  · have : u 0 * (v 0 * w 1 - v 1 * w 0) = 0 := by linear_combination v 0 * hw - w 0 * hv
    exact (mul_eq_zero.mp this).resolve_left h
  · have : u 1 * (v 0 * w 1 - v 1 * w 0) = 0 := by linear_combination v 1 * hw - w 1 * hv
    exact (mul_eq_zero.mp this).resolve_left h

/-- The sign pattern of `x` on `[0, m)` consists of one arc of nonnegative and
one arc of nonpositive values (in linear form: an interval and its
complement). -/
def SSlin (x : ℕ → ℝ) (m : ℕ) : Prop :=
  ∃ i j, i ≤ j ∧ j ≤ m ∧
    (((∀ n, i ≤ n → n < j → 0 ≤ x n) ∧ (∀ n, n < m → (n < i ∨ j ≤ n) → x n ≤ 0)) ∨
     ((∀ n, i ≤ n → n < j → x n ≤ 0) ∧ (∀ n, n < m → (n < i ∨ j ≤ n) → 0 ≤ x n)))

theorem SSlin.neg {x : ℕ → ℝ} {m : ℕ} (h : SSlin x m) : SSlin (fun n => -x n) m := by
  obtain ⟨i, j, hij, hjm, h⟩ := h
  refine ⟨i, j, hij, hjm, ?_⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨fun n a b => by linarith [h1 n a b], fun n a b => by linarith [h2 n a b]⟩
  · exact Or.inl ⟨fun n a b => by linarith [h1 n a b], fun n a b => by linarith [h2 n a b]⟩

/-- Partial sums grow along a nonnegative stretch. -/
theorem psum_mono {x : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b) (h : ∀ r, a ≤ r → r < b → 0 ≤ x r) :
    ∑ r ∈ range a, x r ≤ ∑ r ∈ range b, x r := by
  rw [← sum_range_add_sum_Ico _ hab]
  have : 0 ≤ ∑ r ∈ Ico a b, x r := sum_nonneg fun r hr => by
    rw [mem_Ico] at hr; exact h r hr.1 hr.2
  linarith

theorem psum_anti {x : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b) (h : ∀ r, a ≤ r → r < b → x r ≤ 0) :
    ∑ r ∈ range b, x r ≤ ∑ r ∈ range a, x r := by
  rw [← sum_range_add_sum_Ico _ hab]
  have : ∑ r ∈ Ico a b, x r ≤ 0 := sum_nonpos fun r hr => by
    rw [mem_Ico] at hr; exact h r hr.1 hr.2
  linarith

/-- **Sign lemma (Step 4(i)).**  `Y n = Σ_{r<n} x r - x 0 / 2` measures the
partial sums from the midpoint of edge `0`.  If the midpoint of edge `T` is at
level `0` too, and neither edge is level, the vertices `1..T` and
`T+1..m` lie strictly on opposite sides. -/
theorem sign_lemma (x : ℕ → ℝ) (m T : ℕ) (hT0 : 0 < T) (hTm : T < m) (hSS : SSlin x m)
    (hsum : ∑ r ∈ range m, x r = 0)
    (hmid : (∑ r ∈ range T, x r - x 0 / 2) + x T / 2 = 0) (ha : x 0 ≠ 0) (hb : x T ≠ 0) :
    (∀ n, 1 ≤ n → n ≤ T → 0 < x 0 * (∑ r ∈ range n, x r - x 0 / 2)) ∧
      (∀ n, T < n → n ≤ m → x 0 * (∑ r ∈ range n, x r - x 0 / 2) < 0) := by
  -- reduce to `x 0 > 0`
  suffices key : ∀ x : ℕ → ℝ, SSlin x m → ∑ r ∈ range m, x r = 0 →
      (∑ r ∈ range T, x r - x 0 / 2) + x T / 2 = 0 → 0 < x 0 → x T ≠ 0 →
      (∀ n, 1 ≤ n → n ≤ T → 0 < ∑ r ∈ range n, x r - x 0 / 2) ∧
        (∀ n, T < n → n ≤ m → ∑ r ∈ range n, x r - x 0 / 2 < 0) by
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · have h := key (fun n => -x n) hSS.neg (by simp [sum_neg_distrib, hsum])
        (by simp only [sum_neg_distrib]; linarith) (by linarith) (by simpa using hb)
      simp only [sum_neg_distrib] at h
      refine ⟨fun n h1 h2 => ?_, fun n h1 h2 => ?_⟩
      · have := h.1 n h1 h2; nlinarith
      · have := h.2 n h1 h2; nlinarith
    · have h := key x hSS hsum hmid hpos hb
      exact ⟨fun n h1 h2 => mul_pos hpos (h.1 n h1 h2), fun n h1 h2 =>
        mul_neg_of_pos_of_neg hpos (h.2 n h1 h2)⟩
  intro x hSS hsum hmid ha hb
  set Y : ℕ → ℝ := fun n => ∑ r ∈ range n, x r - x 0 / 2 with hY
  have hY1 : Y 1 = x 0 / 2 := by simp [hY]; ring
  have hYm : Y m = -(x 0 / 2) := by simp [hY, hsum]
  have hYT : Y T = -(x T / 2) := by simp only [hY]; linarith
  have hYT1 : Y (T + 1) = x T / 2 := by
    simp only [hY, sum_range_succ]; simp only [hY] at hYT; linarith
  have mono : ∀ a b, a ≤ b → (∀ r, a ≤ r → r < b → 0 ≤ x r) → Y a ≤ Y b := fun a b hab h => by
    simp only [hY]; linarith [psum_mono hab h]
  have anti : ∀ a b, a ≤ b → (∀ r, a ≤ r → r < b → x r ≤ 0) → Y b ≤ Y a := fun a b hab h => by
    simp only [hY]; linarith [psum_anti hab h]
  obtain ⟨i, j, hij, hjm, hcase⟩ := hSS
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- nonnegative on `[i, j)`, nonpositive outside
    have hi : i = 0 := by
      by_contra hi0
      have := h2 0 (by omega) (Or.inl (by omega)); linarith
    subst hi
    have hTj : j ≤ T := by
      by_contra hTj; push Not at hTj
      have hxT : 0 < x T := lt_of_le_of_ne (h1 T (by omega) hTj) (Ne.symm hb)
      have := mono 1 T hT0 (fun r hr1 hr2 => h1 r (by omega) (by omega))
      linarith
    have hxT : x T < 0 := lt_of_le_of_ne (h2 T hTm (Or.inr hTj)) hb
    refine ⟨fun n hn1 hnT => ?_, fun n hn1 hnm => ?_⟩
    · rcases le_total n j with hnj | hnj
      · have := mono 1 n hn1 (fun r hr1 hr2 => h1 r (by omega) (by omega)); linarith
      · have := anti n T hnT (fun r hr1 hr2 => h2 r (by omega) (Or.inr (by omega))); linarith
    · have := anti (T + 1) n hn1 (fun r hr1 hr2 => h2 r (by omega) (Or.inr (by omega)))
      linarith
  · -- nonpositive on `[i, j)`, nonnegative outside
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · -- everything nonnegative: impossible
      have : 0 < ∑ r ∈ range m, x r := by
        rw [← sum_range_add_sum_Ico _ (show 1 ≤ m by omega)]
        have hpos : 0 < ∑ r ∈ range 1, x r := by simpa using ha
        have : 0 ≤ ∑ r ∈ Ico 1 m, x r := sum_nonneg fun r hr => by
          rw [mem_Ico] at hr; exact h2 r hr.2 (Or.inr (by omega))
        linarith
      linarith
    have hi : 1 ≤ i := by
      by_contra hi0
      have := h1 0 (by omega) hj0; linarith
    by_cases hTin : i ≤ T ∧ T < j
    · have hxT : x T < 0 := lt_of_le_of_ne (h1 T hTin.1 hTin.2) hb
      refine ⟨fun n hn1 hnT => ?_, fun n hn1 hnm => ?_⟩
      · rcases le_total n i with hni | hni
        · have := mono 1 n hn1 (fun r hr1 hr2 => h2 r (by omega) (Or.inl (by omega)))
          linarith
        · have := anti n T hnT (fun r hr1 hr2 => h1 r (by omega) (by omega)); linarith
      · rcases le_total n j with hnj | hnj
        · have := anti (T + 1) n hn1 (fun r hr1 hr2 => h1 r (by omega) (by omega)); linarith
        · have := mono n m hnm (fun r hr1 hr2 => h2 r hr2 (Or.inr (by omega))); linarith
    · exfalso
      have hxT : 0 < x T := by
        have : 0 ≤ x T := h2 T hTm (by omega)
        exact lt_of_le_of_ne this (Ne.symm hb)
      -- some negative value after `T`
      have hneg : ∃ r, T < r ∧ r < m ∧ x r < 0 := by
        by_contra hcon; push Not at hcon
        have := mono (T + 1) m (by omega) (fun r hr1 hr2 => hcon r (by omega) hr2)
        linarith
      obtain ⟨r, hr1, hr2, hr3⟩ := hneg
      have hrin : i ≤ r ∧ r < j := by
        by_contra h; have := h2 r hr2 (by omega); linarith
      have hTi : T < i := by omega
      have := mono 1 T hT0 (fun r hr1 hr2 => h2 r (by omega) (Or.inl (by omega)))
      linarith

/-- **Summation by parts (Step 2).**  With partial sums `V n = Σ_{s<n} g s`,
`Σ g = 0`, `Σ ζ g = 0`, and the cyclic depth increments
`w n = ζ n - ζ (n-1)` (`ζ m := ζ 0`), the weighted sum of the levels
`cross2 D (V n - P)` vanishes. -/
theorem abel_identity (g : ℕ → ℝ²) (ζ : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (h1 : ∑ s ∈ range m, g s = 0) (h2 : ∑ s ∈ range m, ζ s • g s = 0) (D P : ℝ²) :
    ∑ n ∈ Ico 1 (m + 1), ((if n = m then ζ 0 else ζ n) - ζ (n - 1)) *
      cross2 D (∑ s ∈ range n, g s - P) = 0 := by
  set Ψ : ℕ → ℝ := fun n => cross2 D (∑ s ∈ range n, g s - P) with hΨ
  have hstep : ∀ n, Ψ (n + 1) = Ψ n + cross2 D (g n) := fun n => by
    simp only [hΨ, sum_range_succ, show ∀ a b c : ℝ², a + b - c = (a - c) + b from
      fun a b c => by abel, cross2_add_right]
  have hm' : Ψ m = Ψ 0 := by simp [hΨ, h1]
  have hx : ∑ s ∈ range m, ζ s * cross2 D (g s) = 0 := by
    have := congrArg (cross2 D) h2
    rw [cross2_sum_right] at this
    simp only [cross2_smul_right] at this
    rwa [show cross2 D 0 = 0 by simp [cross2]] at this
  rw [sum_Ico_eq_sum_range, show m + 1 - 1 = m by omega]
  simp only [add_comm 1, Nat.add_sub_cancel]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have e1 : ∑ s ∈ range (m' + 1), ((if s + 1 = m' + 1 then ζ 0 else ζ (s + 1)) - ζ s) * Ψ (s + 1)
      = ∑ s ∈ range (m' + 1), (if s + 1 = m' + 1 then ζ 0 else ζ (s + 1)) * Ψ (s + 1) -
        ∑ s ∈ range (m' + 1), ζ s * Ψ (s + 1) := by
    rw [← sum_sub_distrib]; exact sum_congr rfl fun s _ => by ring
  rw [e1]
  have e2 : ∑ s ∈ range (m' + 1), ζ s * Ψ (s + 1) = ∑ s ∈ range (m' + 1), ζ s * Ψ s := by
    have : ∑ s ∈ range (m' + 1), ζ s * Ψ (s + 1) =
        ∑ s ∈ range (m' + 1), ζ s * Ψ s + ∑ s ∈ range (m' + 1), ζ s * cross2 D (g s) := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun s _ => by rw [hstep]; ring
    rw [this, hx, add_zero]
  have e3 : ∑ s ∈ range (m' + 1), (if s + 1 = m' + 1 then ζ 0 else ζ (s + 1)) * Ψ (s + 1) =
      ∑ s ∈ range (m' + 1), ζ s * Ψ s := by
    rw [sum_range_succ, sum_range_succ']
    rw [ite_eq_left rfl, hm']
    congr 1
    exact sum_congr rfl fun s hs => by
      rw [ite_eq_right (by rw [mem_range] at hs; omega)]
  rw [e2, e3, sub_self]

/-- Rotating the index of a sum over `range m`. -/
theorem sum_range_rotate {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m T : ℕ) (hT : T < m) :
    ∑ s ∈ range m, f ((T + s) % m) = ∑ s ∈ range m, f s := by
  rw [← sum_range_add_sum_Ico _ (show m - T ≤ m by omega)]
  have e1 : ∑ s ∈ range (m - T), f ((T + s) % m) = ∑ r ∈ Ico T m, f r := by
    rw [sum_Ico_eq_sum_range]
    exact sum_congr rfl fun s hs => by
      rw [mem_range] at hs; rw [Nat.mod_eq_of_lt (by omega)]
  have e2 : ∑ s ∈ Ico (m - T) m, f ((T + s) % m) = ∑ r ∈ range T, f r := by
    rw [sum_Ico_eq_sum_range, show m - (m - T) = T by omega]
    exact sum_congr rfl fun s hs => by
      rw [mem_range] at hs
      congr 1
      rw [show T + (m - T + s) = s + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2, add_comm, sum_range_add_sum_Ico _ hT.le]

/-- **Step 4(ii), the degenerate case.**  If the line of the first force
edge also passes through the midpoint of edge `T`, then (the line being a
supporting line of the force polygon, and the depth weights having opposite
strict signs on the two arcs) every force is parallel to the first. -/
theorem deg_lemma (g : ℕ → ℝ²) (m T : ℕ) (hT0 : 0 < T) (hTm : T < m)
    (h1 : ∑ s ∈ range m, g s = 0) (w : ℕ → ℝ)
    (hw : ((∀ n, 1 ≤ n → n ≤ T → 0 ≤ w n) ∧ (∀ n, T < n → n ≤ m → w n ≤ 0)) ∨
      ((∀ n, 1 ≤ n → n ≤ T → w n ≤ 0) ∧ (∀ n, T < n → n ≤ m → 0 ≤ w n)))
    (hwne : ∀ n, 1 ≤ n → n < m → g n ≠ 0 → w n ≠ 0)
    (hOr : ∃ j, j ≤ m ∧ (∀ s, 0 < s → s < j → 0 ≤ cross2 (g 0) (g s)) ∧
      (∀ s, j ≤ s → s < m → cross2 (g 0) (g s) ≤ 0))
    (hAbel : ∑ n ∈ Ico 1 (m + 1), w n *
      cross2 (g 0) (∑ s ∈ range n, g s - (1 / 2 : ℝ) • g 0) = 0)
    (hmid : cross2 (g 0) (∑ s ∈ range T, g s + (1 / 2 : ℝ) • g T - (1 / 2 : ℝ) • g 0) = 0) :
    ∀ s < m, cross2 (g 0) (g s) = 0 := by
  set y : ℕ → ℝ := fun s => cross2 (g 0) (g s) with hy
  have hy0 : y 0 = 0 := cross2_self _
  set Ψ : ℕ → ℝ := fun n => ∑ s ∈ range n, y s with hΨ
  have hΨeq : ∀ n, cross2 (g 0) (∑ s ∈ range n, g s - (1 / 2 : ℝ) • g 0) = Ψ n := fun n => by
    rw [cross2_sub_right, cross2_sum_right, cross2_smul_right, cross2_self]; simp [hΨ, hy]
  simp only [hΨeq] at hAbel
  have hΨ1 : Ψ 1 = 0 := by simp [hΨ, hy0]
  have hΨm : Ψ m = 0 := by
    have := congrArg (cross2 (g 0)) h1
    rw [cross2_sum_right] at this
    simpa [hΨ, hy, cross2] using this
  have hmid' : Ψ T + y T / 2 = 0 := by
    rw [cross2_sub_right, cross2_add_right, cross2_sum_right, cross2_smul_right,
      cross2_smul_right, cross2_self] at hmid
    simp only [hΨ, hy]; linarith
  have hΨT1 : Ψ (T + 1) = Ψ T + y T := by simp [hΨ, sum_range_succ]
  obtain ⟨j, hjm, hjpos, hjneg⟩ := hOr
  have hnonneg : ∀ n, 1 ≤ n → n ≤ m → 0 ≤ Ψ n := by
    intro n hn1 hnm
    rcases le_total n j with hnj | hnj
    · have := psum_mono hn1 (fun r hr1 hr2 => hjpos r (by omega) (by omega))
      simp only [hΨ] at hΨ1 ⊢; linarith
    · have := psum_anti hnm (fun r hr1 hr2 => hjneg r (by omega) hr2)
      simp only [hΨ] at hΨm ⊢; linarith
  have hT0' := hnonneg T hT0 hTm.le
  have hT1' := hnonneg (T + 1) (by omega) (by omega)
  have hΨT : Ψ T = 0 := by linarith
  have hΨT1' : Ψ (T + 1) = 0 := by linarith
  -- one of the two arcs is on the line
  have hzero_part : (∀ n, 1 ≤ n → n ≤ T → Ψ n = 0) ∨ (∀ n, T < n → n ≤ m → Ψ n = 0) := by
    rcases le_total T j with hTj | hTj
    · left
      intro n hn1 hnT
      have := psum_mono hnT (fun r hr1 hr2 => hjpos r (by omega) (by omega))
      simp only [hΨ] at hΨT ⊢
      linarith [hnonneg n hn1 (by omega)]
    · right
      intro n hn1 hnm
      have := psum_anti hn1 (fun r hr1 hr2 => hjneg r (by omega) (by omega))
      simp only [hΨ] at hΨT1' ⊢
      linarith [hnonneg n (by omega) hnm]
  -- the depth balance forces the supported points of the other arc onto the line
  have hsplit : ∑ n ∈ Ico 1 (m + 1), w n * Ψ n =
      ∑ n ∈ Ico 1 (T + 1), w n * Ψ n + ∑ n ∈ Ico (T + 1) (m + 1), w n * Ψ n :=
    (sum_Ico_consecutive _ (by omega) (by omega)).symm
  have hsupp : ∀ n, 1 ≤ n → n < m → g n ≠ 0 → Ψ n = 0 := by
    rcases hzero_part with hz | hz
    · have hfirst : ∑ n ∈ Ico 1 (T + 1), w n * Ψ n = 0 :=
        sum_eq_zero fun n hn => by rw [mem_Ico] at hn; rw [hz n hn.1 (by omega), mul_zero]
      rw [hsplit, hfirst, zero_add] at hAbel
      intro n hn1 hnm hgn
      by_cases hnT : n ≤ T
      · exact hz n hn1 hnT
      have hn : n ∈ Ico (T + 1) (m + 1) := mem_Ico.mpr ⟨by omega, by omega⟩
      have hterm : w n * Ψ n = 0 := by
        rcases hw with ⟨_, hw2⟩ | ⟨_, hw2⟩
        · exact (sum_eq_zero_iff_of_nonpos fun r hr => by
            rw [mem_Ico] at hr
            exact mul_nonpos_of_nonpos_of_nonneg (hw2 r (by omega) (by omega))
              (hnonneg r (by omega) (by omega))).mp hAbel n hn
        · exact (sum_eq_zero_iff_of_nonneg fun r hr => by
            rw [mem_Ico] at hr
            exact mul_nonneg (hw2 r (by omega) (by omega))
              (hnonneg r (by omega) (by omega))).mp hAbel n hn
      exact (mul_eq_zero.mp hterm).resolve_left (hwne n hn1 hnm hgn)
    · have hsecond : ∑ n ∈ Ico (T + 1) (m + 1), w n * Ψ n = 0 :=
        sum_eq_zero fun n hn => by rw [mem_Ico] at hn; rw [hz n (by omega) (by omega), mul_zero]
      rw [hsplit, hsecond, add_zero] at hAbel
      intro n hn1 hnm hgn
      by_cases hnT : T < n
      · exact hz n hnT hnm.le
      have hn : n ∈ Ico 1 (T + 1) := mem_Ico.mpr ⟨hn1, by omega⟩
      have hterm : w n * Ψ n = 0 := by
        rcases hw with ⟨hw1, _⟩ | ⟨hw1, _⟩
        · exact (sum_eq_zero_iff_of_nonneg fun r hr => by
            rw [mem_Ico] at hr
            exact mul_nonneg (hw1 r hr.1 (by omega)) (hnonneg r hr.1 (by omega))).mp hAbel n hn
        · exact (sum_eq_zero_iff_of_nonpos fun r hr => by
            rw [mem_Ico] at hr
            exact mul_nonpos_of_nonpos_of_nonneg (hw1 r hr.1 (by omega))
              (hnonneg r hr.1 (by omega))).mp hAbel n hn
      exact (mul_eq_zero.mp hterm).resolve_left (hwne n hn1 hnm hgn)
  -- `Ψ` is constant across forces equal to zero
  have hstretch : ∀ a b, a ≤ b → (∀ r, a ≤ r → r < b → g r = 0) → Ψ b = Ψ a := by
    intro a b hab h
    have h1' := psum_mono hab (x := y) (fun r h1 h2 => by simp [hy, h r h1 h2, cross2])
    have h2' := psum_anti hab (x := y) (fun r h1 h2 => by simp [hy, h r h1 h2, cross2])
    simp only [hΨ]; linarith
  intro s hs
  by_cases hgs : g s = 0
  · change y s = 0
    simp [hy, hgs, cross2]
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · exact hy0
  have hΨs : Ψ s = 0 := hsupp s hs0 hs hgs
  have hΨs1 : Ψ (s + 1) = 0 := by
    have hex : ∃ j, s + 1 ≤ j ∧ (j = m ∨ (j < m ∧ g j ≠ 0)) := ⟨m, by omega, Or.inl rfl⟩
    set s' := Nat.find hex with hs'
    obtain ⟨hs'1, hs'2⟩ := Nat.find_spec hex
    have hle : s' ≤ m := Nat.find_min' hex ⟨by omega, Or.inl rfl⟩
    have hconst : Ψ s' = Ψ (s + 1) := hstretch (s + 1) s' hs'1 (fun r hr1 hr2 => by
      by_contra hgr
      have := Nat.find_min hex hr2
      exact this ⟨hr1, Or.inr ⟨by omega, hgr⟩⟩)
    rw [← hconst]
    rcases hs'2 with h | ⟨h1', h2'⟩
    · have : s' = m := h
      rw [this]; exact hΨm
    · exact hsupp s' (by omega) h1' h2'
  have : Ψ (s + 1) = Ψ s + y s := by simp [hΨ, sum_range_succ]
  change y s = 0
  linarith

/-- Rotate the force at the top depth to the front when it lies on the separating line. -/
private theorem forces_parallel_of_top_aligned (g : ℕ → ℝ²) (ζf : ℕ → ℝ)
    (m T : ℕ) (hT0 : 0 < T) (hTm : T < m) (hgT : g T ≠ 0)
    (h1 : ∑ s ∈ range m, g s = 0) (h2f : ∑ s ∈ range m, ζf s • g s = 0)
    {w : ℕ → ℝ} (hw : w = fun n => (if n = m then ζf 0 else ζf n) - ζf (n - 1))
    (hw1 : ∀ n, 1 ≤ n → n ≤ T → 0 ≤ w n)
    (hw2 : ∀ n, T < n → n ≤ m → w n ≤ 0) (hwm : w m < 0)
    (hwne : ∀ n, 1 ≤ n → n < m → g n ≠ 0 → w n ≠ 0)
    (hOrT : ∃ j, j ≤ m ∧ (∀ s, 0 < s → s < j → 0 ≤ cross2 (g T) (g ((T + s) % m))) ∧
      (∀ s, j ≤ s → s < m → cross2 (g T) (g ((T + s) % m)) ≤ 0))
    (hb : cross2 ((∑ s ∈ range T, g s) + (1 / 2 : ℝ) • g T - (1 / 2 : ℝ) • g 0)
      (g T) = 0) :
    ∀ s < m, cross2 (g 0) (g s) = 0 := by
  have hm : 0 < m := by omega
  set V : ℕ → ℝ² := fun n => ∑ s ∈ range n, g s with hV
  set D := V T + (1 / 2 : ℝ) • g T - (1 / 2 : ℝ) • g 0 with hD
  change cross2 D (g T) = 0 at hb
  set g' : ℕ → ℝ² := fun s => g ((T + s) % m) with hg'
  set ζ' : ℕ → ℝ := fun s => ζf ((T + s) % m) with hζ'
  have hg'0 : g' 0 = g T := by simp [hg', Nat.mod_eq_of_lt hTm]
  have hg'T : g' (m - T) = g 0 := by simp [hg', show T + (m - T) = m by omega]
  have h1' : ∑ s ∈ range m, g' s = 0 := by rw [sum_range_rotate g m T hTm]; exact h1
  have h2' : ∑ s ∈ range m, ζ' s • g' s = 0 := by
    rw [sum_range_rotate (fun r => ζf r • g r) m T hTm]; exact h2f
  have hV' : ∑ s ∈ range (m - T), g' s = -V T := by
    have e : ∑ s ∈ range (m - T), g' s = ∑ r ∈ Ico T m, g r := by
      rw [sum_Ico_eq_sum_range]
      exact sum_congr rfl fun s hs => by
        rw [mem_range] at hs; simp [hg', Nat.mod_eq_of_lt (show T + s < m by omega)]
    rw [e]
    have := sum_range_add_sum_Ico g hTm.le
    rw [h1] at this
    simp only [hV]
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact this
  set w' : ℕ → ℝ := fun n => (if n = m then ζ' 0 else ζ' n) - ζ' (n - 1) with hw'
  -- the rotated weights are the weights at the rotated index
  have hw'eq : ∀ n, 1 ≤ n → n ≤ m →
      w' n = w (if T + n < m then T + n else if T + n = m then m else T + n - m) := by
    intro n h1 h2
    rcases eq_or_lt_of_le h2 with h2 | h2
    · have e1 : T % m = T := Nat.mod_eq_of_lt hTm
      have e2 : (T + (n - 1)) % m = T - 1 := by
        rw [show T + (n - 1) = (T - 1) + m by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      have e3 : (if T + n < m then T + n else if T + n = m then m else T + n - m) = T := by
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega
      rw [e3]
      simp only [hw', hζ', hw]
      rw [ite_eq_left h2, ite_eq_right (by omega), Nat.add_zero, e1, e2]
    · by_cases hlt : T + n < m
      · have e1 : (T + n) % m = T + n := Nat.mod_eq_of_lt hlt
        have e2 : (T + (n - 1)) % m = T + n - 1 := by
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        simp only [hw', hζ', hw]
        rw [ite_eq_right (by omega), ite_eq_left hlt, ite_eq_right (by omega), e1, e2]
      · by_cases heq : T + n = m
        · have e1 : (T + n) % m = 0 := by rw [heq, Nat.mod_self]
          have e2 : (T + (n - 1)) % m = m - 1 := by
            rw [Nat.mod_eq_of_lt (by omega)]; omega
          simp only [hw', hζ', hw]
          rw [ite_eq_right (by omega), ite_eq_right hlt, ite_eq_left heq, ite_eq_left rfl, e1, e2]
        · have e1 : (T + n) % m = T + n - m := by
            rw [show T + n = (T + n - m) + m by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega)]; omega
          have e2 : (T + (n - 1)) % m = T + n - m - 1 := by
            rw [show T + (n - 1) = (T + n - m - 1) + m by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega)]
          simp only [hw', hζ', hw]
          rw [ite_eq_right (by omega), ite_eq_right hlt, ite_eq_right heq,
            ite_eq_right (by omega), e1, e2]
  have hwr1 : ∀ n, 1 ≤ n → n ≤ m - T → w' n ≤ 0 := by
    intro n h1 h2
    rw [hw'eq n h1 (by omega)]
    split_ifs with ha hb'
    · exact hw2 _ (by omega) (by omega)
    · exact hwm.le
    · omega
  have hwr2 : ∀ n, m - T < n → n ≤ m → 0 ≤ w' n := by
    intro n h1 h2
    rw [hw'eq n (by omega) h2]
    split_ifs with ha hb'
    · omega
    · omega
    · exact hw1 _ (by omega) (by omega)
  have hwr_ne : ∀ n, 1 ≤ n → n < m → g' n ≠ 0 → w' n ≠ 0 := by
    intro n h1 h2 hgn
    rw [hw'eq n h1 h2.le]
    split_ifs with ha hb'
    · refine hwne _ (by omega) ha ?_
      simpa [hg', Nat.mod_eq_of_lt ha] using hgn
    · exact hwm.ne
    · refine hwne _ (by omega) (by omega) ?_
      have : (T + n) % m = T + n - m := by
        rw [show T + n = (T + n - m) + m by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]; omega
      simpa [hg', this] using hgn
  have hdeg := deg_lemma g' m (m - T) (by omega) (by omega) h1' w'
    (Or.inr ⟨hwr1, hwr2⟩) hwr_ne (by simpa [hg'0] using hOrT)
    (abel_identity g' ζ' m hm h1' h2' (g' 0) ((1 / 2 : ℝ) • g' 0))
    (by
      rw [hV', hg'T, hg'0]
      have : -V T + (1 / 2 : ℝ) • g 0 - (1 / 2 : ℝ) • g T = -D := by
        simp only [hD]; abel
      rw [this, cross2_neg_right, cross2_comm, neg_neg]
      simpa using hb)
  have hall : ∀ r < m, cross2 (g T) (g r) = 0 := by
    intro r hr
    have := hdeg ((r + (m - T)) % m) (Nat.mod_lt _ hm)
    rw [hg'0] at this
    simp only [hg'] at this
    rwa [Nat.add_mod_mod, show T + (r + (m - T)) = r + m by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hr] at this
  intro r hr
  exact cross2_trans hgT (hall 0 hm) (hall r hr)

/-- **Theorem 7.3, Steps 2–4.**  Forces `g 0, …, g (m-1)` (the corner forces in
cyclic order, starting at the deepest corner `0` carrying a force; forces may
vanish) with zero sum and zero depth moment, whose depths along the nonzero
forces rise strictly from `0` to `T` and fall strictly back, and whose
directions have the sign-switch properties of an angularly sorted sequence
(`hSS`, and the orientation at the extreme forces `hOr0`, `hOrT`), are all
parallel. -/
theorem forces_parallel (g : ℕ → ℝ²) (ζ : ℕ → ℝ) (m T : ℕ) (hT0 : 0 < T) (hTm : T < m)
    (hg0 : g 0 ≠ 0) (hgT : g T ≠ 0)
    (h1 : ∑ s ∈ range m, g s = 0) (h2 : ∑ s ∈ range m, ζ s • g s = 0)
    (hrise : ∀ a b, a < b → b ≤ T → g a ≠ 0 → g b ≠ 0 → ζ a < ζ b)
    (hfall : ∀ a b, T ≤ a → a < b → b < m → g a ≠ 0 → g b ≠ 0 → ζ b < ζ a)
    (hbot : ∀ a, 0 < a → a < m → g a ≠ 0 → ζ 0 < ζ a)
    (hSS : ∀ D, SSlin (fun s => cross2 D (g s)) m)
    (hOr0 : ∃ j, j ≤ m ∧ (∀ s, 0 < s → s < j → 0 ≤ cross2 (g 0) (g s)) ∧
      (∀ s, j ≤ s → s < m → cross2 (g 0) (g s) ≤ 0))
    (hOrT : ∃ j, j ≤ m ∧ (∀ s, 0 < s → s < j → 0 ≤ cross2 (g T) (g ((T + s) % m))) ∧
      (∀ s, j ≤ s → s < m → cross2 (g T) (g ((T + s) % m)) ≤ 0)) :
    ∀ s < m, cross2 (g 0) (g s) = 0 := by
  classical
  have hm : 0 < m := by omega
  -- fill the depths at force-free corners by the last forced depth
  set P : ℕ → Prop := fun j => g j ≠ 0 with hP
  set ζf : ℕ → ℝ := fun n => ζ (Nat.findGreatest P n) with hζf
  have hfg_self : ∀ n, g n ≠ 0 → Nat.findGreatest P n = n := fun n h => Nat.findGreatest_eq h
  have hfg_spec : ∀ n, g (Nat.findGreatest P n) ≠ 0 := fun n =>
    Nat.findGreatest_spec (P := P) (Nat.zero_le n) hg0
  have hfg_le : ∀ n, Nat.findGreatest P n ≤ n := fun n => Nat.findGreatest_le n
  have hfg_ge : ∀ n j, j ≤ n → g j ≠ 0 → j ≤ Nat.findGreatest P n := fun n j hj hg =>
    Nat.le_findGreatest hj hg
  have hfg_step : ∀ n, g (n + 1) = 0 → Nat.findGreatest P (n + 1) = Nat.findGreatest P n :=
    fun n h => Nat.findGreatest_of_not (by simpa [hP] using h)
  have h2f : ∑ s ∈ range m, ζf s • g s = 0 := by
    rw [← h2]
    exact sum_congr rfl fun s _ => by
      by_cases hgs : g s = 0
      · simp [hgs]
      · simp only [hζf, hfg_self s hgs]
  set w : ℕ → ℝ := fun n => (if n = m then ζf 0 else ζf n) - ζf (n - 1) with hw
  -- the weights: `≥ 0` before `T`, `≤ 0` after, nonzero at forced corners
  have hwval : ∀ n, 1 ≤ n → n < m → w n = ζf n - ζf (n - 1) := fun n h1 h2 => by
    simp only [hw, ite_eq_right (show n ≠ m by omega)]
  have hw_zero : ∀ n, 1 ≤ n → n < m → g n = 0 → w n = 0 := fun n h1 h2 hg => by
    rw [hwval n h1 h2]
    simp only [hζf]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [hfg_step n' hg, show n' + 1 - 1 = n' by omega, sub_self]
  have hw_supp : ∀ n, 1 ≤ n → n < m → g n ≠ 0 →
      w n = ζ n - ζ (Nat.findGreatest P (n - 1)) := fun n h1 h2 hg => by
    rw [hwval n h1 h2]; simp only [hζf, hfg_self n hg]
  have hw1 : ∀ n, 1 ≤ n → n ≤ T → 0 ≤ w n := by
    intro n h1 h2
    by_cases hg : g n = 0
    · rw [hw_zero n h1 (by omega) hg]
    · rw [hw_supp n h1 (by omega) hg]
      have := hrise (Nat.findGreatest P (n - 1)) n (by have := hfg_le (n - 1); omega) h2
        (hfg_spec _) hg
      linarith
  have hwT : 0 < w T := by
    rw [hw_supp T hT0 hTm hgT]
    have := hrise (Nat.findGreatest P (T - 1)) T (by have := hfg_le (T - 1); omega) le_rfl
      (hfg_spec _) hgT
    linarith
  have hwm : w m < 0 := by
    have e0 : Nat.findGreatest P 0 = 0 := Nat.findGreatest_eq hg0
    have : w m = ζ 0 - ζ (Nat.findGreatest P (m - 1)) := by
      change (if m = m then ζf 0 else ζf m) - ζf (m - 1) = _
      rw [ite_eq_left rfl]
      simp only [hζf, e0]
    rw [this]
    have hge := hfg_ge (m - 1) T (by omega) hgT
    have := hbot (Nat.findGreatest P (m - 1)) (by omega) (by have := hfg_le (m - 1); omega)
      (hfg_spec _)
    linarith
  have hw2 : ∀ n, T < n → n ≤ m → w n ≤ 0 := by
    intro n h1 h2
    rcases eq_or_lt_of_le h2 with h2 | h2
    · rw [h2]; exact hwm.le
    · by_cases hg : g n = 0
      · rw [hw_zero n (by omega) h2 hg]
      · rw [hw_supp n (by omega) h2 hg]
        have hge := hfg_ge (n - 1) T (by omega) hgT
        have := hfall (Nat.findGreatest P (n - 1)) n hge (by have := hfg_le (n - 1); omega) h2
          (hfg_spec _) hg
        linarith
  have hwne : ∀ n, 1 ≤ n → n < m → g n ≠ 0 → w n ≠ 0 := by
    intro n h1 h2 hg
    rw [hw_supp n h1 h2 hg]
    have hq := hfg_le (n - 1)
    by_cases hnT : n ≤ T
    · have := hrise (Nat.findGreatest P (n - 1)) n (by omega) hnT (hfg_spec _) hg; linarith
    · have hge := hfg_ge (n - 1) T (by omega) hgT
      have := hfall (Nat.findGreatest P (n - 1)) n hge (by omega) h2 (hfg_spec _) hg; linarith
  set V : ℕ → ℝ² := fun n => ∑ s ∈ range n, g s with hV
  set D := V T + (1 / 2 : ℝ) • g T - (1 / 2 : ℝ) • g 0 with hD
  by_cases ha : cross2 D (g 0) = 0
  · -- the separating line contains force edge `0`
    refine deg_lemma g m T hT0 hTm h1 w (Or.inl ⟨hw1, hw2⟩) hwne hOr0 ?_ ?_
    · exact abel_identity g ζf m hm h1 h2f (g 0) ((1 / 2 : ℝ) • g 0)
    · rw [cross2_comm]; simpa [hD, hV] using ha
  by_cases hb : cross2 D (g T) = 0
  · -- the separating line contains force edge `T`: rotate `T` to the front
    exact forces_parallel_of_top_aligned g ζf m T hT0 hTm hgT h1 h2f
      hw hw1 hw2 hwm hwne hOrT hb
  -- generic case: strict separation, contradicting the depth balance
  exfalso
  set x : ℕ → ℝ := fun s => cross2 D (g s) with hx
  have hsum : ∑ r ∈ range m, x r = 0 := by
    have := congrArg (cross2 D) h1
    rw [cross2_sum_right] at this
    simpa [hx, cross2] using this
  have hY : ∀ n, cross2 D (∑ s ∈ range n, g s - (1 / 2 : ℝ) • g 0) =
      ∑ r ∈ range n, x r - x 0 / 2 := by
    intro n
    rw [cross2_sub_right, cross2_sum_right, cross2_smul_right]
    simp only [hx]
    ring
  have hmid : (∑ r ∈ range T, x r - x 0 / 2) + x T / 2 = 0 := by
    rw [← hY]
    have e : (∑ s ∈ range T, g s - (1 / 2 : ℝ) • g 0) + (1 / 2 : ℝ) • g T = D := by
      simp only [hD, hV]; abel
    have : cross2 D (∑ s ∈ range T, g s - (1 / 2 : ℝ) • g 0) + x T / 2 = cross2 D D := by
      calc cross2 D (∑ s ∈ range T, g s - (1 / 2 : ℝ) • g 0) + x T / 2
          = cross2 D ((∑ s ∈ range T, g s - (1 / 2 : ℝ) • g 0) + (1 / 2 : ℝ) • g T) := by
            rw [cross2_add_right, cross2_smul_right]; simp only [hx]; ring
        _ = cross2 D D := by rw [e]
    rw [this, cross2_self]
  obtain ⟨hpos, hneg⟩ := sign_lemma x m T hT0 hTm (hSS D) hsum hmid ha hb
  have habel := abel_identity g ζf m hm h1 h2f D ((1 / 2 : ℝ) • g 0)
  simp only [hY] at habel
  have : 0 < ∑ n ∈ Ico 1 (m + 1), w n * (x 0 * (∑ r ∈ range n, x r - x 0 / 2)) := by
    rw [← sum_Ico_consecutive _ (show 1 ≤ T + 1 by omega) (show T + 1 ≤ m + 1 by omega)]
    have hA : 0 < ∑ n ∈ Ico 1 (T + 1), w n * (x 0 * (∑ r ∈ range n, x r - x 0 / 2)) := by
      rw [← add_sum_erase _ _ (mem_Ico.mpr ⟨hT0, by omega⟩ : T ∈ Ico 1 (T + 1))]
      have hTterm := mul_pos hwT (hpos T hT0 le_rfl)
      have hrest : 0 ≤ ∑ n ∈ (Ico 1 (T + 1)).erase T,
          w n * (x 0 * (∑ r ∈ range n, x r - x 0 / 2)) := sum_nonneg fun n hn => by
        have hn' := mem_Ico.mp (mem_of_mem_erase hn)
        exact mul_nonneg (hw1 n hn'.1 (by omega)) (hpos n hn'.1 (by omega)).le
      linarith
    have hB : 0 ≤ ∑ n ∈ Ico (T + 1) (m + 1), w n * (x 0 * (∑ r ∈ range n, x r - x 0 / 2)) :=
      sum_nonneg fun n hn => by
        rw [mem_Ico] at hn
        exact mul_nonneg_of_nonpos_of_nonpos (hw2 n (by omega) (by omega))
          (hneg n (by omega) (by omega)).le
    linarith
  have hzero : ∑ n ∈ Ico 1 (m + 1), w n * (x 0 * (∑ r ∈ range n, x r - x 0 / 2)) = 0 := by
    have : ∑ n ∈ Ico 1 (m + 1), w n * (x 0 * (∑ r ∈ range n, x r - x 0 / 2)) =
        x 0 * ∑ n ∈ Ico 1 (m + 1), w n * (∑ r ∈ range n, x r - x 0 / 2) := by
      rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
    rw [this, habel, mul_zero]
  linarith

end Minimality

end RupertMinimality
