/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import LeanPool.RupertMinimality.Minimality.Polygon

/-! # Thm73 -/

@[expose] public section

namespace RupertMinimality

/-!
# Theorem 7.3: from forces to a horizontal double normal (glue)

Translates the polygon setting of `hasHorizontalDoubleNormal_of_forces` into the
sequence setting of `forces_parallel`:
* cyclic unimodality gives the rise/fall structure in any rotated reading
  (`noZig`);
* the normal cones give the sign-switch properties of the forces;
* Step 5: parallel forces give a horizontal double normal.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-- A cyclic sequence of distinct reals with exactly one local maximum (hence
exactly one local minimum). -/
def IsCyclicUnimodal {k : ℕ} [NeZero k] (z : ZMod k → ℝ) : Prop :=
  Function.Injective z ∧
    (Finset.univ.filter (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i)).card = 1

/-- The corner `(p i, z i)` of the silhouette cycle in `ℝ³`. -/
noncomputable def liftPt (q : ℝ²) (t : ℝ) : ℝ³ := !₂[q 0, q 1, t]

/-- The silhouette cycle `C = x₀x₁⋯x_{k-1}x₀` has a *horizontal double normal*:
two points of `C` at the same depth whose projections span a double normal of
the shadow `conv p`. -/
def HasHorizontalDoubleNormal {k : ℕ} (p : ZMod k → ℝ²) (z : ZMod k → ℝ) : Prop :=
  ∃ y y' : ℝ³, (∃ i, y ∈ segment ℝ (liftPt (p i) (z i)) (liftPt (p (i + 1)) (z (i + 1)))) ∧
    (∃ j, y' ∈ segment ℝ (liftPt (p j) (z j)) (liftPt (p (j + 1)) (z (j + 1)))) ∧
    y 2 = y' 2 ∧ projXy y ≠ projXy y' ∧
    projXy y' - projXy y ∈ normalConeAt (convexHull ℝ (Set.range p)) (projXy y') ∧
    projXy y - projXy y' ∈ normalConeAt (convexHull ℝ (Set.range p)) (projXy y)


/-- An interior maximum over a window of the cycle is a strict local maximum. -/
theorem exists_localMax_window {k : ℕ} (z : ZMod k → ℝ) (hz : Function.Injective z)
    (B : ZMod k) (L : ℕ) (hL : L < k) (u : ℕ) (_hu0 : 0 < u) (huL : u < L)
    (h0 : z B < z (B + u)) (hL' : z (B + L) < z (B + u)) :
    ∃ p : ℕ, 0 < p ∧ p < L ∧ z (B + p - 1) < z (B + p) ∧ z (B + p + 1) < z (B + p) := by
  obtain ⟨p, hp, hmax⟩ := (range (L + 1)).exists_max_image (fun q : ℕ => z (B + q))
    ⟨u, mem_range.mpr (by omega)⟩
  rw [mem_range] at hp
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := hmax u (mem_range.mpr (by omega))
    simp at this; linarith
  have hpL : p ≠ L := by
    rintro rfl
    have := hmax u (mem_range.mpr (by omega))
    linarith
  refine ⟨p, by omega, by omega, ?_, ?_⟩
  · have h1 := hmax (p - 1) (mem_range.mpr (by omega))
    have hc : ((p - 1 : ℕ) : ZMod k) = (p : ZMod k) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    simp only [hc, ← add_sub_assoc] at h1
    refine lt_of_le_of_ne h1 (fun h => ?_)
    have := hz h
    have h2 := zmod_add_ne (k := k) (a := p - 1) (b := p) (by omega) (by omega) (by omega) B
    rw [hc, ← add_sub_assoc] at h2
    exact h2 this
  · have h1 := hmax (p + 1) (mem_range.mpr (by omega))
    simp only [Nat.cast_succ, ← add_assoc] at h1
    refine lt_of_le_of_ne h1 (fun h => ?_)
    have := hz h
    have h2 := zmod_add_ne (k := k) (a := p + 1) (b := p) (by omega) (by omega) (by omega) B
    rw [Nat.cast_succ, ← add_assoc] at h2
    exact h2 this

theorem natCast_mod_two {k : ℕ} {x y : ℕ} (hx : x < k) (hy : y < 2 * k)
    (h : (x : ZMod k) = (y : ZMod k)) : x = y ∨ x + k = y := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx] at h
  by_cases hyk : y < k
  · left; rw [Nat.mod_eq_of_lt hyk] at h; exact h
  · right
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- A cyclically unimodal sequence has at most one strict local maximum. -/
theorem IsCyclicUnimodal.eq_of_localMax {k : ℕ} [NeZero k] {z : ZMod k → ℝ}
    (hz : IsCyclicUnimodal z) {q1 q2 : ZMod k}
    (h1 : z (q1 - 1) < z q1 ∧ z (q1 + 1) < z q1) (h2 : z (q2 - 1) < z q2 ∧ z (q2 + 1) < z q2) :
    q1 = q2 := by
  by_contra hne
  have : 1 < (univ.filter (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i)).card :=
    one_lt_card.mpr ⟨q1, by simp [h1], q2, by simp [h2], hne⟩
  rw [hz.2] at this
  exact lt_irrefl _ this

theorem zmod_add_natCast_sub {k : ℕ} (B : ZMod k) {a x : ℕ} (h : a ≤ x) :
    B + (a : ZMod k) + ((x - a : ℕ) : ZMod k) = B + x := by
  rw [Nat.cast_sub h]; ring

/-- **No zigzag.**  In any linear reading of a cyclically unimodal sequence, four
positions never alternate low–high–low–high. -/
theorem IsCyclicUnimodal.noZig {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (hz : IsCyclicUnimodal z)
    (B : ZMod k) {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d) (hdk : d < k) :
    ¬ ((z (B + a) < z (B + b) ∧ z (B + c) < z (B + b) ∧ z (B + c) < z (B + d) ∧
        z (B + a) < z (B + d)) ∨
       (z (B + b) < z (B + a) ∧ z (B + b) < z (B + c) ∧ z (B + d) < z (B + c) ∧
        z (B + d) < z (B + a))) := by
  have hk0 : 0 < k := by omega
  have hkz : ((k : ℕ) : ZMod k) = 0 := ZMod.natCast_self k
  -- the two windows of a zigzag give two distinct local maxima
  have key : ∀ a b c d : ℕ, a < b → b < c → c < d → d < k →
      z (B + a) < z (B + b) → z (B + c) < z (B + b) → z (B + c) < z (B + d) →
      z (B + a) < z (B + d) → False := by
    intro a b c d hab hbc hcd hdk h1 h2 h3 h4
    obtain ⟨p1, hp1, hp1L, hl1, hr1⟩ := exists_localMax_window z hz.1 (B + a) (c - a) (by omega)
      (b - a) (by omega) (by omega)
      (by rw [zmod_add_natCast_sub B hab.le]; exact h1)
      (by rw [zmod_add_natCast_sub B (by omega : a ≤ c), zmod_add_natCast_sub B hab.le]; exact h2)
    obtain ⟨p2, hp2, hp2L, hl2, hr2⟩ := exists_localMax_window z hz.1 (B + c) (k - c + a)
      (by omega) (d - c) (by omega) (by omega)
      (by rw [zmod_add_natCast_sub B hcd.le]; exact h3)
      (by
        rw [zmod_add_natCast_sub B hcd.le,
          show B + (c : ZMod k) + ((k - c + a : ℕ) : ZMod k) = B + a by
            rw [Nat.cast_add, Nat.cast_sub (by omega), hkz]; ring]
        exact h4)
    have heq := hz.eq_of_localMax ⟨hl1, hr1⟩ ⟨hl2, hr2⟩
    have : ((a + p1 : ℕ) : ZMod k) = ((c + p2 : ℕ) : ZMod k) := by
      push_cast; linear_combination heq
    rcases natCast_mod_two (by omega) (by omega) this with h | h <;> omega
  rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
  · exact key a b c d hab hbc hcd hdk h1 h2 h3 h4
  · -- rotate the pattern: windows around `c` and around `a`
    obtain ⟨p1, hp1, hp1L, hl1, hr1⟩ := exists_localMax_window z hz.1 (B + b) (d - b) (by omega)
      (c - b) (by omega) (by omega)
      (by rw [zmod_add_natCast_sub B hbc.le]; exact h2)
      (by rw [zmod_add_natCast_sub B (by omega : b ≤ d), zmod_add_natCast_sub B hbc.le]; exact h3)
    obtain ⟨p2, hp2, hp2L, hl2, hr2⟩ := exists_localMax_window z hz.1 (B + d) (k - d + b)
      (by omega) (k - d + a) (by omega) (by omega)
      (by
        rw [show B + (d : ZMod k) + ((k - d + a : ℕ) : ZMod k) = B + a by
          rw [Nat.cast_add, Nat.cast_sub (by omega), hkz]; ring]
        exact h4)
      (by
        rw [show B + (d : ZMod k) + ((k - d + a : ℕ) : ZMod k) = B + a by
            rw [Nat.cast_add, Nat.cast_sub (by omega), hkz]; ring,
          show B + (d : ZMod k) + ((k - d + b : ℕ) : ZMod k) = B + b by
            rw [Nat.cast_add, Nat.cast_sub (by omega), hkz]; ring]
        exact h1)
    have heq := hz.eq_of_localMax ⟨hl1, hr1⟩ ⟨hl2, hr2⟩
    have : ((b + p1 : ℕ) : ZMod k) = ((d + p2 : ℕ) : ZMod k) := by
      push_cast; linear_combination heq
    rcases natCast_mod_two (by omega) (by omega) this with h | h <;> omega

/-- Sums over `ZMod k` read linearly from any base point. -/
theorem sum_zmod_eq_sum_range {k : ℕ} [NeZero k] {M : Type*} [AddCommMonoid M]
    (F : ZMod k → M) (B : ZMod k) : ∑ i, F i = ∑ n ∈ range k, F (B + n) := by
  rw [← Equiv.sum_comp (Equiv.addLeft B) F]
  simp only [Equiv.coe_addLeft]
  symm
  refine sum_bij (fun n _ => (n : ZMod k)) (fun _ _ => mem_univ _) (fun a ha b hb h => ?_)
    (fun i _ => ⟨i.val, mem_range.mpr (ZMod.val_lt i), ZMod.natCast_zmod_val i⟩)
    (fun _ _ => rfl)
  rw [mem_range] at ha hb
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact h

/-- Sign pattern with two free positions `0` and `t`. -/
theorem SSlin_of_two_free (c : ℕ → ℝ) (k t : ℕ) (htk : t ≤ k)
    (hpos : ∀ n, 1 ≤ n → n < t → 0 ≤ c n) (hneg : ∀ n, t + 1 ≤ n → n < k → c n ≤ 0) :
    SSlin c k := by
  by_cases ht0 : t = 0
  · subst ht0
    by_cases hc0 : 0 ≤ c 0
    · refine ⟨0, min 1 k, by omega, by omega, Or.inl ⟨fun n h1 h2 => ?_, fun n h1 h2 => ?_⟩⟩
      · have : n = 0 := by omega
        rw [this]; exact hc0
      · exact hneg n (by omega) h1
    · refine ⟨0, 0, le_rfl, by omega, Or.inl ⟨fun n h1 h2 => by omega, fun n h1 h2 => ?_⟩⟩
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · linarith
      · exact hneg n (by omega) h1
  set i0 := if 0 ≤ c 0 then 0 else 1 with hi0
  set j0 := if t < k ∧ 0 ≤ c t then t + 1 else t with hj0
  refine ⟨i0, j0, ?_, ?_, Or.inl ⟨fun n h1 h2 => ?_, fun n h1 h2 => ?_⟩⟩
  · simp only [hi0, hj0]; split_ifs <;> omega
  · simp only [hj0]; split_ifs with h <;> omega
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [hi0] at h1; split_ifs at h1 with h
      · exact h
      · omega
    · by_cases hnt : n < t
      · exact hpos n hn hnt
      · have : n = t := by simp only [hj0] at h2; split_ifs at h2 <;> omega
        subst this
        simp only [hj0] at h2; split_ifs at h2 with h
        · exact h.2
        · omega
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases h2 with h2 | h2
      · simp only [hi0] at h2; split_ifs at h2 with h
        · omega
        · push Not at h; exact h.le
      · simp only [hj0] at h2; split_ifs at h2 <;> omega
    · by_cases hnt : t + 1 ≤ n
      · exact hneg n hnt h1
      · rcases h2 with h2 | h2
        · simp only [hi0] at h2; split_ifs at h2 <;> omega
        · have : n = t := by simp only [hj0] at h2; split_ifs at h2 <;> omega
          subst this
          simp only [hj0] at h2; split_ifs at h2 with h
          · omega
          · push Not at h; exact (h h1).le

theorem mod_add_lt {k o n : ℕ} (ho : o < k) (hn : n < k) :
    (o + n) % k = if o + n < k then o + n else o + n - k := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The sign-switch property survives a cyclic rotation of the index. -/
theorem SSlin_rotate {x : ℕ → ℝ} {k : ℕ} (hx : SSlin x k) (o : ℕ) (ho : o < k) :
    SSlin (fun n => x ((o + n) % k)) k := by
  -- the case "nonnegative on `[i, j)`, nonpositive outside"
  have caseA : ∀ x : ℕ → ℝ, ∀ i j, i ≤ j → j ≤ k → (∀ n, i ≤ n → n < j → 0 ≤ x n) →
      (∀ n, n < k → (n < i ∨ j ≤ n) → x n ≤ 0) → SSlin (fun n => x ((o + n) % k)) k := by
    intro x i j hij hjk hin hout
    by_cases hoi : o ≤ i
    · refine ⟨i - o, j - o, by omega, by omega, Or.inl ⟨fun n h1 h2 => ?_, fun n h1 h2 => ?_⟩⟩
      · dsimp only; rw [mod_add_lt ho (by omega), ite_eq_left (by omega)];
        exact hin _ (by omega) (by omega)
      · dsimp only; rw [mod_add_lt ho h1]
        split_ifs with h
        · exact hout _ h (by omega)
        · exact hout _ (by omega) (by omega)
    · by_cases hjo : o ≤ j
      · refine ⟨j - o, i + k - o, by omega, by omega, Or.inr ⟨fun n h1 h2 => ?_,
          fun n h1 h2 => ?_⟩⟩
        · dsimp only; rw [mod_add_lt ho (by omega)]
          split_ifs with h
          · exact hout _ h (by omega)
          · exact hout _ (by omega) (by omega)
        · dsimp only; rw [mod_add_lt ho h1]
          split_ifs with h
          · exact hin _ (by omega) (by omega)
          · exact hin _ (by omega) (by omega)
      · refine ⟨i + k - o, j + k - o, by omega, by omega, Or.inl ⟨fun n h1 h2 => ?_,
          fun n h1 h2 => ?_⟩⟩
        · dsimp only; rw [mod_add_lt ho (by omega), ite_eq_right (by omega)]
          exact hin _ (by omega) (by omega)
        · dsimp only; rw [mod_add_lt ho h1]
          split_ifs with h
          · exact hout _ h (by omega)
          · exact hout _ (by omega) (by omega)
  obtain ⟨i, j, hij, hjk, hc⟩ := hx
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact caseA x i j hij hjk h1 h2
  · have := caseA (fun n => -x n) i j hij hjk (fun n a b => by simp [h1 n a b])
      (fun n a b => by simp [h2 n a b])
    have := this.neg
    simpa using this

theorem cross2_outNormal (D x y : ℝ²) : cross2 D (outNormal x y) = -⟪D, y - x⟫ := by
  simp [outNormal, cross2, PiLp.inner_apply, Fin.sum_univ_two]; ring

/-- The force at a corner, tested against `D`, is a nonnegative combination of
the (negated) increments of `⟪D, ·⟫` along the two edges at the corner. -/
theorem IsCcwPolygon.corner_value {k : ℕ} {p : ZMod k → ℝ²} (hp : IsCcwPolygon p) (i : ZMod k)
    {f : ℝ²} (hf : f ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i)) (D : ℝ²) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      cross2 D f = a * -⟪D, p i - p (i - 1)⟫ + b * -⟪D, p (i + 1) - p i⟫ := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hp.normalCone_decomp i hf
  refine ⟨a, b, ha, hb, ?_⟩
  rw [cross2_add_right, cross2_smul_right, cross2_smul_right, cross2_outNormal,
    cross2_outNormal]

theorem zmod_add_natCast_pred {k : ℕ} (M : ZMod k) {n : ℕ} (hn : 1 ≤ n) :
    M + (n : ZMod k) - 1 = M + ((n - 1 : ℕ) : ZMod k) := by
  rw [Nat.cast_sub hn, Nat.cast_one]; ring

theorem zmod_add_natCast_succ {k : ℕ} (M : ZMod k) (n : ℕ) :
    M + (n : ZMod k) + 1 = M + ((n + 1 : ℕ) : ZMod k) := by
  rw [Nat.cast_succ]; ring

/-- Corner values of the forces against `D`, read from a corner maximising
`⟪ν, ·⟫`: `≥ 0` strictly inside the decreasing run, `≤ 0` strictly inside the
increasing run (Step 1). -/
theorem IsCcwPolygon.corner_signs {k : ℕ} {p : ZMod k → ℝ²} (hp : IsCcwPolygon p)
    {f : ZMod k → ℝ²} (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i))
    (D : ℝ²) (M : ZMod k) (t : ℕ)
    (hle : ∀ n, n < t → ⟪D, p (M + ((n + 1 : ℕ) : ZMod k)) - p (M + (n : ZMod k))⟫ ≤ 0)
    (hge : ∀ n, t ≤ n → n < k → 0 ≤ ⟪D, p (M + ((n + 1 : ℕ) : ZMod k)) - p (M + (n : ZMod k))⟫) :
    (∀ n, 1 ≤ n → n < t → 0 ≤ cross2 D (f (M + n))) ∧
      (∀ n, t + 1 ≤ n → n < k → cross2 D (f (M + n)) ≤ 0) := by
  constructor
  · intro n h1 h2
    obtain ⟨a, b, ha, hb, h⟩ := hp.corner_value (M + n) (hf _) D
    rw [h, zmod_add_natCast_pred M h1, zmod_add_natCast_succ M n]
    have e1 := hle (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega] at e1
    have e2 := hle n h2
    nlinarith [mul_nonneg ha (neg_nonneg.mpr e1), mul_nonneg hb (neg_nonneg.mpr e2)]
  · intro n h1 h2
    obtain ⟨a, b, ha, hb, h⟩ := hp.corner_value (M + n) (hf _) D
    rw [h, zmod_add_natCast_pred M (by omega), zmod_add_natCast_succ M n]
    have e1 := hge (n - 1) (by omega) (by omega)
    rw [show n - 1 + 1 = n by omega] at e1
    have e2 := hge n (by omega) h2
    nlinarith [mul_nonneg ha e1, mul_nonneg hb e2]

/-- **Sign switch (Step 1)** of the corner forces against any `D`, read from
any base corner `B`. -/
theorem IsCcwPolygon.forces_SS {k : ℕ} [NeZero k] {p : ZMod k → ℝ²} (hp : IsCcwPolygon p)
    {f : ZMod k → ℝ²} (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i))
    (B : ZMod k) (D : ℝ²) : SSlin (fun n => cross2 D (f (B + n))) k := by
  obtain ⟨M, -, hM⟩ := (univ : Finset (ZMod k)).exists_max_image (fun i => ⟪D, p i⟫)
    univ_nonempty
  obtain ⟨t, htk, hle, hge⟩ := hp.pattern_from_max D M (fun i => hM i (mem_univ _))
  obtain ⟨hpos, hneg⟩ := hp.corner_signs hf D M t hle hge
  have hSS := SSlin_of_two_free (fun n => cross2 D (f (M + n))) k t htk hpos hneg
  have hrot := SSlin_rotate hSS (B - M).val (ZMod.val_lt _)
  convert hrot using 2 with n
  congr 2
  rw [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_zmod_val]; ring

/-- Read from corner `u`, the cross-products with its force are nonnegative before the cut
and nonpositive after it. -/
theorem IsCcwPolygon.forces_oriented {k : ℕ} {p : ZMod k → ℝ²} (hp : IsCcwPolygon p)
    {f : ZMod k → ℝ²} (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i))
    (u : ZMod k) :
    ∃ j, j ≤ k ∧ (∀ s, 0 < s → s < j → 0 ≤ cross2 (f u) (f (u + s))) ∧
      (∀ s, j ≤ s → s < k → cross2 (f u) (f (u + s)) ≤ 0) := by
  have hmax : ∀ i, ⟪f u, p i⟫ ≤ ⟪f u, p u⟫ := fun i => by
    have := hf u (p i) (subset_convexHull ℝ _ ⟨i, rfl⟩)
    rw [inner_sub_right] at this; linarith
  obtain ⟨t, htk, hle, hge⟩ := hp.pattern_from_max (f u) u hmax
  obtain ⟨hpos, hneg⟩ := hp.corner_signs hf (f u) u t hle hge
  refine ⟨if t < k ∧ 0 ≤ cross2 (f u) (f (u + t)) then t + 1 else t, ?_, fun s h1 h2 => ?_,
    fun s h1 h2 => ?_⟩
  · split_ifs with h <;> omega
  · by_cases hst : s < t
    · exact hpos s h1 hst
    · split_ifs at h2 with h
      · have : s = t := by omega
        rw [this]; exact h.2
      · omega
  · by_cases hst : t + 1 ≤ s
    · exact hneg s hst h2
    · split_ifs at h1 with h
      · omega
      · have : s = t := by omega
        subst this
        push Not at h
        exact (h h2).le

theorem proj_xy_liftPt (q : ℝ²) (t : ℝ) : projXy (liftPt q t) = q := by
  ext i; fin_cases i <;> simp [projXy, liftPt]

theorem liftPt_two (q : ℝ²) (t : ℝ) : (liftPt q t) 2 = t := by simp [liftPt]

/-- In the plane, a vector parallel to `e` is `⟪e, v⟫ / ‖e‖²` times `e`. -/
theorem norm_sq_smul_of_cross2 {v e : ℝ²} (h : cross2 v e = 0) :
    ‖e‖ ^ 2 • v = ⟪e, v⟫ • e := by
  have hn : ‖e‖ ^ 2 = e 0 ^ 2 + e 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp only [cross2] at h
  ext i; fin_cases i <;> simp [hn, PiLp.inner_apply, Fin.sum_univ_two]
  · linear_combination (e 1) * h
  · linear_combination (-(e 0)) * h

/-- The hull of the corners lies in the slab between the extreme values of a
linear functional. -/
theorem convexHull_le_of_corners {k : ℕ} {p : ZMod k → ℝ²} {e : ℝ²} {M : ℝ}
    (h : ∀ i, ⟪e, p i⟫ ≤ M) : ∀ q ∈ convexHull ℝ (Set.range p), ⟪e, q⟫ ≤ M := by
  intro q hq
  have : convexHull ℝ (Set.range p) ⊆ {q | ⟪e, q⟫ ≤ M} :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact h i)
      (convex_halfSpace_le (innerₛₗ ℝ e).isLinear M)
  exact this hq

theorem convexHull_ge_of_corners {k : ℕ} {p : ZMod k → ℝ²} {e : ℝ²} {μ : ℝ}
    (h : ∀ i, μ ≤ ⟪e, p i⟫) : ∀ q ∈ convexHull ℝ (Set.range p), μ ≤ ⟪e, q⟫ := by
  intro q hq
  have : convexHull ℝ (Set.range p) ⊆ {q | μ ≤ ⟪e, q⟫} :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact h i)
      (convex_halfSpace_ge (innerₛₗ ℝ e).isLinear μ)
  exact this hq

/-- The corners maximising a nonzero linear functional lie in one edge
`{a, a + 1}`. -/
theorem IsCcwPolygon.max_edge {k : ℕ} {p : ZMod k → ℝ²} (hp : IsCcwPolygon p)
    {e : ℝ²} (he : e ≠ 0) (B : ZMod k) (hB : ∀ l, ⟪e, p l⟫ ≤ ⟪e, p B⟫) (S : ZMod k → Prop)
    (hS : ∀ i, S i → ⟪e, p i⟫ = ⟪e, p B⟫) :
    ∃ a : ZMod k, ∀ i, S i → i = a ∨ i = a + 1 := by
  by_cases hm : S (B - 1)
  · refine ⟨B - 1, fun i hi => ?_⟩
    rcases hp.max_adjacent he hB (hS i hi) with h | h | h
    · exact Or.inl h
    · right; rw [h]; ring
    · exfalso
      exact hp.not_three_max he B (hS _ hm) (by rw [← h]; exact hS i hi)
  · refine ⟨B, fun i hi => ?_⟩
    rcases hp.max_adjacent he hB (hS i hi) with h | h | h
    · exact absurd (h ▸ hi) hm
    · exact Or.inl h
    · exact Or.inr h

/-- **Step 5.**  Parallel corner forces with zero sum, zero depth moment and
zero torque give a horizontal double normal. -/
theorem IsCcwPolygon.hdn_of_parallel {k : ℕ} [NeZero k] {p : ZMod k → ℝ²} (hp : IsCcwPolygon p)
    (z : ZMod k → ℝ) {f : ZMod k → ℝ²}
    (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i))
    {e : ℝ²} (he : e ≠ 0) (c : ZMod k → ℝ) (hfc : ∀ i, f i = c i • e) {B : ZMod k}
    (hcB : 0 < c B) (h1 : ∑ i, f i = 0) (h2 : ∑ i, z i • f i = 0)
    (h3 : ∑ i, cross2 (p i) (f i) = 0) : HasHorizontalDoubleNormal p z := by
  classical
  have hk := hp.1
  have hc1 : ∑ i, c i = 0 := by
    have : (∑ i, c i) • e = 0 := by rw [sum_smul, ← h1]; exact sum_congr rfl fun i _ => (hfc i).symm
    exact (smul_eq_zero.mp this).resolve_right he
  have hc2 : ∑ i, c i * z i = 0 := by
    have : (∑ i, c i * z i) • e = 0 := by
      rw [sum_smul, ← h2]; exact sum_congr rfl fun i _ => by rw [hfc i, smul_smul, mul_comm]
    exact (smul_eq_zero.mp this).resolve_right he
  have hc3 : cross2 (∑ i, c i • p i) e = 0 := by
    rw [cross2_comm, cross2_sum_right, neg_eq_zero, ← neg_eq_zero, ← h3, ← sum_neg_distrib]
    exact sum_congr rfl fun i _ => by
      rw [hfc i, cross2_smul_right, cross2_smul_right, cross2_comm e (p i)]; ring
  -- maximisers and minimisers
  have hmaxP : ∀ i, 0 < c i → ∀ j, ⟪e, p j⟫ ≤ ⟪e, p i⟫ := by
    intro i hi j
    have := hf i (p j) (subset_convexHull ℝ _ ⟨j, rfl⟩)
    rw [hfc i, real_inner_smul_left, inner_sub_right] at this
    have := (mul_nonpos_iff.mp this)
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · linarith
    · linarith
  have hminN : ∀ i, c i < 0 → ∀ j, ⟪e, p i⟫ ≤ ⟪e, p j⟫ := by
    intro i hi j
    have := hf i (p j) (subset_convexHull ℝ _ ⟨j, rfl⟩)
    rw [hfc i, real_inner_smul_left, inner_sub_right] at this
    rcases mul_nonpos_iff.mp this with ⟨h, _⟩ | ⟨_, h⟩
    · linarith
    · linarith
  obtain ⟨b0, hb0⟩ : ∃ i, c i < 0 := by
    by_contra hcon; push Not at hcon
    have : 0 < ∑ i, c i := by
      rw [← add_sum_erase _ _ (mem_univ B)]
      have := sum_nonneg fun i (_ : i ∈ univ.erase B) => hcon i
      linarith
    linarith
  set M := ⟪e, p B⟫ with hM
  set μ := ⟪e, p b0⟫ with hμ
  have hPM : ∀ i, 0 < c i → ⟪e, p i⟫ = M := fun i hi =>
    le_antisymm (hmaxP B hcB i) (hmaxP i hi B)
  have hNμ : ∀ i, c i < 0 → ⟪e, p i⟫ = μ := fun i hi =>
    le_antisymm (hminN i hi b0) (hminN b0 hb0 i)
  have hle : ∀ j, ⟪e, p j⟫ ≤ M := hmaxP B hcB
  have hge : ∀ j, μ ≤ ⟪e, p j⟫ := hminN b0 hb0
  have hμM : μ < M := by
    by_contra hcon; push Not at hcon
    have heq : ∀ j, ⟪e, p j⟫ = M := fun j => le_antisymm (hle j) (by linarith [hge j])
    exact hp.not_three_max he B (by rw [heq, heq]) (by rw [heq, heq])
  obtain ⟨a, ha⟩ := hp.max_edge he B hle (fun i => 0 < c i) hPM
  obtain ⟨b, hb⟩ := hp.max_edge (neg_ne_zero.mpr he) b0
    (fun l => by rw [inner_neg_left, inner_neg_left]; linarith [hge l])
    (fun i => c i < 0) (fun i hi => by rw [inner_neg_left, inner_neg_left, hNμ i hi])
  have hneA : a ≠ a + 1 := zmod_ne_add_one (by omega) a
  have hneB : b ≠ b + 1 := zmod_ne_add_one (by omega) b
  set cp : ZMod k → ℝ := fun i => max (c i) 0
  set cn : ZMod k → ℝ := fun i => max (-c i) 0
  have hcpcn : ∀ i, c i = cp i - cn i := fun i => by
    simp only [cp, cn]; rcases le_total 0 (c i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hcp0 : ∀ i, 0 ≤ cp i := fun i => le_max_right _ _
  have hcn0 : ∀ i, 0 ≤ cn i := fun i => le_max_right _ _
  have hcp_supp : ∀ i, i ≠ a ∧ i ≠ a + 1 → cp i = 0 := fun i hi => by
    simp only [cp]; apply max_eq_right; by_contra h; push Not at h
    rcases ha i h with h' | h'
    · exact hi.1 h'
    · exact hi.2 h'
  have hcn_supp : ∀ i, i ≠ b ∧ i ≠ b + 1 → cn i = 0 := fun i hi => by
    simp only [cn]; apply max_eq_right; by_contra h; push Not at h
    rcases hb i (by linarith) with h' | h'
    · exact hi.1 h'
    · exact hi.2 h'
  have hcpM : ∀ i, cp i * ⟪e, p i⟫ = cp i * M := fun i => by
    by_cases h : 0 < c i
    · rw [hPM i h]
    · simp only [cp, max_eq_right (not_lt.mp h), zero_mul]
  have hcnμ : ∀ i, cn i * ⟪e, p i⟫ = cn i * μ := fun i => by
    by_cases h : c i < 0
    · rw [hNμ i h]
    · simp only [cn, max_eq_right (by linarith [not_lt.mp h] : -c i ≤ 0), zero_mul]
  set C := ∑ i, cp i with hC
  have hCn : ∑ i, cn i = C := by
    have : ∑ i, (cp i - cn i) = 0 := by rw [← hc1]; exact sum_congr rfl fun i _ => (hcpcn i).symm
    rw [sum_sub_distrib] at this; linarith
  have hCpos : 0 < C := by
    rw [hC, ← add_sum_erase _ _ (mem_univ B)]
    have : 0 < cp B := lt_max_of_lt_left hcB
    linarith [sum_nonneg fun i (_ : i ∈ univ.erase B) => hcp0 i]
  set x : ZMod k → ℝ³ := fun i => liftPt (p i) (z i) with hx
  set Yp : ℝ³ := (1 / C) • ∑ i, cp i • x i with hYp
  set Yn : ℝ³ := (1 / C) • ∑ i, cn i • x i with hYn
  -- the points lie on silhouette edges
  have hCa : cp a + cp (a + 1) = C := by
    rw [hC, Fintype.sum_eq_add a (a + 1) hneA hcp_supp]
  have hCb : cn b + cn (b + 1) = C := by
    rw [← hCn, Fintype.sum_eq_add b (b + 1) hneB hcn_supp]
  have hYp_seg : Yp ∈ segment ℝ (x a) (x (a + 1)) := by
    refine ⟨cp a / C, cp (a + 1) / C, div_nonneg (hcp0 a) hCpos.le,
      div_nonneg (hcp0 _) hCpos.le, by rw [← add_div, hCa, div_self hCpos.ne'], ?_⟩
    rw [hYp, Fintype.sum_eq_add a (a + 1) hneA (fun i hi => by rw [hcp_supp i hi, zero_smul]),
      smul_add, smul_smul, smul_smul]
    congr 1 <;> congr 1 <;> ring
  have hYn_seg : Yn ∈ segment ℝ (x b) (x (b + 1)) := by
    refine ⟨cn b / C, cn (b + 1) / C, div_nonneg (hcn0 b) hCpos.le,
      div_nonneg (hcn0 _) hCpos.le, by rw [← add_div, hCb, div_self hCpos.ne'], ?_⟩
    rw [hYn, Fintype.sum_eq_add b (b + 1) hneB (fun i hi => by rw [hcn_supp i hi, zero_smul]),
      smul_add, smul_smul, smul_smul]
    congr 1 <;> congr 1 <;> ring
  -- projections and depths
  have hproj : ∀ w : ZMod k → ℝ, projXy ((1 / C) • ∑ i, w i • x i) =
      (1 / C) • ∑ i, w i • p i := fun w => by
    rw [← projL_apply, map_smul, map_sum]
    simp only [map_smul, projL_apply, hx, proj_xy_liftPt]
  have hdepth : ∀ w : ZMod k → ℝ, ((1 / C) • ∑ i, w i • x i) 2 = (1 / C) * ∑ i, w i * z i :=
    fun w => by
      simp only [PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply, hx, liftPt_two]
  have hz_eq : Yp 2 = Yn 2 := by
    rw [hYp, hYn, hdepth, hdepth]
    congr 1
    have : ∑ i, (cp i - cn i) * z i = 0 := by
      rw [← hc2]; exact sum_congr rfl fun i _ => by rw [hcpcn i]
    simp only [sub_mul, sum_sub_distrib] at this
    linarith
  set v := projXy Yp - projXy Yn with hv
  have hv_eq : v = (1 / C) • ∑ i, c i • p i := by
    rw [hv, hYp, hYn, hproj, hproj, ← smul_sub, ← sum_sub_distrib]
    congr 1
    exact sum_congr rfl fun i _ => by rw [hcpcn i, sub_smul]
  have hvc : cross2 v e = 0 := by
    rw [hv_eq, cross2_comm, cross2_smul_right, cross2_comm, hc3]; ring
  have hep : ⟪e, projXy Yp⟫ = M := by
    rw [hYp, hproj, real_inner_smul_right, inner_sum]
    simp only [real_inner_smul_right, hcpM, ← sum_mul, ← hC]
    field_simp
  have hen : ⟪e, projXy Yn⟫ = μ := by
    rw [hYn, hproj, real_inner_smul_right, inner_sum]
    simp only [real_inner_smul_right, hcnμ, ← sum_mul, hCn]
    field_simp
  have hev : ⟪e, v⟫ = M - μ := by rw [hv, inner_sub_right, hep, hen]
  have he2 : 0 < ‖e‖ ^ 2 := by positivity
  set lam := (M - μ) / ‖e‖ ^ 2 with hlam
  have hlam0 : 0 < lam := div_pos (by linarith) he2
  have hvl : v = lam • e := by
    have := norm_sq_smul_of_cross2 hvc
    rw [hev] at this
    apply smul_right_injective ℝ² he2.ne'
    simp only
    rw [this, smul_smul, hlam, mul_div_cancel₀ _ he2.ne']
  refine ⟨Yn, Yp, ⟨b, hYn_seg⟩, ⟨a, hYp_seg⟩, hz_eq.symm, ?_, ?_, ?_⟩
  · intro h
    have : v = 0 := by rw [hv, h, sub_self]
    rw [hvl] at this
    exact he ((smul_eq_zero.mp this).resolve_left hlam0.ne')
  · intro q hq
    rw [show projXy Yp - projXy Yn = v from rfl, hvl, real_inner_smul_left, inner_sub_right, hep]
    exact mul_nonpos_of_nonneg_of_nonpos hlam0.le
      (by linarith [convexHull_le_of_corners hle q hq])
  · intro q hq
    rw [show projXy Yn - projXy Yp = -v by rw [hv]; abel, hvl, inner_neg_left,
      real_inner_smul_left, inner_sub_right, hen]
    have := convexHull_ge_of_corners hge q hq
    nlinarith

theorem IsCcwPolygon.injective {k : ℕ} {p : ZMod k → ℝ²} (hp : IsCcwPolygon p) :
    Function.Injective p := by
  intro i j hij
  by_contra hne
  by_cases h1 : j = i + 1
  · have h := hp.2 (i - 1) j (by rw [h1]; exact (zmod_sub_one_ne_add_one hp.1 i).symm)
      (by rw [h1, sub_add_cancel]; exact (zmod_ne_add_one (by have := hp.1; omega) i).symm)
    rw [sub_add_cancel, ← hij, cross2_self] at h
    exact lt_irrefl _ h
  · have h := hp.2 i j (Ne.symm hne) h1
    rw [← hij, sub_self] at h
    simp [cross2] at h

/-- Three points with positive orientation are affinely independent. -/
theorem affineIndependent_of_cross2_pos {a b c : ℝ²} (h : 0 < cross2 (b - a) (c - a)) :
    AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hcol
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (p₀ := a) (by simp)).mp hcol
  obtain ⟨rb, hrb⟩ := hv b (by simp)
  obtain ⟨rc, hrc⟩ := hv c (by simp)
  rw [vadd_eq_add] at hrb hrc
  rw [hrb, hrc, add_sub_cancel_right, add_sub_cancel_right, cross2_smul_right,
    show cross2 (rb • v) v = rb * cross2 v v by simp [cross2]; ring, cross2_self] at h
  simp at h

/-- A strictly convex polygon has interior points. -/
theorem IsCcwPolygon.interior_nonempty {k : ℕ} {p : ZMod k → ℝ²} (hp : IsCcwPolygon p) :
    (interior (convexHull ℝ (Set.range p))).Nonempty := by
  have hk := hp.1
  have h2 : (2 : ZMod k) ≠ 0 := by
    have := zmod_add_ne (k := k) (a := 2) (b := 0) (by omega) (by omega) (by omega) 0
    simpa using this
  have h21 : (2 : ZMod k) ≠ 0 + 1 := by
    have := zmod_add_ne (k := k) (a := 2) (b := 1) (by omega) (by omega) (by omega) 0
    simpa using this
  have hpos := hp.2 0 2 h2 h21
  rw [zero_add] at hpos
  have hind := affineIndependent_of_cross2_pos hpos
  have hspan : affineSpan ℝ (Set.range ![p 0, p 1, p 2]) = ⊤ :=
    (hind.affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr (by simp)
  have := (interior_convexHull_nonempty_iff_affineSpan_eq_top).mpr hspan
  refine this.mono (interior_mono (convexHull_mono ?_))
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp

/-- At an interior point the normal cone is `{0}`. -/
theorem normalConeAt_eq_zero_of_mem_interior {S : Set ℝ²} {q n : ℝ²} (hq : q ∈ interior S)
    (hn : n ∈ normalConeAt S q) : n = 0 := by
  by_contra hn0
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior q hq
  have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn0
  have hmem : q + (r / 2 / ‖n‖) • n ∈ S := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), div_mul_cancel₀ _ hnpos.ne']
    linarith))
  have := hn _ hmem
  rw [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq] at this
  have : 0 < r / 2 / ‖n‖ * ‖n‖ ^ 2 := by positivity
  linarith

end Minimality

end RupertMinimality
