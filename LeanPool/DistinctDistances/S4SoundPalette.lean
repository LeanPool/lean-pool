/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.ChordRadiusBound
public import LeanPool.DistinctDistances.S4RowBuilder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Soundness of the close-pair rows of the `1/40` certificate

Proves that the rows `Pa`, `Pb`, `Pc` of Theorem S4 of
`docs/results/explicit-constant-gain-1-40-2026-10-21.md` (Lemma P'' (a), (b), (c) of
`docs/results/explicit-constant-gain-5-239-2026-10-20.md`, §2), as built by
`Esgk.S4.Params.rowPa`, `Esgk.S4.Params.rowPb` and `Esgk.S4.Params.rowPc`, hold at the
normalized variables `Esgk.S4.val` of a configuration of the contradiction argument.

* `Esgk.S4.Params.chordOK_sound`: the chord evidence of `Esgk.S4.Params.chordOK` gives the chord
  condition `Esgk.S4.Setting.ChordHolds`. Evidence `0` is the uniform Step L0 and evidence `1`
  the radius bound (both from `Esgk.saturated_incidence_close_pair_of_radius`, cases (b) and
  (a)); evidence `k + 2` is the proved chord condition `k` of the table, made weaker by a
  smaller lower radius, a larger upper radius and a larger chord bound.
* `Esgk.S4.Params.rowPa_sound`, `Esgk.S4.Params.rowPb_sound`, `Esgk.S4.Params.rowPc_sound`: the
  rows. For `r′² < 4` they are the radius-cut forms of Lemma P'' divided by `n²`
  (`Esgk.sum_closedBall_sq_card_sub_one_lower_bound_radius_cut` and its relatives); for
  `r′² ≥ 4` every palette value has `r² ≤ 4ρ² ≤ r′²ρ²`, and they are the bounded-palette forms
  divided by `n²` (`Esgk.sum_closedBall_sq_card_sub_one_lower_bound_bounded_palette` and its
  relatives). The thresholds are `u = g_ih² ρ²`, `v = g_ir² ρ²` and `t = g_iρ² ρ²`.

The table evidence compares the upper radius `hi` with the upper radius of the table entry
without squares, so it needs `0 ≤ hi`; the builder checks `0 ≤ hi` in that branch.
-/

@[expose] public section

namespace Esgk.S4

open Finset EuclideanGeometry

variable {n : ℕ}

/-! ### Chord conditions -/

/-- **The chord evidence is sound.** If the builder accepts the chord evidence `e` for the
chord condition `(lo, hi, T)` and the proved chord conditions of the table hold, then every
saturated incidence of radius `r` with `lo²ρ² < r² ≤ hi²ρ²` has two of its points at squared
distance at most `Tρ²`. Evidence `0`: the uniform Step L0 `(1 - sBar²)(1 + sBar) ≤ sBar T`.
Evidence `1`: the radius bound `(1 - sBar²)² hi² ≤ sBar² T²` with `T ≥ 0`. Evidence `k + 2`: the
table entry `k` with `0 ≤ lo′ ≤ lo`, `0 ≤ hi ≤ hi′` and `T′ ≤ T`. -/
theorem Params.chordOK_sound (P : Params) (S : Setting n) {lo hi T : ℚ} {e : Nat}
    (h : P.chordOK lo hi T e = true) (hch : P.ChordsHold S) :
    S.ChordHolds lo hi T := by
  have hσ : (0 : ℝ) < (sig : ℝ) := by rw [Setting.sig_cast]; norm_num
  match e, h with
  | 0, h =>
    simp only [Params.chordOK, decide_eq_true_eq] at h
    have hb : (1 - (sig : ℝ) ^ 2) * (1 + (sig : ℝ)) ≤ (sig : ℝ) * (T : ℝ) := by
      have h' := (Rat.cast_le (K := ℝ)).2 h
      push_cast at h'
      linarith
    exact saturated_incidence_close_pair_of_radius (v := (hi : ℝ) ^ 2) S.hρ hσ S.hlo S.hhi
      (Or.inr (Or.inl hb)) _
  | 1, h =>
    simp only [Params.chordOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, hT⟩ := h
    have ha : (1 - (sig : ℝ) ^ 2) ^ 2 * (hi : ℝ) ^ 2 ≤ (sig : ℝ) ^ 2 * (T : ℝ) ^ 2 := by
      have h' := (Rat.cast_le (K := ℝ)).2 h1
      push_cast at h'
      linarith
    exact saturated_incidence_close_pair_of_radius S.hρ hσ S.hlo S.hhi
      (Or.inl ⟨ha, by exact_mod_cast hT⟩) _
  | k + 2, h =>
    simp only [Params.chordOK, Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq] at h
    obtain ⟨⟨⟨⟨⟨hk, h0⟩, hlo⟩, hhi⟩, hhi'⟩, hT⟩ := h
    intro x hx hl hh
    have hρ2 : 0 ≤ S.ρ ^ 2 := sq_nonneg _
    have hlo2 : ((P.ch k).1 : ℝ) ^ 2 ≤ (lo : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by exact_mod_cast h0) (by exact_mod_cast hlo) 2
    have hhi2 : (hi : ℝ) ^ 2 ≤ ((P.ch k).2.1 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by exact_mod_cast hhi) (by exact_mod_cast hhi') 2
    obtain ⟨a, b, ha, hb, hab, hd⟩ := hch k hk x hx
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hlo2 hρ2) hl)
      (hh.trans (mul_le_mul_of_nonneg_right hhi2 hρ2))
    exact ⟨a, b, ha, hb, hab,
      hd.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hT) hρ2)⟩

/-! ### Normalized variables in count form -/

/-- `0 < n` in `ℝ`. -/
private theorem natCast_pos (S : Setting n) : (0 : ℝ) < n := by exact_mod_cast S.n_pos

section CountForm

variable (P : Params) (S : Setting n)

/-- `P(gᵢ²ρ²) = 𝒜(gᵢ) n²`. -/
private theorem pairs_eq_val {i : Nat} (hi : i < P.ng) :
    S.pairs ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) = val P S (aVar i) * ((n : ℝ) * n) := by
  have hN := natCast_pos S
  rw [val_aVar P S hi, div_mul_cancel₀ _ (mul_pos hN hN).ne']

/-- `R(gᵢ²ρ²) = ℛ(gᵢ) n`. -/
private theorem pal_eq_val {i : Nat} (hi : i < P.ng) :
    S.pal ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) = val P S (rVar i) * n := by
  rw [val_rVar P S hi, div_mul_cancel₀ _ (natCast_pos S).ne']

/-- `D = (D/n) n`. -/
private theorem D_eq_val : S.D = val P S P.dV * n := by
  rw [val_dV, div_mul_cancel₀ _ (natCast_pos S).ne']

/-- `(1/n) n² = n`. -/
private theorem eV_mul : val P S P.eV * ((n : ℝ) * n) = n := by
  have hN := (natCast_pos S).ne'
  rw [val_eV]
  field_simp

/-- The side conditions of Lemma P'' accepted by `Params.palOK`, as real inequalities on the
thresholds `u = g_ih²ρ²`, `v = g_ir²ρ²`, `t = g_iρ²ρ²`, with the chord condition on the
saturated circles of squared radius in `(u, v]`. -/
private theorem palOK_facts {iρ ir ih e : Nat} (h : P.palOK iρ ir ih e = true)
    (hch : P.ChordsHold S) :
    iρ < P.ng ∧ ir < P.ng ∧ ih < P.ng ∧
    0 ≤ (P.g ih : ℝ) ^ 2 * S.ρ ^ 2 ∧
    (P.g ih : ℝ) ^ 2 * S.ρ ^ 2 ≤ (P.g ir : ℝ) ^ 2 * S.ρ ^ 2 ∧
    4 * ((P.g ih : ℝ) ^ 2 * S.ρ ^ 2) ≤ (P.g iρ : ℝ) ^ 2 * S.ρ ^ 2 ∧
    (∀ x ∈ SaturatedDistanceIncidences S.p, (P.g ih : ℝ) ^ 2 * S.ρ ^ 2 < x.2 ^ 2 →
      x.2 ^ 2 ≤ (P.g ir : ℝ) ^ 2 * S.ρ ^ 2 → ∃ a b,
        a ∈ DistanceOutNeighborsAtValue S.p x.1 x.2 ∧
        b ∈ DistanceOutNeighborsAtValue S.p x.1 x.2 ∧ a < b ∧
        dist (S.p a) (S.p b) ^ 2 ≤ (P.g iρ : ℝ) ^ 2 * S.ρ ^ 2) := by
  simp only [Params.palOK, Params.ok, Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hiρ, hir⟩, hih⟩, -⟩, h4⟩, hle⟩, hc⟩ := h
  have hρ2 : 0 ≤ S.ρ ^ 2 := sq_nonneg _
  have hT : ((P.sq iρ : ℚ) : ℝ) = (P.g iρ : ℝ) ^ 2 := by
    simp only [Params.sq]; push_cast; ring
  have h4R : 4 * (P.g ih : ℝ) ^ 2 ≤ (P.g iρ : ℝ) ^ 2 := by
    have h' := (Rat.cast_le (K := ℝ)).2 h4
    simp only [Params.sq] at h'
    push_cast at h'
    linarith
  have hleR : (P.g ih : ℝ) ^ 2 ≤ (P.g ir : ℝ) ^ 2 := by
    have h' := (Rat.cast_le (K := ℝ)).2 hle
    simp only [Params.sq] at h'
    push_cast at h'
    linarith
  have hchord := P.chordOK_sound S hc hch
  refine ⟨hiρ, hir, hih, by positivity, mul_le_mul_of_nonneg_right hleR hρ2, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right h4R hρ2
    linarith
  · intro x hx hl hh
    obtain ⟨a, b, ha, hb, hab, hd⟩ := hchord x hx hl hh
    rw [hT] at hd
    exact ⟨a, b, ha, hb, hab, hd⟩

/-- For `g_ir² ≥ 4`, every palette value has `r² ≤ 4ρ² ≤ g_ir²ρ²`. -/
private theorem palette_sq_le_of_four_le {ir : Nat} (h4 : 4 ≤ P.sq ir) :
    ∀ x ∈ OrderedDistanceValues S.p, x ^ 2 ≤ (P.g ir : ℝ) ^ 2 * S.ρ ^ 2 := by
  intro x hx
  have h1 := palette_sq_le_four_mul_distanceAnnulusRadiusSq S.n_pos S.hcap hx
  rw [← S.hρsq] at h1
  have h4R : (4 : ℝ) ≤ (P.g ir : ℝ) ^ 2 := by
    have h' := (Rat.cast_le (K := ℝ)).2 h4
    simp only [Params.sq] at h'
    push_cast at h'
    linarith
  have := mul_le_mul_of_nonneg_right h4R (sq_nonneg S.ρ)
  linarith

end CountForm

/-! ### The rows -/

/-- **Row `Pa` is sound** (Lemma P''(a) at `ρ = g_iρ`, `r′ = g_ir`, `ρ/2 = g_ih`, with the
chord evidence `e`). For `g_ir² < 4` the row is `𝒜(r′) - 2ℛ(r′) - 𝒜(ρ) ≤ 0`, the count form
`P(v) - 2n R(v) ≤ P(t)` divided by `n²`; for `g_ir² ≥ 4` it is `-1/n - 2D/n - 𝒜(ρ) ≤ -1`, the
count form `n(n - 1) - 2nD ≤ P(t)` divided by `n²`. Thresholds `u = g_ih²ρ²`, `v = g_ir²ρ²`,
`t = g_iρ²ρ²`. -/
theorem Params.rowPa_sound (P : Params) (S : Setting n) {iρ ir ih e : Nat} {r : QRow}
    (h : P.rowPa iρ ir ih e = some r) (hch : P.ChordsHold S) :
    r.Holds (val P S) := by
  unfold Params.rowPa at h
  by_cases hok : P.palOK iρ ir ih e = true
  · rw [ite_eq_left hok] at h
    obtain rfl := Option.some.inj h
    obtain ⟨hiρ, hir, -, hu, huv, hut, hS⟩ := palOK_facts P S hok hch
    have hN := natCast_pos S
    have hNN : (0 : ℝ) < (n : ℝ) * n := mul_pos hN hN
    by_cases h4 : 4 ≤ P.sq ir
    · have hL : (n : ℝ) * ((n : ℝ) - 1) - 2 * (n : ℝ) * S.D ≤
          S.pairs ((P.g iρ : ℝ) ^ 2 * S.ρ ^ 2) :=
        sum_closedBall_sq_card_sub_one_lower_bound_bounded_palette S.hp S.hgp.1 S.hcap hu huv
          hut (palette_sq_le_of_four_le P S h4) hS
      rw [D_eq_val P S, pairs_eq_val P S hiρ] at hL
      have he := eV_mul P S
      simp only [Params.palBase, decide_eq_true h4, Bool.cond_true, QRow.Holds, QRow.lhs,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      push_cast
      refine le_of_mul_le_mul_right ?_ hNN
      linarith
    · have hL : S.pairs ((P.g ir : ℝ) ^ 2 * S.ρ ^ 2) -
          2 * (n : ℝ) * S.pal ((P.g ir : ℝ) ^ 2 * S.ρ ^ 2) ≤
          S.pairs ((P.g iρ : ℝ) ^ 2 * S.ρ ^ 2) :=
        sum_closedBall_sq_card_sub_one_lower_bound_radius_cut S.hp S.hgp.1 S.hcap hu huv hut hS
      rw [pairs_eq_val P S hir, pal_eq_val P S hir, pairs_eq_val P S hiρ] at hL
      simp only [Params.palBase, decide_eq_false h4, Bool.cond_false, QRow.Holds, QRow.lhs,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      push_cast
      refine le_of_mul_le_mul_right ?_ hNN
      linarith
  · rw [ite_eq_right hok] at h
    exact absurd h (by simp)

/-- **Row `Pb` is sound** (Lemma P''(b) at `ρ = g_iρ`, `r′ = g_ir`, `ρ/2 = g_ih`, with the
chord evidence `e`). For `g_ir² < 4` the row is
`𝒜(r′) - 2ℛ(r′) - 𝒜(ρ) + 𝒜(ρ/2) - ℛ(ρ/2) ≤ 0`, the count form
`P(u) + P(v) - n R(u) - 2n R(v) ≤ P(t)` divided by `n²`; for `g_ir² ≥ 4` it is
`-1/n - 2D/n - 𝒜(ρ) + 𝒜(ρ/2) - ℛ(ρ/2) ≤ -1`, the count form
`P(u) + n(n - 1) - n R(u) - 2nD ≤ P(t)` divided by `n²`. Thresholds `u = g_ih²ρ²`,
`v = g_ir²ρ²`, `t = g_iρ²ρ²`. -/
theorem Params.rowPb_sound (P : Params) (S : Setting n) {iρ ir ih e : Nat} {r : QRow}
    (h : P.rowPb iρ ir ih e = some r) (hch : P.ChordsHold S) :
    r.Holds (val P S) := by
  unfold Params.rowPb at h
  by_cases hok : P.palOK iρ ir ih e = true
  · rw [ite_eq_left hok] at h
    obtain rfl := Option.some.inj h
    obtain ⟨hiρ, hir, hih, hu, huv, hut, hS⟩ := palOK_facts P S hok hch
    have hN := natCast_pos S
    have hNN : (0 : ℝ) < (n : ℝ) * n := mul_pos hN hN
    by_cases h4 : 4 ≤ P.sq ir
    · have hL : S.pairs ((P.g ih : ℝ) ^ 2 * S.ρ ^ 2) + (n : ℝ) * ((n : ℝ) - 1) -
          (n : ℝ) * S.pal ((P.g ih : ℝ) ^ 2 * S.ρ ^ 2) - 2 * (n : ℝ) * S.D ≤
          S.pairs ((P.g iρ : ℝ) ^ 2 * S.ρ ^ 2) :=
        sum_closedBall_sq_card_sub_one_lower_bound_bounded_palette_add_short S.hp S.hgp.1
          S.hcap hu huv hut (palette_sq_le_of_four_le P S h4) hS
      rw [D_eq_val P S, pairs_eq_val P S hih, pal_eq_val P S hih, pairs_eq_val P S hiρ] at hL
      have he := eV_mul P S
      simp only [Params.palBase, decide_eq_true h4, Bool.cond_true, QRow.Holds, QRow.lhs,
        List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      push_cast
      refine le_of_mul_le_mul_right ?_ hNN
      linarith
    · have hL : S.pairs ((P.g ih : ℝ) ^ 2 * S.ρ ^ 2) + S.pairs ((P.g ir : ℝ) ^ 2 * S.ρ ^ 2) -
          (n : ℝ) * S.pal ((P.g ih : ℝ) ^ 2 * S.ρ ^ 2) -
          2 * (n : ℝ) * S.pal ((P.g ir : ℝ) ^ 2 * S.ρ ^ 2) ≤
          S.pairs ((P.g iρ : ℝ) ^ 2 * S.ρ ^ 2) :=
        sum_closedBall_sq_card_sub_one_lower_bound_radius_cut_add_short S.hp S.hgp.1 S.hcap hu
          huv hut hS
      rw [pairs_eq_val P S hih, pairs_eq_val P S hir, pal_eq_val P S hih, pal_eq_val P S hir,
        pairs_eq_val P S hiρ] at hL
      simp only [Params.palBase, decide_eq_false h4, Bool.cond_false, QRow.Holds, QRow.lhs,
        List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      push_cast
      refine le_of_mul_le_mul_right ?_ hNN
      linarith
  · rw [ite_eq_right hok] at h
    exact absurd h (by simp)

/-- **Row `Pc` is sound** (Lemma P''(c) at `ρ = g_iρ`, `r′ = g_ir`, `ρ/2 = g_ih`, with the
chord evidence `e`). For `g_ir² < 4` the row is
`𝒜(r′) - 2ℛ(r′) - 𝒜(ρ) - 𝒜(ρ/2) + 2ℛ(ρ/2) ≤ 0`, the count form
`P(v) - P(u) - 2n R(v) + 2n R(u) ≤ P(t)` divided by `n²`; for `g_ir² ≥ 4` it is
`-1/n - 2D/n - 𝒜(ρ) - 𝒜(ρ/2) + 2ℛ(ρ/2) ≤ -1`, the count form
`n(n - 1) - P(u) - 2nD + 2n R(u) ≤ P(t)` divided by `n²`. Thresholds `u = g_ih²ρ²`,
`v = g_ir²ρ²`, `t = g_iρ²ρ²`. -/
theorem Params.rowPc_sound (P : Params) (S : Setting n) {iρ ir ih e : Nat} {r : QRow}
    (h : P.rowPc iρ ir ih e = some r) (hch : P.ChordsHold S) :
    r.Holds (val P S) := by
  unfold Params.rowPc at h
  by_cases hok : P.palOK iρ ir ih e = true
  · rw [ite_eq_left hok] at h
    obtain rfl := Option.some.inj h
    obtain ⟨hiρ, hir, hih, hu, huv, hut, hS⟩ := palOK_facts P S hok hch
    have hN := natCast_pos S
    have hNN : (0 : ℝ) < (n : ℝ) * n := mul_pos hN hN
    by_cases h4 : 4 ≤ P.sq ir
    · have hL : (n : ℝ) * ((n : ℝ) - 1) - S.pairs ((P.g ih : ℝ) ^ 2 * S.ρ ^ 2) -
          2 * (n : ℝ) * S.D + 2 * (n : ℝ) * S.pal ((P.g ih : ℝ) ^ 2 * S.ρ ^ 2) ≤
          S.pairs ((P.g iρ : ℝ) ^ 2 * S.ρ ^ 2) :=
        sum_closedBall_sq_card_sub_one_lower_bound_bounded_palette_sub_short S.hp S.hgp.1
          S.hcap hu huv hut (palette_sq_le_of_four_le P S h4) hS
      rw [D_eq_val P S, pairs_eq_val P S hih, pal_eq_val P S hih, pairs_eq_val P S hiρ] at hL
      have he := eV_mul P S
      simp only [Params.palBase, decide_eq_true h4, Bool.cond_true, QRow.Holds, QRow.lhs,
        List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      push_cast
      refine le_of_mul_le_mul_right ?_ hNN
      linarith
    · have hL : S.pairs ((P.g ir : ℝ) ^ 2 * S.ρ ^ 2) - S.pairs ((P.g ih : ℝ) ^ 2 * S.ρ ^ 2) -
          2 * (n : ℝ) * S.pal ((P.g ir : ℝ) ^ 2 * S.ρ ^ 2) +
          2 * (n : ℝ) * S.pal ((P.g ih : ℝ) ^ 2 * S.ρ ^ 2) ≤
          S.pairs ((P.g iρ : ℝ) ^ 2 * S.ρ ^ 2) :=
        sum_closedBall_sq_card_sub_one_lower_bound_radius_cut_sub_short S.hp S.hgp.1 S.hcap hu
          huv hut hS
      rw [pairs_eq_val P S hih, pairs_eq_val P S hir, pal_eq_val P S hih, pal_eq_val P S hir,
        pairs_eq_val P S hiρ] at hL
      simp only [Params.palBase, decide_eq_false h4, Bool.cond_false, QRow.Holds, QRow.lhs,
        List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      push_cast
      refine le_of_mul_le_mul_right ?_ hNN
      linarith
  · rw [ite_eq_right hok] at h
    exact absurd h (by simp)

end Esgk.S4
