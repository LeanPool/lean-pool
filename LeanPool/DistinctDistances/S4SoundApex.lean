/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.ApexWindowGeneral
public import LeanPool.DistinctDistances.KappaImageGap
public import LeanPool.DistinctDistances.S4RowBuilder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Soundness of the rows A'' and J of the `1/40` certificate

Theorem S4 of `docs/results/explicit-constant-gain-1-40-2026-10-21.md` uses two row families
whose geometric content is a single count inequality each:

* Lemma A'' (`Params.rowAA`): the averaged apex-window row at a far threshold `λ = g_il`, window
  ends `w = g_iw`, `h = g_ih` and a rational witness `r₄ ≥ √(4 - λ²)`. The count form is
  `six_mul_far_pairs_le_apex_window_general`; the row is that inequality divided by `3n²`.
* Lemma J (`Params.rowJ`): the κ-image length gap at `λ = g_il`, `g₂ = g_ig2`, `g_σ = g_igs`,
  with `h₀² = W²/(4λ²)` (`W = 1 - sBar²`) and a rational witness `u ≤ √(sBar² - h₀²)`. The count
  form is `sum_closedBall_sq_card_kappa_gap`; the row is that inequality divided by `n²`.

Each soundness theorem reads the side conditions checked in `ℚ` by the row builder, casts them
to `ℝ`, applies the count inequality with `c`, `ρ` and `σ = sBar` of the `Setting`, and divides.
-/

@[expose] public section

namespace Esgk.S4

/-- `n > 0` and `n² > 0` in `ℝ` for a `Setting`. -/
private theorem setting_cast_pos {n : ℕ} (S : Setting n) : (0 : ℝ) < n ∧ (0 : ℝ) < n * n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast S.n_pos
  exact ⟨hn, mul_pos hn hn⟩

/-- `0 < sBar` in `ℝ`. -/
private theorem sig_cast_pos : (0 : ℝ) < (sig : ℝ) := by
  rw [Setting.sig_cast]; norm_num

/-- Soundness of the row of Lemma A'': if `rowAA` accepts the indices and the witness
`r₄ = r4n/r4d`, its row `-2𝒜(λ) - (4/3)𝒜(h) + (4/3)𝒜(w) - 6 D/n - 4/n ≤ -4` holds at the
normalized variables of `S`. This is `six_mul_far_pairs_le_apex_window_general` at
`σ = sBar`, `l = g_il²`, `w = g_iw²`, `h = g_ih²`, `r₄ = r4n/r4d`, divided by `3n²`. -/
theorem Params.rowAA_sound {n : ℕ} (P : Params) (S : Setting n) {il iw ih r4n r4d : Nat}
    {r : QRow} (h : P.rowAA il iw ih r4n r4d = some r) : r.Holds (val P S) := by
  unfold Params.rowAA at h
  dsimp only at h
  split_ifs at h with hc
  obtain rfl := (Option.some.inj h).symm
  generalize mkRat (r4n : ℤ) r4d = r4 at hc
  simp only [Params.ok, Params.stepL0, Nat.blt_eq, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at hc
  simp only [Params.sq] at hc
  obtain ⟨hil, hiw, hih, hr0, hlr, hlσ, hL0, hw0, hw, hh⟩ := hc
  obtain ⟨hn, hnn⟩ := setting_cast_pos S
  have hr0' : (0 : ℝ) ≤ (r4 : ℝ) := by exact_mod_cast hr0
  have hlr' : 4 - (P.g il : ℝ) ^ 2 ≤ (r4 : ℝ) ^ 2 := by
    rw [pow_two, pow_two]; exact_mod_cast hlr
  have hlσ' : 4 - (P.g il : ℝ) ^ 2 ≤ 4 * (sig : ℝ) ^ 2 := by
    rw [pow_two, pow_two]; exact_mod_cast hlσ
  have hL0' : (1 - (sig : ℝ) ^ 2) * ((sig : ℝ) + 1) ≤ (sig : ℝ) * (P.g il : ℝ) ^ 2 := by
    rw [pow_two, pow_two]; exact_mod_cast hL0
  have hw0' : (0 : ℝ) ≤ (P.g iw : ℝ) ^ 2 := sq_nonneg _
  have hw' : (P.g iw : ℝ) ^ 2 ≤ (sig : ℝ) ^ 2 + 1 - (sig : ℝ) * (r4 : ℝ) := by
    rw [pow_two, pow_two]; exact_mod_cast hw
  have hh' : 2 + (r4 : ℝ) ≤ (P.g ih : ℝ) ^ 2 := by
    rw [pow_two]; exact_mod_cast hh
  have hA : 6 * ((n : ℝ) * n - n - S.pairs ((P.g il : ℝ) ^ 2 * S.ρ ^ 2)) ≤
      6 * (n : ℝ) * (3 * S.D - (n : ℝ) + 1) +
        4 * (S.pairs ((P.g ih : ℝ) ^ 2 * S.ρ ^ 2) - S.pairs ((P.g iw : ℝ) ^ 2 * S.ρ ^ 2)) :=
    six_mul_far_pairs_le_apex_window_general S.hp S.hgp.1 S.hcap S.hρ sig_cast_pos S.hlo S.hhi
      hr0' hlr' hlσ' hL0' hw0' hw' hh'
  simp only [QRow.Holds, QRow.lhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [val_aVar P S hil, val_aVar P S hiw, val_aVar P S hih, val_dV, val_eV]
  have e : ((-2 : ℚ) : ℝ) * (S.pairs ((P.g il : ℝ) ^ 2 * S.ρ ^ 2) / ((n : ℝ) * n)) +
      (((-4 / 3 : ℚ) : ℝ) * (S.pairs ((P.g ih : ℝ) ^ 2 * S.ρ ^ 2) / ((n : ℝ) * n)) +
      (((4 / 3 : ℚ) : ℝ) * (S.pairs ((P.g iw : ℝ) ^ 2 * S.ρ ^ 2) / ((n : ℝ) * n)) +
      (((-6 : ℚ) : ℝ) * (S.D / n) + (((-4 : ℚ) : ℝ) * (1 / n) + 0)))) =
      (-2 * S.pairs ((P.g il : ℝ) ^ 2 * S.ρ ^ 2) - 4 / 3 * S.pairs ((P.g ih : ℝ) ^ 2 * S.ρ ^ 2)
        + 4 / 3 * S.pairs ((P.g iw : ℝ) ^ 2 * S.ρ ^ 2) - 6 * S.D * n - 4 * n) /
        ((n : ℝ) * n) := by
    push_cast
    field_simp
    ring
  rw [e, div_le_iff₀ hnn]
  push_cast
  linarith

/-- Soundness of the row of Lemma J: if `rowJ` accepts the indices and the witness
`u = un/ud`, its row `𝒜(g₂) - 𝒜(λ) - 𝒜(g_σ) - 6 D/n - 2/n ≤ -2` holds at the normalized
variables of `S`. This is `sum_closedBall_sq_card_kappa_gap` at `s = sBar`, `l = g_il²`,
`H = W²/(4 g_il²)` with `W = 1 - sBar²`, `G' = g_ig2²`, `g = g_igs`, `G'' = g_igs²`,
`u = un/ud`, divided by `n²`. -/
theorem Params.rowJ_sound {n : ℕ} (P : Params) (S : Setting n) {il ig2 igs un ud : Nat}
    {r : QRow} (h : P.rowJ il ig2 igs un ud = some r) : r.Holds (val P S) := by
  unfold Params.rowJ at h
  dsimp only at h
  split_ifs at h with hc
  obtain rfl := (Option.some.inj h).symm
  generalize mkRat (un : ℤ) ud = u at hc
  generalize wid * wid / (4 * P.sq il) = H at hc
  simp only [Params.ok, Nat.blt_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hc
  simp only [Params.sq, wid] at hc
  obtain ⟨hil, hig2, higs, hl, hH, hG', hu0, hu, hg0, hg⟩ := hc
  obtain ⟨hn, hnn⟩ := setting_cast_pos S
  have hl' : (0 : ℝ) < (P.g il : ℝ) ^ 2 := by
    rw [pow_two]; exact_mod_cast hl
  have hH' : (1 - (sig : ℝ) ^ 2) ^ 2 ≤ 4 * (P.g il : ℝ) ^ 2 * (H : ℝ) := by
    rw [pow_two, pow_two, pow_two]; exact_mod_cast hH
  have hG'' : (P.g ig2 : ℝ) ^ 2 < 4 * ((sig : ℝ) ^ 2 - (H : ℝ)) := by
    rw [pow_two, pow_two]; exact_mod_cast hG'
  have hu0' : (0 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu0
  have hu' : (u : ℝ) ^ 2 ≤ (sig : ℝ) ^ 2 - (H : ℝ) := by
    rw [pow_two, pow_two]; exact_mod_cast hu
  have hg0' : (0 : ℝ) ≤ (P.g igs : ℝ) := by exact_mod_cast hg0
  have hg' : 1 - (sig : ℝ) ^ 2 ≤ (P.g igs : ℝ) ^ 2 + 2 * (P.g igs : ℝ) * (u : ℝ) := by
    rw [pow_two, pow_two]; exact_mod_cast hg
  have hJ : S.pairs ((P.g ig2 : ℝ) ^ 2 * S.ρ ^ 2) - S.pairs ((P.g il : ℝ) ^ 2 * S.ρ ^ 2) -
      S.pairs ((P.g igs : ℝ) ^ 2 * S.ρ ^ 2) ≤ 2 * (n : ℝ) * (3 * S.D - (n : ℝ) + 1) :=
    sum_closedBall_sq_card_kappa_gap S.hp S.hgp S.hρ S.hlo S.hhi hl' hH' hG'' hu0' hu' hg0'
      hg' le_rfl
  simp only [QRow.Holds, QRow.lhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [val_aVar P S hig2, val_aVar P S hil, val_aVar P S higs, val_dV, val_eV]
  have e : ((1 : ℚ) : ℝ) * (S.pairs ((P.g ig2 : ℝ) ^ 2 * S.ρ ^ 2) / ((n : ℝ) * n)) +
      (((-1 : ℚ) : ℝ) * (S.pairs ((P.g il : ℝ) ^ 2 * S.ρ ^ 2) / ((n : ℝ) * n)) +
      (((-1 : ℚ) : ℝ) * (S.pairs ((P.g igs : ℝ) ^ 2 * S.ρ ^ 2) / ((n : ℝ) * n)) +
      (((-6 : ℚ) : ℝ) * (S.D / n) + (((-2 : ℚ) : ℝ) * (1 / n) + 0)))) =
      (S.pairs ((P.g ig2 : ℝ) ^ 2 * S.ρ ^ 2) - S.pairs ((P.g il : ℝ) ^ 2 * S.ρ ^ 2)
        - S.pairs ((P.g igs : ℝ) ^ 2 * S.ρ ^ 2) - 6 * S.D * n - 2 * n) / ((n : ℝ) * n) := by
    push_cast
    field_simp
    ring
  rw [e, div_le_iff₀ hnn]
  push_cast
  linarith

end Esgk.S4
