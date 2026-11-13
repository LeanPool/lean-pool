/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4RowBuilder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Soundness of the apex-band rows of the `1/40` certificate

Theorem S4 of `docs/results/explicit-constant-gain-1-40-2026-10-21.md` uses the rows of
Lemma AB (apex bands, `docs/results/explicit-constant-gain-2-89-2026-10-20.md` §2). This file
proves that every rational row built by `Params.rowAB1`, `Params.rowAB2`, `Params.rowAB3`,
`Params.rowAB4`, `Params.rowAB6u` and `Params.rowAB6v` of `Esgk.S4RowBuilder` holds at the
normalized variables `val P S` of a configuration `S` (the rows AB6u and AB6v in the case
`yMean ≤ Y_hi`). Each proof reads the side conditions off the builder, casts them to `ℝ` and
applies the count-form lemma of `Esgk.BandTriples` (the row times `n²`) with `c` the centroid,
`ρ` the annulus radius and `σ = sBar`.

A chain of bands `b₀, …, b₀ + m - 1` (`Params.chain`) has the squared edges
`E j = g(bLo(b₀ + j))²` for `j < m` and `E m = g(bHi(b₀ + m - 1))²` (`Params.bandEdge`):
band `b₀ + j` is the band `(E j, E (j + 1)]` at the threshold `g(bLam b₀)²`
(`Params.bandTri_chain`), and the edges are nondecreasing (`Params.bandEdge_mono`).
-/

@[expose] public section

namespace Esgk.S4

open Finset

/-! ### Rows of a list of entries -/

/-- The left-hand side of a row whose entries are a concatenation. -/
private theorem lhs_append (A B : List (Nat × ℚ)) (rhs : ℚ) (v : Nat → ℝ) :
    QRow.lhs ⟨A ++ B, rhs⟩ v = QRow.lhs ⟨A, rhs⟩ v + QRow.lhs ⟨B, rhs⟩ v := by
  simp [QRow.lhs, List.map_append, List.sum_append]

/-- The left-hand side of the band entries `(sel (b₀ + j), q)`, `j < m`, at `v` is
`∑_{j < m} q v(sel (b₀ + j))`. -/
theorem QRow.lhs_bandEnt (sel : Nat → Nat) (q : ℚ) (b0 m : Nat) (rhs : ℚ) (v : Nat → ℝ) :
    QRow.lhs ⟨Params.bandEnt sel q b0 m, rhs⟩ v =
      ∑ j ∈ range m, (q : ℝ) * v (sel (b0 + j)) := by
  induction m with
  | zero => simp [QRow.lhs, Params.bandEnt]
  | succ m ih =>
    unfold QRow.lhs at ih ⊢
    simp only [Params.bandEnt, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero] at ih ⊢
    rw [ih, Finset.sum_range_succ]

/-- A builder `if c then some x else none` that returns `some r` has `c` and `x = r`. -/
private theorem of_ite_eq_some {c : Prop} [Decidable c] {x r : QRow}
    (h : (if c then some x else none) = some r) : c ∧ x = r := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h
    exact ⟨hc, Option.some.inj h⟩
  · rw [ite_eq_right hc] at h
    exact absurd h (by simp)

/-! ### Casts of the side conditions -/

/-- The cast of a squared grid point. -/
private theorem sq_cast (P : Params) (i : Nat) : ((P.sq i : ℚ) : ℝ) = (P.g i : ℝ) ^ 2 := by
  rw [Params.sq, Rat.cast_mul, sq]

/-- The cast of `max x 0`. -/
private theorem posPartQ_cast (x : ℚ) : ((Params.posPartQ x : ℚ) : ℝ) = max (x : ℝ) 0 := by
  unfold Params.posPartQ
  rcases le_or_gt x 0 with hx | hx
  · rw [decide_eq_true hx, Bool.cond_true, Rat.cast_zero, max_eq_right (by exact_mod_cast hx)]
  · rw [decide_eq_false (not_le.mpr hx), Bool.cond_false, max_eq_left (by exact_mod_cast hx.le)]

/-- Step L0 at the squared threshold `l`, cast to `ℝ`. -/
private theorem stepL0_cast {l : ℚ} (h : Params.stepL0 l = true) :
    (1 - (sig : ℝ) ^ 2) * ((sig : ℝ) + 1) ≤ (sig : ℝ) * (l : ℝ) := by
  have h' := (Rat.cast_le (K := ℝ)).mpr (of_decide_eq_true h)
  push_cast at h'
  linarith

/-- `0 < sBar`. -/
private theorem sig_pos : (0 : ℝ) < (sig : ℝ) := by
  rw [Setting.sig_cast]
  norm_num

/-- `R(t) ≤ D`. -/
private theorem pal_le_D {n : ℕ} (S : Setting n) (t : ℝ) : S.pal t ≤ S.D := by
  unfold Setting.pal Setting.D NumDistancesOrdered
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-! ### Chains of bands -/

/-- The squared band edges of the chain of bands `b₀, …, b₀ + m - 1`: `E j = g(bLo(b₀ + j))²`
for `j < m`, and `E j = g(bHi(b₀ + m - 1))²` for `j ≥ m` (the upper edge `E m`). -/
noncomputable def Params.bandEdge (P : Params) (b0 m j : Nat) : ℝ :=
  if j < m then (P.g (P.bLo (b0 + j)) : ℝ) ^ 2 else (P.g (P.bHi (b0 + m - 1)) : ℝ) ^ 2

/-- The conditions of a chain of bands, band by band. -/
private theorem chain_spec (P : Params) (b0 : Nat) : ∀ m, P.chain b0 m = true → ∀ k < m,
    P.bLam (b0 + k) = P.bLam b0 ∧ P.sq (P.bLo (b0 + k)) ≤ P.sq (P.bHi (b0 + k)) ∧
      (k = 0 ∨ P.bHi (b0 + k - 1) = P.bLo (b0 + k))
  | 0, _ => fun k hk ↦ absurd hk (Nat.not_lt_zero k)
  | m + 1, h => by
    simp only [Params.chain, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨⟨hc, hl⟩, hs⟩, he⟩ := h
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact chain_spec P b0 m hc k hk
    · refine ⟨Nat.eq_of_beq_eq_true hl, of_decide_eq_true hs, ?_⟩
      rcases he with he | he
      · exact Or.inl (Nat.eq_of_beq_eq_true he)
      · exact Or.inr (Nat.eq_of_beq_eq_true he)

/-- The lower edge of band `b₀ + j` of a chain. -/
private theorem bandEdge_of_lt (P : Params) {b0 m j : Nat} (hj : j < m) :
    P.bandEdge b0 m j = (P.g (P.bLo (b0 + j)) : ℝ) ^ 2 := by
  rw [Params.bandEdge, ite_eq_left hj]

/-- The upper edge of band `b₀ + j` of a chain. -/
private theorem bandEdge_succ (P : Params) {b0 m j : Nat} (h : P.chain b0 m = true)
    (hj : j < m) : P.bandEdge b0 m (j + 1) = (P.g (P.bHi (b0 + j)) : ℝ) ^ 2 := by
  by_cases hj1 : j + 1 < m
  · rw [bandEdge_of_lt P hj1]
    rcases (chain_spec P b0 m h (j + 1) hj1).2.2 with h0 | he
    · omega
    · rw [← he, show b0 + (j + 1) - 1 = b0 + j by omega]
  · rw [Params.bandEdge, ite_eq_right hj1, show b0 + m - 1 = b0 + j by omega]

/-- The bands of a chain `b₀, …, b₀ + m - 1`: band `b₀ + j` (`j < m`) is the band
`(E j, E (j + 1)]` of the squared edges `E = Params.bandEdge P b₀ m`, at the squared threshold
`g(bLam b₀)²` of `b₀`. -/
theorem Params.bandTri_chain {n : ℕ} (P : Params) (S : Setting n) {b0 m : Nat}
    (h : P.chain b0 m = true) {j : Nat} (hj : j < m) :
    S.bandTri P (b0 + j) = apexBandTriples S.p S.ρ ((P.g (P.bLam b0) : ℝ) ^ 2)
      (P.bandEdge b0 m j) (P.bandEdge b0 m (j + 1)) := by
  rw [bandEdge_of_lt P hj, bandEdge_succ P h hj, Setting.bandTri,
    (chain_spec P b0 m h j hj).1]

/-- The squared edges of a chain of bands are nondecreasing: `E j ≤ E (j + 1)` for `j < m`. -/
theorem Params.bandEdge_mono (P : Params) {b0 m : Nat} (h : P.chain b0 m = true) :
    ∀ j < m, P.bandEdge b0 m j ≤ P.bandEdge b0 m (j + 1) := by
  intro j hj
  rw [bandEdge_of_lt P hj, bandEdge_succ P h hj, ← sq_cast, ← sq_cast]
  exact_mod_cast (chain_spec P b0 m h j hj).2.1

/-! ### Rows AB1 and AB2 -/

/-- Soundness of row AB1 of Lemma AB (`sum_card_apexBandTriples_ge`, the row times `n²`): over
a chain of bands `b₀, …, b₀ + m - 1` at the threshold `λ = g(bLam b₀)` with `4e₀² ≤ λ²` and
`4 ≤ e_m²`, `-2𝒜(λ) - 6 D/n - 4/n - ∑ⱼ W_{b₀+j} ≤ -4`. -/
theorem Params.rowAB1_sound {n : ℕ} (P : Params) (S : Setting n) {b0 m : Nat} {r : QRow}
    (h : P.rowAB1 b0 m = some r) : r.Holds (val P S) := by
  unfold Params.rowAB1 at h
  obtain ⟨hc, rfl⟩ := of_ite_eq_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Params.ok, Params.okB, Nat.blt_eq] at hc
  obtain ⟨⟨⟨⟨⟨hm, -⟩, hch⟩, hlam⟩, hE0⟩, hEm⟩ := hc
  have hN : (0 : ℝ) < n := by exact_mod_cast S.n_pos
  have hN0 : (n : ℝ) ≠ 0 := hN.ne'
  have hE0' : 4 * P.bandEdge b0 m 0 ≤ (P.g (P.bLam b0) : ℝ) ^ 2 := by
    rw [bandEdge_of_lt P hm, Nat.add_zero, ← sq_cast, ← sq_cast]
    exact_mod_cast hE0
  have hEm' : 4 ≤ P.bandEdge b0 m m := by
    rw [Params.bandEdge, ite_eq_right (lt_irrefl m), ← sq_cast]
    exact_mod_cast hEm
  have key := sum_card_apexBandTriples_ge (c := S.c) (E := P.bandEdge b0 m) S.hp S.hgp.1
    S.hρ S.hhi (sq_nonneg _) hE0' hEm'
  have hsum : ∑ j ∈ range m, ((S.bandTri P (b0 + j)).card : ℝ) =
      ∑ j ∈ range m, ((apexBandTriples S.p S.ρ ((P.g (P.bLam b0) : ℝ) ^ 2)
        (P.bandEdge b0 m j) (P.bandEdge b0 m (j + 1))).card : ℝ) :=
    Finset.sum_congr rfl fun j hj ↦ by rw [P.bandTri_chain S hch (Finset.mem_range.mp hj)]
  rw [← hsum] at key
  change 2 * ((n : ℝ) * n - n - S.pairs ((P.g (P.bLam b0) : ℝ) ^ 2 * S.ρ ^ 2)) -
      2 * (n : ℝ) * (3 * S.D - (n : ℝ) + 1) ≤ _ at key
  unfold QRow.Holds
  rw [lhs_append, QRow.lhs_bandEnt]
  simp only [QRow.lhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [val_aVar P S hlam, val_dV, val_eV]
  simp only [val_wV]
  push_cast
  rw [← Finset.mul_sum, ← Finset.sum_div]
  rw [← sub_nonpos]
  have hNN : (0 : ℝ) < (n : ℝ) * n := by positivity
  calc _ = (-2 * S.pairs ((P.g (P.bLam b0) : ℝ) ^ 2 * S.ρ ^ 2) - 6 * S.D * n - 4 * n -
        ∑ j ∈ range m, ((S.bandTri P (b0 + j)).card : ℝ) + 4 * ((n : ℝ) * n)) /
          ((n : ℝ) * n) := by
        field_simp
        ring
    _ ≤ 0 := by
        rw [div_le_iff₀ hNN, zero_mul]
        linarith

/-- Soundness of row AB2 of Lemma AB (`card_apexBandTriples_le_window`, the row times `n²`):
under Step L0 at `λ = g(bLam b)` and `e_lo ≤ e_hi`,
`W_b - (4/3) 𝒜(e_hi) + (4/3) 𝒜(e_lo) ≤ 0`. -/
theorem Params.rowAB2_sound {n : ℕ} (P : Params) (S : Setting n) {b : Nat} {r : QRow}
    (h : P.rowAB2 b = some r) : r.Holds (val P S) := by
  unfold Params.rowAB2 at h
  obtain ⟨hc, rfl⟩ := of_ite_eq_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Params.ok, Params.okB, Nat.blt_eq] at hc
  obtain ⟨⟨⟨⟨-, hlo⟩, hhi⟩, hL0⟩, hE⟩ := hc
  have hN : (0 : ℝ) < n := by exact_mod_cast S.n_pos
  have hNN : (0 : ℝ) < (n : ℝ) * n := by positivity
  have hchord := stepL0_cast hL0
  rw [sq_cast] at hchord
  have hE' : (P.g (P.bLo b) : ℝ) ^ 2 ≤ (P.g (P.bHi b) : ℝ) ^ 2 := by
    rw [← sq_cast, ← sq_cast]
    exact_mod_cast hE
  have key : ((S.bandTri P b).card : ℝ) ≤
      4 / 3 * (S.pairs ((P.g (P.bHi b) : ℝ) ^ 2 * S.ρ ^ 2) -
        S.pairs ((P.g (P.bLo b) : ℝ) ^ 2 * S.ρ ^ 2)) :=
    card_apexBandTriples_le_window S.hcap S.hρ sig_pos hchord S.hlo S.hhi hE'
  unfold QRow.Holds
  simp only [QRow.lhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [val_wV, val_aVar P S hlo, val_aVar P S hhi]
  push_cast
  calc _ = (((S.bandTri P b).card : ℝ) - 4 / 3 * (S.pairs ((P.g (P.bHi b) : ℝ) ^ 2 * S.ρ ^ 2) -
        S.pairs ((P.g (P.bLo b) : ℝ) ^ 2 * S.ρ ^ 2))) / ((n : ℝ) * n) := by ring
    _ ≤ 0 := by
        rw [div_le_iff₀ hNN, zero_mul]
        linarith

/-! ### Rows AB3 and AB4 -/

/-- Soundness of row AB3 of Lemma AB (`lower_edge_mul_card_apexBandTriples_le`, the row times
`n²`): for `t > 0`, with `K⁺ = (4 + t)sBar² + (4sBar² - λ²)/t`,
`(2e_lo² - K⁺) W_b - (1 + 2/t) U_b - (2 + t) V_b ≤ 0`. -/
theorem Params.rowAB3_sound {n : ℕ} (P : Params) (S : Setting n) {b tn td : Nat} {r : QRow}
    (h : P.rowAB3 b tn td = some r) : r.Holds (val P S) := by
  unfold Params.rowAB3 at h
  obtain ⟨hc, rfl⟩ := of_ite_eq_some h
  generalize mkRat tn td = t at hc ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨-, ht⟩ := hc
  have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hN : (0 : ℝ) < n := by exact_mod_cast S.n_pos
  have hNN : (0 : ℝ) < (n : ℝ) * n := by positivity
  have key : (2 * (P.g (P.bLo b) : ℝ) ^ 2 - ((4 + (t : ℝ)) * (sig : ℝ) ^ 2 +
      (4 * (sig : ℝ) ^ 2 - (P.g (P.bLam b) : ℝ) ^ 2) / (t : ℝ))) *
        ((S.bandTri P b).card : ℝ) ≤
      (1 + 2 / (t : ℝ)) * ∑ x ∈ S.bandTri P b, (S.y x.2.1 + S.y x.2.2) +
        (2 + (t : ℝ)) * ∑ x ∈ S.bandTri P b, S.y x.1 :=
    lower_edge_mul_card_apexBandTriples_le S.hρ ht'
  unfold QRow.Holds
  simp only [QRow.lhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [val_wV, val_uV, val_vV]
  push_cast [sq_cast]
  calc _ = ((2 * (P.g (P.bLo b) : ℝ) ^ 2 - ((4 + (t : ℝ)) * (sig : ℝ) ^ 2 +
      (4 * (sig : ℝ) ^ 2 - (P.g (P.bLam b) : ℝ) ^ 2) / (t : ℝ))) *
        ((S.bandTri P b).card : ℝ) -
      ((1 + 2 / (t : ℝ)) * ∑ x ∈ S.bandTri P b, (S.y x.2.1 + S.y x.2.2) +
        (2 + (t : ℝ)) * ∑ x ∈ S.bandTri P b, S.y x.1)) / ((n : ℝ) * n) := by ring
    _ ≤ 0 := by
        rw [div_le_iff₀ hNN, zero_mul]
        linarith

/-- Soundness of row AB4 of Lemma AB (`upper_edge_mul_card_apexBandTriples_le`, the row times
`n²`): for `t > 0`, with `K⁻ = (4 - t)sBar² - (4sBar² - λ²)/t`,
`(K⁻ - 2e_hi²) W_b - max(2/t - 1, 0) U_b - max(t - 2, 0) V_b ≤ 0`. -/
theorem Params.rowAB4_sound {n : ℕ} (P : Params) (S : Setting n) {b tn td : Nat} {r : QRow}
    (h : P.rowAB4 b tn td = some r) : r.Holds (val P S) := by
  unfold Params.rowAB4 at h
  obtain ⟨hc, rfl⟩ := of_ite_eq_some h
  generalize mkRat tn td = t at hc ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨-, ht⟩ := hc
  have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hN : (0 : ℝ) < n := by exact_mod_cast S.n_pos
  have hNN : (0 : ℝ) < (n : ℝ) * n := by positivity
  have key : ((4 - (t : ℝ)) * (sig : ℝ) ^ 2 - (4 * (sig : ℝ) ^ 2 - (P.g (P.bLam b) : ℝ) ^ 2) /
      (t : ℝ) - 2 * (P.g (P.bHi b) : ℝ) ^ 2) * ((S.bandTri P b).card : ℝ) ≤
      max (2 / (t : ℝ) - 1) 0 * ∑ x ∈ S.bandTri P b, (S.y x.2.1 + S.y x.2.2) +
        max ((t : ℝ) - 2) 0 * ∑ x ∈ S.bandTri P b, S.y x.1 :=
    upper_edge_mul_card_apexBandTriples_le S.hρ ht' S.hlo
  unfold QRow.Holds
  simp only [QRow.lhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [val_wV, val_uV, val_vV]
  simp only [Rat.cast_neg, posPartQ_cast]
  push_cast [sq_cast]
  calc _ = (((4 - (t : ℝ)) * (sig : ℝ) ^ 2 - (4 * (sig : ℝ) ^ 2 - (P.g (P.bLam b) : ℝ) ^ 2) /
      (t : ℝ) - 2 * (P.g (P.bHi b) : ℝ) ^ 2) * ((S.bandTri P b).card : ℝ) -
      (max (2 / (t : ℝ) - 1) 0 * ∑ x ∈ S.bandTri P b, (S.y x.2.1 + S.y x.2.2) +
        max ((t : ℝ) - 2) 0 * ∑ x ∈ S.bandTri P b, S.y x.1)) / ((n : ℝ) * n) := by ring
    _ ≤ 0 := by
        rw [div_le_iff₀ hNN, zero_mul]
        linarith

/-! ### Rows AB6 -/

/-- Soundness of row AB6u of Lemma AB (`sum_bands_base_excess_le_far_palette`, the row times
`n²`) in the case `yMean ≤ Y_hi`: over a chain of bands `b₀, …, b₀ + m - 1` at the threshold
`λ = g(bLam b₀)`, `∑ⱼ U_{b₀+j} - 12 Y_hi D/n + 12 Y_hi ℛ(λ) ≤ 0`. -/
theorem Params.rowAB6u_sound {n : ℕ} (P : Params) (S : Setting n) {Yhi : ℚ} {b0 m : Nat}
    {r : QRow} (h : P.rowAB6u Yhi b0 m = some r) (hy : S.ybar ≤ (Yhi : ℝ)) :
    r.Holds (val P S) := by
  unfold Params.rowAB6u at h
  obtain ⟨hc, rfl⟩ := of_ite_eq_some h
  simp only [Bool.and_eq_true, Params.ok, Nat.blt_eq] at hc
  obtain ⟨⟨⟨-, -⟩, hch⟩, hlam⟩ := hc
  have hN : (0 : ℝ) < n := by exact_mod_cast S.n_pos
  have hN0 : (n : ℝ) ≠ 0 := hN.ne'
  have hNN : (0 : ℝ) < (n : ℝ) * n := by positivity
  have key := sum_bands_base_excess_le_far_palette (c := S.c) (σ := (sig : ℝ))
    (Λ := (P.g (P.bLam b0) : ℝ) ^ 2) (E := P.bandEdge b0 m) S.hp S.hgp.1 S.hcap S.hρ S.hlo
    (P.bandEdge_mono hch)
  have hsum : ∑ j ∈ range m, ∑ x ∈ S.bandTri P (b0 + j), (S.y x.2.1 + S.y x.2.2) =
      ∑ j ∈ range m, ∑ x ∈ apexBandTriples S.p S.ρ ((P.g (P.bLam b0) : ℝ) ^ 2)
        (P.bandEdge b0 m j) (P.bandEdge b0 m (j + 1)),
          (radialExcess S.p S.c S.ρ (sig : ℝ) x.2.1 + radialExcess S.p S.c S.ρ (sig : ℝ) x.2.2) :=
    Finset.sum_congr rfl fun j hj ↦ by rw [P.bandTri_chain S hch (Finset.mem_range.mp hj)]; rfl
  rw [← hsum] at key
  change _ ≤ 12 * (∑ i, S.y i) * (S.D - S.pal ((P.g (P.bLam b0) : ℝ) ^ 2 * S.ρ ^ 2)) at key
  have hSy : ∑ i, S.y i ≤ (Yhi : ℝ) * n := by
    rw [Setting.ybar, div_le_iff₀ hN] at hy
    exact hy
  have hDR : 0 ≤ S.D - S.pal ((P.g (P.bLam b0) : ℝ) ^ 2 * S.ρ ^ 2) :=
    sub_nonneg.mpr (pal_le_D S _)
  have hmul := mul_le_mul_of_nonneg_right hSy hDR
  unfold QRow.Holds
  rw [lhs_append, QRow.lhs_bandEnt]
  simp only [QRow.lhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [val_dV, val_rVar P S hlam]
  simp only [val_uV]
  push_cast
  simp only [one_mul]
  rw [← Finset.sum_div]
  calc _ = (∑ j ∈ range m, ∑ x ∈ S.bandTri P (b0 + j), (S.y x.2.1 + S.y x.2.2) -
        12 * (Yhi : ℝ) * n * (S.D - S.pal ((P.g (P.bLam b0) : ℝ) ^ 2 * S.ρ ^ 2))) /
          ((n : ℝ) * n) := by
        field_simp
        ring
    _ ≤ 0 := by
        rw [div_le_iff₀ hNN, zero_mul]
        linarith

/-- Soundness of row AB6v of Lemma AB (`sum_bands_apex_excess_le_far_palette`, the row times
`n²`) in the case `yMean ≤ Y_hi`: over a chain of bands `b₀, …, b₀ + m - 1` at the threshold
`λ = g(bLam b₀)` with Step L0 at `λ` and `4h² ≤ λ²` for `h = g_ih`,
`∑ⱼ V_{b₀+j} - 4 Y_hi D/n + 4 Y_hi ℛ(h) ≤ 0`. -/
theorem Params.rowAB6v_sound {n : ℕ} (P : Params) (S : Setting n) {Yhi : ℚ} {b0 m ih : Nat}
    {r : QRow} (h : P.rowAB6v Yhi b0 m ih = some r) (hy : S.ybar ≤ (Yhi : ℝ)) :
    r.Holds (val P S) := by
  unfold Params.rowAB6v at h
  obtain ⟨hc, rfl⟩ := of_ite_eq_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Params.ok, Nat.blt_eq] at hc
  obtain ⟨⟨⟨⟨⟨-, -⟩, hch⟩, hih⟩, hL0⟩, hH⟩ := hc
  have hN : (0 : ℝ) < n := by exact_mod_cast S.n_pos
  have hN0 : (n : ℝ) ≠ 0 := hN.ne'
  have hNN : (0 : ℝ) < (n : ℝ) * n := by positivity
  have hchord := stepL0_cast hL0
  rw [sq_cast] at hchord
  have hH' : 4 * (P.g ih : ℝ) ^ 2 ≤ (P.g (P.bLam b0) : ℝ) ^ 2 := by
    rw [← sq_cast, ← sq_cast]
    exact_mod_cast hH
  have key := sum_bands_apex_excess_le_far_palette (c := S.c) (E := P.bandEdge b0 m) S.hcap
    S.hρ sig_pos hchord S.hlo S.hhi hH' (P.bandEdge_mono hch)
  have hsum : ∑ j ∈ range m, ∑ x ∈ S.bandTri P (b0 + j), S.y x.1 =
      ∑ j ∈ range m, ∑ x ∈ apexBandTriples S.p S.ρ ((P.g (P.bLam b0) : ℝ) ^ 2)
        (P.bandEdge b0 m j) (P.bandEdge b0 m (j + 1)),
          radialExcess S.p S.c S.ρ (sig : ℝ) x.1 :=
    Finset.sum_congr rfl fun j hj ↦ by rw [P.bandTri_chain S hch (Finset.mem_range.mp hj)]; rfl
  rw [← hsum] at key
  change _ ≤ 4 * (∑ i, S.y i) * (S.D - S.pal ((P.g ih : ℝ) ^ 2 * S.ρ ^ 2)) at key
  have hSy : ∑ i, S.y i ≤ (Yhi : ℝ) * n := by
    rw [Setting.ybar, div_le_iff₀ hN] at hy
    exact hy
  have hDR : 0 ≤ S.D - S.pal ((P.g ih : ℝ) ^ 2 * S.ρ ^ 2) := sub_nonneg.mpr (pal_le_D S _)
  have hmul := mul_le_mul_of_nonneg_right hSy hDR
  unfold QRow.Holds
  rw [lhs_append, QRow.lhs_bandEnt]
  simp only [QRow.lhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [val_dV, val_rVar P S hih]
  simp only [val_vV]
  push_cast
  simp only [one_mul]
  rw [← Finset.sum_div]
  calc _ = (∑ j ∈ range m, ∑ x ∈ S.bandTri P (b0 + j), S.y x.1 -
        4 * (Yhi : ℝ) * n * (S.D - S.pal ((P.g ih : ℝ) ^ 2 * S.ρ ^ 2))) /
          ((n : ℝ) * n) := by
        field_simp
        ring
    _ ≤ 0 := by
        rw [div_le_iff₀ hNN, zero_mul]
        linarith

end Esgk.S4
