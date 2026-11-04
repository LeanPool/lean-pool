/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4RowBuilder
public import LeanPool.DistinctDistances.ShortChainRowFacts
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Soundness of the basic rows and of the box of the `1/40` certificate

Theorem S4 of `docs/results/explicit-constant-gain-1-40-2026-10-21.md` is proved by an
exact-rational certificate over the normalized variables `val P S` of `Esgk.S4RowBuilder`:
`𝒜(g) = P(g²ρ²)/n²`, `ℛ(g) = R(g²ρ²)/n`, `D/n`, `1/n` and the band variables `W, U, V` of
Lemma AB. This file proves that the rows of the five basic families hold at `val P S`
whenever their builder returns a row, and that `val P S` lies in the box `P.box`:

* `Params.rowAmono_sound`: `𝒜(gᵢ) ≤ 𝒜(gⱼ)` for `gᵢ² ≤ gⱼ²` (the close-pair count is
  nondecreasing);
* `Params.rowXmono_sound`: `3ℛ - 𝒜` is nondecreasing from `gᵢ` to `gⱼ` (degree cap three);
* `Params.rowXpos_sound`: `𝒜(gᵢ) ≤ 3ℛ(gᵢ)` (degree cap three);
* `Params.rowXleq_sound`: `3ℛ(gᵢ) - 𝒜(gᵢ) - 3 D/n - 1/n ≤ -1`, that is `3ℛ - 𝒜 ≤ 𝔮` with
  `𝔮 = 3 D/n - 1 + 1/n` (row bound (B1), lower side, summed over the points);
* `Params.rowA2lo_sound`: `-𝒜(gᵢ) - 1/n ≤ -1` for `gᵢ² ≥ 4` (every pair is within squared
  distance `4ρ²`);
* `Params.box_sound`: the box `𝒜 ∈ [0, 1]`, `ℛ ∈ [0, dMean]`, `D/n ∈ [1/3 - ε/3, dMean]`,
  `1/n ∈ [0, ε]`, `W ∈ [0, 2]`, `U, V ∈ [0, 4]`.

Each row is proved from its count form (the row times `n²`) and divided by `n²`.
-/

@[expose] public section

namespace Esgk.S4

open Finset EuclideanGeometry Esgk.FarkasPackedCheck

variable {n : ℕ}

/-! ### Casts and scaling -/

private theorem sq_cast (P : Params) (i : Nat) : ((P.sq i : ℚ) : ℝ) = (P.g i : ℝ) ^ 2 := by
  simp [Params.sq, sq]

/-- A rational comparison of squared grid points gives the comparison of the thresholds. -/
private theorem thr_le {P : Params} {i j : Nat} (h : P.sq i ≤ P.sq j) (ρ : ℝ) :
    (P.g i : ℝ) ^ 2 * ρ ^ 2 ≤ (P.g j : ℝ) ^ 2 * ρ ^ 2 := by
  have h' : ((P.sq i : ℚ) : ℝ) ≤ ((P.sq j : ℚ) : ℝ) := by exact_mod_cast h
  rw [sq_cast, sq_cast] at h'
  exact mul_le_mul_of_nonneg_right h' (sq_nonneg ρ)

private theorem thr_nonneg (P : Params) (i : Nat) (ρ : ℝ) : 0 ≤ (P.g i : ℝ) ^ 2 * ρ ^ 2 := by
  positivity

private theorem nR_pos (S : Setting n) : (0 : ℝ) < n := by exact_mod_cast S.n_pos

private theorem nnR_pos (S : Setting n) : (0 : ℝ) < (n : ℝ) * n := by
  have := nR_pos S
  positivity

/-- The variable `𝒜(gᵢ)` times `n²` is the close-pair count `P(gᵢ²ρ²)`. -/
private theorem aVar_mul (P : Params) (S : Setting n) {i : Nat} (hi : i < P.ng) :
    val P S (aVar i) * ((n : ℝ) * n) = S.pairs ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) := by
  rw [val_aVar P S hi, div_mul_cancel₀ _ (nnR_pos S).ne']

/-- The variable `ℛ(gᵢ)` times `n²` is `n R(gᵢ²ρ²)`. -/
private theorem rVar_mul (P : Params) (S : Setting n) {i : Nat} (hi : i < P.ng) :
    val P S (rVar i) * ((n : ℝ) * n) = n * S.pal ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) := by
  have := nR_pos S
  rw [val_rVar P S hi]
  field_simp

/-- The variable `D/n` times `n²` is `n D`. -/
private theorem dV_mul (P : Params) (S : Setting n) :
    val P S P.dV * ((n : ℝ) * n) = n * S.D := by
  have := nR_pos S
  rw [val_dV P S]
  field_simp

/-- The variable `1/n` times `n²` is `n`. -/
private theorem eV_mul (P : Params) (S : Setting n) :
    val P S P.eV * ((n : ℝ) * n) = n := by
  have := nR_pos S
  rw [val_eV P S]
  field_simp

private theorem ok_lt {P : Params} {i : Nat} (h : P.ok i = true) : i < P.ng := by
  rwa [Params.ok, Nat.blt_eq] at h

/-! ### The basic rows -/

/-- Soundness of the row `𝒜(gᵢ) ≤ 𝒜(gⱼ)` (for `gᵢ² ≤ gⱼ²`): the close-pair count
`P(t) = Σ_j (N_j(t) - 1)` is nondecreasing in the squared threshold; the row times `n²` is
`P(gᵢ²ρ²) ≤ P(gⱼ²ρ²)`. -/
theorem Params.rowAmono_sound (P : Params) (S : Setting n) {i j : Nat} {r : QRow}
    (h : P.rowAmono i j = some r) : r.Holds (val P S) := by
  unfold Params.rowAmono at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hi, hj⟩, hij⟩ := hc
  cases h
  unfold QRow.Holds QRow.lhs
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  have hm : S.pairs ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) ≤ S.pairs ((P.g j : ℝ) ^ 2 * S.ρ ^ 2) :=
    sum_closedBall_sq_card_sub_one_mono S.p (thr_le hij S.ρ)
  refine le_of_mul_le_mul_right ?_ (nnR_pos S)
  linarith [aVar_mul P S (ok_lt hi), aVar_mul P S (ok_lt hj)]

/-- Soundness of the row `3ℛ(gᵢ) - 𝒜(gᵢ) ≤ 3ℛ(gⱼ) - 𝒜(gⱼ)` (for `gᵢ² ≤ gⱼ²`): with the
degree cap three, `P(gⱼ²ρ²) - P(gᵢ²ρ²) ≤ n · 3(R(gⱼ²ρ²) - R(gᵢ²ρ²))`, which is the row times
`n²`. -/
theorem Params.rowXmono_sound (P : Params) (S : Setting n) {i j : Nat} {r : QRow}
    (h : P.rowXmono i j = some r) : r.Holds (val P S) := by
  unfold Params.rowXmono at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hi, hj⟩, hij⟩ := hc
  cases h
  unfold QRow.Holds QRow.lhs
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  have hm : S.pairs ((P.g j : ℝ) ^ 2 * S.ρ ^ 2) - S.pairs ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) ≤
      (n : ℝ) * (3 * (S.pal ((P.g j : ℝ) ^ 2 * S.ρ ^ 2) - S.pal ((P.g i : ℝ) ^ 2 * S.ρ ^ 2))) :=
    sum_closedBall_sq_card_sub_one_sub_le_three_mul_palette_sub S.hcap (thr_nonneg P i S.ρ)
      (thr_le hij S.ρ)
  refine le_of_mul_le_mul_right ?_ (nnR_pos S)
  linarith [aVar_mul P S (ok_lt hi), aVar_mul P S (ok_lt hj), rVar_mul P S (ok_lt hi),
    rVar_mul P S (ok_lt hj)]

/-- Soundness of the row `𝒜(gᵢ) ≤ 3ℛ(gᵢ)`: with the degree cap three,
`P(gᵢ²ρ²) ≤ n · 3R(gᵢ²ρ²)`, which is the row times `n²`. -/
theorem Params.rowXpos_sound (P : Params) (S : Setting n) {i : Nat} {r : QRow}
    (h : P.rowXpos i = some r) : r.Holds (val P S) := by
  unfold Params.rowXpos at h
  split_ifs at h with hi
  cases h
  unfold QRow.Holds QRow.lhs
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  have hm : S.pairs ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) ≤
      (n : ℝ) * (3 * S.pal ((P.g i : ℝ) ^ 2 * S.ρ ^ 2)) :=
    sum_closedBall_sq_card_sub_one_le_three_mul_palette S.hcap (thr_nonneg P i S.ρ)
  refine le_of_mul_le_mul_right ?_ (nnR_pos S)
  linarith [aVar_mul P S (ok_lt hi), rVar_mul P S (ok_lt hi)]

/-- Soundness of the row `3ℛ(gᵢ) - 𝒜(gᵢ) - 3 D/n - 1/n ≤ -1` (that is, `3ℛ - 𝒜 ≤ 𝔮`): with
the degree cap three, every closed ball of squared radius `gᵢ²ρ²` holds at least
`3R(gᵢ²ρ²) - (3D - n + 1)` points other than its center; summed over the centers this is
`n (3R(gᵢ²ρ²) - (3D - n + 1)) ≤ P(gᵢ²ρ²)`, the row times `n²`. -/
theorem Params.rowXleq_sound (P : Params) (S : Setting n) {i : Nat} {r : QRow}
    (h : P.rowXleq i = some r) : r.Holds (val P S) := by
  unfold Params.rowXleq at h
  split_ifs at h with hi
  cases h
  unfold QRow.Holds QRow.lhs
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  have hs := Finset.sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin n))) ↦
    three_mul_palette_sub_le_closedBall_sq_card_sub_one S.n_pos S.hcap (thr_nonneg P i S.ρ) j
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hm : (n : ℝ) * (3 * S.pal ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) - (3 * S.D - (n : ℝ) + 1)) ≤
      S.pairs ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) := hs
  refine le_of_mul_le_mul_right ?_ (nnR_pos S)
  linarith [aVar_mul P S (ok_lt hi), rVar_mul P S (ok_lt hi), dV_mul P S, eV_mul P S]

/-- Soundness of the row `-𝒜(gᵢ) - 1/n ≤ -1` (for `gᵢ² ≥ 4`): with the degree cap three every
pair is within squared distance `4ρ²`, so `n² - n ≤ P(gᵢ²ρ²)`, the row times `n²`. -/
theorem Params.rowA2lo_sound (P : Params) (S : Setting n) {i : Nat} {r : QRow}
    (h : P.rowA2lo i = some r) : r.Holds (val P S) := by
  unfold Params.rowA2lo at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hi, h4⟩ := hc
  cases h
  unfold QRow.Holds QRow.lhs
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  have h4' : (4 : ℝ) ≤ (P.g i : ℝ) ^ 2 := by
    rw [← sq_cast]
    exact_mod_cast h4
  have hm : (n : ℝ) * n - n ≤ S.pairs ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) :=
    mul_self_sub_le_sum_closedBall_sq_card_sub_one_of_four_le S.hcap S.hρsq h4'
  refine le_of_mul_le_mul_right ?_ (nnR_pos S)
  linarith [aVar_mul P S (ok_lt hi), eV_mul P S]

/-! ### The box -/

private theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem beq_true {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  rw [Nat.beq_eq]
  exact h

private theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

private theorem blt_false {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · rw [Nat.blt_eq] at hb
    exact absurd hb h

/-- The box of the certificate holds at the normalized variables: `𝒜 ∈ [0, 1]` (the
close-pair count is between `0` and `n² - n`), `ℛ ∈ [0, dMean]` (`R ≤ D ≤ dMean n`),
`D/n ∈ [1/3 - ε/3, dMean]` (`n ≤ 3D` and the contradiction hypothesis), `1/n ∈ [0, ε]`
(`n ≥ 10⁴`), `W ∈ [0, 2]` (at most two equidistant witnesses per ordered pair),
`U ∈ [0, 4]` and `V ∈ [0, 4]` (the radial excesses lie in `[0, 1 - sBar²]`). This is the
hypothesis `hbox` of `FarkasPackedCheck.check_sound`. -/
theorem Params.box_sound {n : ℕ} (P : Params) (S : Setting n) :
    ∀ k < P.box.nv, ((P.box.lo k : ℚ) : ℝ) ≤ val P S k ∧ val P S k ≤ ((P.box.hi k : ℚ) : ℝ) := by
  intro k hk
  have hk' : k < 2 * P.ng + 2 + 3 * P.nb := hk
  have hn := nR_pos S
  have hN := nnR_pos S
  have hnR := S.hnR
  rcases lt_or_ge k (2 * P.ng) with hlt | hge
  · obtain ⟨i, rfl | rfl⟩ : ∃ i, k = 2 * i ∨ k = 2 * i + 1 := ⟨k / 2, by omega⟩
    · -- `𝒜(gᵢ) ∈ [0, 1]`
      have hi : i < P.ng := by omega
      have e : val P S (2 * i) = S.pairs ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) / ((n : ℝ) * n) :=
        val_aVar P S hi
      have hlo : P.box.lo (2 * i) = 0 := by
        simp only [Params.box, beq_false (show 2 * i ≠ 2 * P.ng by omega), Bool.cond_false]
      have hhi : P.box.hi (2 * i) = 1 := by
        simp only [Params.box, blt_true hlt, beq_true (show 2 * i % 2 = 0 by omega), Bool.cond_true]
      have h0 : 0 ≤ S.pairs ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) :=
        sum_closedBall_sq_card_sub_one_nonneg S.p (thr_nonneg P i S.ρ)
      have h1 : S.pairs ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) ≤ (n : ℝ) * n - n :=
        sum_closedBall_sq_card_sub_one_le_mul_self_sub S.p _
      rw [hlo, hhi, e]
      push_cast
      refine ⟨div_nonneg h0 hN.le, (div_le_one hN).2 (by linarith)⟩
    · -- `ℛ(gᵢ) ∈ [0, dMean]`
      have hi : i < P.ng := by omega
      have e : val P S (2 * i + 1) = S.pal ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) / n :=
        val_rVar P S hi
      have hlo : P.box.lo (2 * i + 1) = 0 := by
        simp only [Params.box, beq_false (show 2 * i + 1 ≠ 2 * P.ng by omega), Bool.cond_false]
      have hhi : P.box.hi (2 * i + 1) = dbar := by
        simp only [Params.box, blt_true hlt, beq_false (show (2 * i + 1) % 2 ≠ 0 by omega),
          Bool.cond_true, Bool.cond_false]
      have h0 : (0 : ℝ) ≤ S.pal ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) := Nat.cast_nonneg _
      have h1 : S.pal ((P.g i : ℝ) ^ 2 * S.ρ ^ 2) ≤ S.D :=
        palette_card_le_numDistancesOrdered S.p _
      have h2 := S.hD_ordered
      rw [hlo, hhi, e]
      simp only [dbar]
      push_cast
      refine ⟨div_nonneg h0 hn.le, (div_le_iff₀ hn).2 (by linarith)⟩
  · rcases eq_or_ne k (2 * P.ng) with rfl | hne
    · -- `D/n ∈ [1/3 - ε/3, dMean]`
      have hlo : P.box.lo (2 * P.ng) = 1 / 3 - eps / 3 := by
        simp only [Params.box, beq_true (rfl : 2 * P.ng = 2 * P.ng), Bool.cond_true]
      have hhi : P.box.hi (2 * P.ng) = dbar := by
        simp only [Params.box, blt_false (lt_irrefl _), beq_true (rfl : 2 * P.ng = 2 * P.ng),
          Bool.cond_true, Bool.cond_false]
      have e : val P S (2 * P.ng) = S.D / n := val_dV P S
      have h1 := S.n_le_three_D
      have h2 := S.hD_ordered
      rw [hlo, hhi, e]
      simp only [eps, dbar]
      push_cast
      refine ⟨(le_div_iff₀ hn).2 (by linarith), (div_le_iff₀ hn).2 (by linarith)⟩
    rcases eq_or_ne k (2 * P.ng + 1) with rfl | hne'
    · -- `1/n ∈ [0, ε]`
      have hlo : P.box.lo (2 * P.ng + 1) = 0 := by
        simp only [Params.box, beq_false (show 2 * P.ng + 1 ≠ 2 * P.ng by omega), Bool.cond_false]
      have hhi : P.box.hi (2 * P.ng + 1) = eps := by
        simp only [Params.box, blt_false (show ¬ 2 * P.ng + 1 < 2 * P.ng by omega),
          beq_false (show 2 * P.ng + 1 ≠ 2 * P.ng by omega),
          beq_true (rfl : 2 * P.ng + 1 = 2 * P.ng + 1), Bool.cond_true, Bool.cond_false]
      have e : val P S (2 * P.ng + 1) = 1 / n := val_eV P S
      rw [hlo, hhi, e]
      simp only [eps]
      push_cast
      refine ⟨by positivity, one_div_le_one_div_of_le (by norm_num) hnR⟩
    · -- the band variables
      have hlo : P.box.lo k = 0 := by simp only [Params.box, beq_false hne, Bool.cond_false]
      have hlt' : ¬ k < 2 * P.ng := by omega
      have e : val P S k = S.bandCount P ((k - (2 * P.ng + 2)) / 3)
          ((k - (2 * P.ng + 2)) % 3) / ((n : ℝ) * n) := by
        unfold val
        rw [ite_eq_right hlt', ite_eq_right hne, ite_eq_right hne']
      have hhi : P.box.hi k = bif Nat.beq ((k - (2 * P.ng + 2)) % 3) 0 then 2 else 4 := by
        simp only [Params.box, blt_false hlt', beq_false hne, beq_false hne', Bool.cond_false]
      rw [hlo, hhi, e]
      generalize (k - (2 * P.ng + 2)) / 3 = b
      have hr : (k - (2 * P.ng + 2)) % 3 < 3 := Nat.mod_lt _ (by norm_num)
      generalize (k - (2 * P.ng + 2)) % 3 = q at hr ⊢
      have hW0 : (0 : ℝ) ≤ ((S.bandTri P b).card : ℝ) := Nat.cast_nonneg _
      have hW : ((S.bandTri P b).card : ℝ) ≤ 2 * (n : ℝ) * n :=
        card_apexBandTriples_le_two_mul S.hp S.hgp.1 S.ρ _ _ _
      have hσ : (0 : ℝ) ≤ (sig : ℝ) ^ 2 * ((S.bandTri P b).card : ℝ) := by positivity
      interval_cases q
      · -- `W_b ∈ [0, 2]`
        have hc : S.bandCount P b 0 = ((S.bandTri P b).card : ℝ) := by
          simp [Setting.bandCount]
        rw [hc, beq_true rfl, Bool.cond_true]
        push_cast
        refine ⟨div_nonneg hW0 hN.le, (div_le_iff₀ hN).2 (by linarith)⟩
      · -- `U_b ∈ [0, 4]`
        have hc : S.bandCount P b 1 = ∑ x ∈ S.bandTri P b, (S.y x.2.1 + S.y x.2.2) := by
          simp [Setting.bandCount]
        have hU0 : 0 ≤ ∑ x ∈ S.bandTri P b, (S.y x.2.1 + S.y x.2.2) :=
          sum_apexBandTriples_base_excess_nonneg S.hρ S.hlo
        have hU : ∑ x ∈ S.bandTri P b, (S.y x.2.1 + S.y x.2.2) ≤
            2 * (1 - (sig : ℝ) ^ 2) * ((S.bandTri P b).card : ℝ) :=
          sum_apexBandTriples_base_excess_le S.hρ S.hhi
        rw [hc, beq_false (by norm_num), Bool.cond_false]
        push_cast
        refine ⟨div_nonneg hU0 hN.le, (div_le_iff₀ hN).2 (by nlinarith)⟩
      · -- `V_b ∈ [0, 4]`
        have hc : S.bandCount P b 2 = ∑ x ∈ S.bandTri P b, S.y x.1 := by
          simp [Setting.bandCount]
        have hV0 : 0 ≤ ∑ x ∈ S.bandTri P b, S.y x.1 :=
          sum_apexBandTriples_apex_excess_nonneg S.hρ S.hlo
        have hV : ∑ x ∈ S.bandTri P b, S.y x.1 ≤
            (1 - (sig : ℝ) ^ 2) * ((S.bandTri P b).card : ℝ) :=
          sum_apexBandTriples_apex_excess_le S.hρ S.hhi
        rw [hc, beq_false (by norm_num), Bool.cond_false]
        push_cast
        refine ⟨div_nonneg hV0 hN.le, (div_le_iff₀ hN).2 (by nlinarith)⟩

end Esgk.S4
