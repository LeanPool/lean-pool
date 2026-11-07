/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.CentroidDefectIdentity
public import LeanPool.DistinctDistances.LayerCakeCut
public import LeanPool.DistinctDistances.S4RowBuilder
public import LeanPool.DistinctDistances.SecondMomentLowerSum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Soundness of the moment rows of the `1/40` certificate

Theorem S4 of `docs/results/explicit-constant-gain-1-40-2026-10-21.md` is proved by an
exact-rational certificate whose rows are built by `Esgk.S4.Params.build`. This file proves
that four row families of the builder are valid at the normalized variables `val P S`:

* `Params.rowMlo_sound`: the row `Mlo` (Lemma M, the lower Riemann sum of the second moment over
  the whole grid), from `second_moment_lower_sum_le` with `τ i = gᵢ²` and `k = ng - 1`; the
  Lean lemma is the row times `2n²`;
* `Params.rowLayer_sound`: the row `K` (Lemma K, the averaged cap of the layer cake) over the
  grid points `gᵢ, …, gⱼ`, from `sum_increment_mul_sum_closedBall_sq_card_sub_one_le_two_mul`
  with `τ k' = g_{i+k'}²` and `k = j - i`; the Lean lemma is the row times `n²`;
* `Params.rowCaseLo_sound`, `Params.rowCaseHi_sound`: the case rows `CASElo` (`Y_lo ≤ yMean` with
  the upper Riemann sum) and `CASEhi` (`yMean ≤ Y_hi` with the lower Riemann sum), from the Riemann
  bounds of the centroid defect identity (`mul_sum_centroid_sq_div_sub_le_upper_sum`,
  `lower_sum_le_mul_sum_centroid_sq_div_sub`) with `τ i = gᵢ²`, `k = ng - 1` and `σ = sBar`; the
  Lean lemmas are the rows times `n²`, with `n² yMean = n Σᵢ |pᵢ - c|²/ρ² - n² sBar²`.

The rows `Mlo`, `K` and the case rows have their entries in cells (`Params.cells`); the left
side of such a row is the sum of the left sides of its cells (`QRow.lhs_cells`), and the grid
check `Params.gridMono` gives the monotonicity of the squared grid values
(`Params.sq_le_of_gridMono`).
-/

@[expose] public section

namespace Esgk.S4

open Finset

/-! ### Cell sums and grid monotonicity -/

/-- The left side of a row is additive in the entry list. -/
private theorem lhs_append (A B : List (Nat × ℚ)) (rhs : ℚ) (v : Nat → ℝ) :
    QRow.lhs ⟨A ++ B, rhs⟩ v = QRow.lhs ⟨A, rhs⟩ v + QRow.lhs ⟨B, rhs⟩ v := by
  simp only [QRow.lhs, List.map_append, List.sum_append]

/-- The left side of a row whose entries are the cells `f k, f (k + 1), …, f (k + c - 1)`
(`Params.cells f c k`) is the sum over `i < c` of the left sides of the cells `f (k + i)`. -/
theorem QRow.lhs_cells (f : Nat → List (Nat × ℚ)) (rhs : ℚ) (v : Nat → ℝ) (c k : Nat) :
    QRow.lhs ⟨Params.cells f c k, rhs⟩ v = ∑ i ∈ range c, QRow.lhs ⟨f (k + i), rhs⟩ v := by
  induction c generalizing k with
  | zero => simp [Params.cells, QRow.lhs]
  | succ c ih =>
    rw [Params.cells, lhs_append, ih (k + 1), Finset.sum_range_succ', add_zero, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by rw [show k + 1 + i = k + (i + 1) by omega]

/-- The grid check `P.gridMono c k` gives `g_{k+i}² ≤ g_{k+i+1}²` for every `i < c`. -/
theorem Params.sq_le_of_gridMono (P : Params) {c k : Nat} (h : P.gridMono c k = true) :
    ∀ i < c, P.sq (k + i) ≤ P.sq (k + i + 1) := by
  induction c generalizing k with
  | zero => intro i hi; omega
  | succ c ih =>
    rw [Params.gridMono, Bool.and_eq_true, decide_eq_true_eq] at h
    intro i hi
    rcases i with _ | i
    · simpa using h.1
    · rw [show k + (i + 1) = k + 1 + i by omega]
      exact ih h.2 i (by omega)

/-- The squared grid value in `ℝ`. -/
private theorem sq_cast (P : Params) (i : Nat) : ((P.sq i : ℚ) : ℝ) = ((P.g i : ℚ) : ℝ) ^ 2 := by
  rw [Params.sq, Rat.cast_mul, sq]

/-- The real squared grid values are nondecreasing on the cells of a grid check. -/
private theorem real_sq_le_of_gridMono (P : Params) {c k : Nat} (h : P.gridMono c k = true) :
    ∀ i < c, ((P.g (k + i) : ℚ) : ℝ) ^ 2 ≤ ((P.g (k + i + 1) : ℚ) : ℝ) ^ 2 := by
  intro i hi
  rw [← sq_cast, ← sq_cast]
  exact_mod_cast P.sq_le_of_gridMono h i hi

/-- The scaled mean radial excess: `n² yMean = n Σᵢ |pᵢ - c|²/ρ² - n² sBar²`. -/
private theorem sq_mul_ybar {n : ℕ} (S : Setting n) :
    (n : ℝ) ^ 2 * S.ybar =
      (n : ℝ) * (∑ i, dist (S.p i) S.c ^ 2 / S.ρ ^ 2) - (n : ℝ) ^ 2 * (sig : ℝ) ^ 2 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast S.n_pos.ne'
  unfold Setting.ybar Setting.y radialExcess
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-! ### Lemma M -/

/-- Soundness of the row `Mlo` of Theorem S4 (Lemma M: the lower Riemann sum of the second
moment over the whole grid), `Σ_cells ((b² - a²)/2) (6ℛ(a) - 𝒜(a)) - 12 D/n - 2/n ≤ -3`. The
Lean lemma `second_moment_lower_sum_le` (with `τ i = gᵢ²`, `k = ng - 1`) is this row times
`2n²`; the builder checks `0 < ng`, `0 ≤ g₀²`, the monotonicity of the grid and
`g_{ng-1}² ≤ 4`. -/
theorem Params.rowMlo_sound {n : ℕ} (P : Params) (S : Setting n) {r : QRow}
    (h : P.rowMlo = some r) : r.Holds (val P S) := by
  unfold Params.rowMlo at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq] at hc
  obtain ⟨⟨⟨hng, hsq0⟩, hmono⟩, hsqk⟩ := hc
  cases h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast S.n_pos
  set τ : ℕ → ℝ := fun i ↦ ((P.g i : ℚ) : ℝ) ^ 2 with hτdef
  have hτ0 : 0 ≤ τ 0 := by
    simp only [hτdef, ← sq_cast]
    exact_mod_cast hsq0
  have hτ : ∀ i < P.ng - 1, τ i ≤ τ (i + 1) := by
    intro i hi
    have := real_sq_le_of_gridMono P hmono i hi
    simpa only [Nat.zero_add] using this
  have hτk : τ (P.ng - 1) ≤ 4 := by
    simp only [hτdef, ← sq_cast]
    exact_mod_cast hsqk
  have L : ∑ i ∈ range (P.ng - 1), (τ (i + 1) - τ i) *
        (6 * (n : ℝ) * S.pal (τ i * S.ρ ^ 2) - S.pairs (τ i * S.ρ ^ 2)) ≤
      2 * (n : ℝ) ^ 2 + 8 * (n : ℝ) * (3 * S.D - (n : ℝ) + 1) - 4 * (n : ℝ) :=
    second_moment_lower_sum_le S.n_pos S.hcap S.hρ S.hρsq τ hτ0 hτ hτk
  have hcell : ∀ i ∈ range (P.ng - 1), QRow.lhs ⟨P.mloCell (0 + i), -3⟩ (val P S) =
      (τ (i + 1) - τ i) * (6 * (n : ℝ) * S.pal (τ i * S.ρ ^ 2) - S.pairs (τ i * S.ρ ^ 2)) /
        (2 * ((n : ℝ) * n)) := by
    intro i hi
    have hi' : i < P.ng := by have := Finset.mem_range.mp hi; omega
    simp only [Nat.zero_add, QRow.lhs, Params.mloCell, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    rw [val_aVar P S hi', val_rVar P S hi']
    push_cast [sq_cast]
    simp only [hτdef]
    field_simp
    ring
  unfold QRow.Holds
  rw [lhs_append, QRow.lhs_cells, Finset.sum_congr rfl hcell, ← Finset.sum_div]
  simp only [QRow.lhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [val_dV, val_eV]
  have hdiv := div_le_div_of_nonneg_right L (by positivity : (0 : ℝ) ≤ 2 * ((n : ℝ) * n))
  have he : (2 * (n : ℝ) ^ 2 + 8 * (n : ℝ) * (3 * S.D - (n : ℝ) + 1) - 4 * (n : ℝ)) /
      (2 * ((n : ℝ) * n)) = -3 + 12 * (S.D / n) + 2 * (1 / n) := by
    field_simp
    ring
  push_cast
  linarith

/-! ### Lemma K -/

/-- Soundness of the row `K` of Theorem S4 (Lemma K: the averaged cap of the layer cake) over the
grid points `gᵢ, …, gⱼ`, `Σ_cells (b² - a²) 𝒜(a) ≤ 2sBar`. The Lean lemma
`sum_increment_mul_sum_closedBall_sq_card_sub_one_le_two_mul` (with `τ k' = g_{i+k'}²`,
`k = j - i`, `σ = sBar`) is this row times `n²`; the builder checks `j < ng`, `i ≤ j`, the
monotonicity of the grid on `gᵢ, …, gⱼ` and `gⱼ² ≤ 2sBar² + 2sBar`. -/
theorem Params.rowLayer_sound {n : ℕ} (P : Params) (S : Setting n) {i j : Nat} {r : QRow}
    (h : P.rowLayer i j = some r) : r.Holds (val P S) := by
  unfold Params.rowLayer at h
  split_ifs at h with hc
  simp only [Params.ok, Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq, Nat.ble_eq] at hc
  obtain ⟨⟨⟨hj, hij⟩, hmono⟩, hsqj⟩ := hc
  cases h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast S.n_pos
  have hσ : (0 : ℝ) < (sig : ℝ) := by rw [Setting.sig_cast]; norm_num
  set τ : ℕ → ℝ := fun m ↦ ((P.g (i + m) : ℚ) : ℝ) ^ 2 with hτdef
  have hτ : ∀ m < j - i, τ m ≤ τ (m + 1) := fun m hm ↦ real_sq_le_of_gridMono P hmono m hm
  have hτk : τ (j - i) ≤ 2 * (sig : ℝ) ^ 2 + 2 * (sig : ℝ) := by
    simp only [hτdef, show i + (j - i) = j by omega, ← sq_cast]
    have h2 : ((P.sq j : ℚ) : ℝ) ≤ ((2 * sig * sig + 2 * sig : ℚ) : ℝ) := Rat.cast_le.mpr hsqj
    push_cast at h2
    linarith
  have L : ∑ m ∈ range (j - i), (τ (m + 1) - τ m) * S.pairs (τ m * S.ρ ^ 2) ≤
      2 * (sig : ℝ) * (n : ℝ) ^ 2 :=
    sum_increment_mul_sum_closedBall_sq_card_sub_one_le_two_mul S.hsum S.hρ hσ S.hlo S.hhi τ
      hτ hτk
  have hcell : ∀ m ∈ range (j - i), QRow.lhs ⟨P.layerCell (i + m), 2 * sig⟩ (val P S) =
      (τ (m + 1) - τ m) * S.pairs (τ m * S.ρ ^ 2) / ((n : ℝ) * n) := by
    intro m hm
    have hm' : i + m < P.ng := by have := Finset.mem_range.mp hm; omega
    simp only [QRow.lhs, Params.layerCell, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    rw [val_aVar P S hm']
    push_cast [sq_cast]
    simp only [hτdef, show i + (m + 1) = i + m + 1 from rfl]
    ring
  unfold QRow.Holds
  rw [QRow.lhs_cells, Finset.sum_congr rfl hcell, ← Finset.sum_div]
  have hdiv := div_le_div_of_nonneg_right L (by positivity : (0 : ℝ) ≤ (n : ℝ) * n)
  have he : 2 * (sig : ℝ) * (n : ℝ) ^ 2 / ((n : ℝ) * n) = 2 * (sig : ℝ) := by
    field_simp
  push_cast
  linarith

/-! ### The case rows -/

/-- Soundness of the row `CASElo` of Theorem S4 in the case `Y_lo ≤ yMean` (the upper Riemann sum
of the centroid defect identity), `12 D/n + 4/n - 2 Up ≤ W - Y_lo + 4` with
`Up = Σ_cells ((b² - a²)/2) 𝒳(b) + (g₀²/2) 𝒳(g₀)`, `𝒳 = 3ℛ - 𝒜` and `W = 1 - sBar²`. The Lean
lemma `mul_sum_centroid_sq_div_sub_le_upper_sum` (with `τ i = gᵢ²`, `k = ng - 1`, `σ = sBar`) is
the bound `yMean ≤ W - 4𝔮 + 2 Up` times `n²`, by
`n² yMean = n Σᵢ |pᵢ - c|²/ρ² - n² sBar²`; the builder
checks `0 < ng`, `0 ≤ g₀²`, the monotonicity of the grid and `4 ≤ g_{ng-1}²`. -/
theorem Params.rowCaseLo_sound {n : ℕ} (P : Params) (S : Setting n) {Ylo : ℚ} {r : QRow}
    (h : P.rowCaseLo Ylo = some r) (hy : (Ylo : ℝ) ≤ S.ybar) : r.Holds (val P S) := by
  unfold Params.rowCaseLo at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq] at hc
  obtain ⟨⟨⟨hng, hsq0⟩, hmono⟩, hsqk⟩ := hc
  cases h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast S.n_pos
  set τ : ℕ → ℝ := fun i ↦ ((P.g i : ℚ) : ℝ) ^ 2 with hτdef
  have hτ0 : 0 ≤ τ 0 := by
    simp only [hτdef, ← sq_cast]
    exact_mod_cast hsq0
  have hτ : ∀ i < P.ng - 1, τ i ≤ τ (i + 1) := by
    intro i hi
    have := real_sq_le_of_gridMono P hmono i hi
    simpa only [Nat.zero_add] using this
  have hτk : 4 ≤ τ (P.ng - 1) := by
    simp only [hτdef, ← sq_cast]
    exact_mod_cast hsqk
  have L : (n : ℝ) * (∑ i, dist (S.p i) S.c ^ 2 / S.ρ ^ 2) - (n : ℝ) ^ 2 * (sig : ℝ) ^ 2 ≤
      (n : ℝ) ^ 2 * (1 - (sig : ℝ) ^ 2) - 4 * (n : ℝ) * (3 * S.D - (n : ℝ) + 1) +
        ∑ i ∈ range (P.ng - 1), (τ (i + 1) - τ i) *
          (3 * (n : ℝ) * S.pal (τ (i + 1) * S.ρ ^ 2) - S.pairs (τ (i + 1) * S.ρ ^ 2)) +
        τ 0 * (3 * (n : ℝ) * S.pal (τ 0 * S.ρ ^ 2) - S.pairs (τ 0 * S.ρ ^ 2)) :=
    mul_sum_centroid_sq_div_sub_le_upper_sum S.n_pos S.hcap S.hρ S.hρsq (sig : ℝ) τ hτ0 hτ hτk
  have hcell : ∀ i ∈ range (P.ng - 1), QRow.lhs ⟨P.upCell (0 + i), wid - Ylo + 4⟩ (val P S) =
      -((τ (i + 1) - τ i) *
        (3 * (n : ℝ) * S.pal (τ (i + 1) * S.ρ ^ 2) - S.pairs (τ (i + 1) * S.ρ ^ 2)) /
          ((n : ℝ) * n)) := by
    intro i hi
    have hi' : i + 1 < P.ng := by have := Finset.mem_range.mp hi; omega
    simp only [Nat.zero_add, QRow.lhs, Params.upCell, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    rw [val_aVar P S hi', val_rVar P S hi']
    push_cast [sq_cast]
    simp only [hτdef]
    field_simp
    ring
  have htail : QRow.lhs ⟨[(rVar 0, -6 * (P.sq 0 / 2)), (aVar 0, 2 * (P.sq 0 / 2))],
      wid - Ylo + 4⟩ (val P S) =
      -(τ 0 * (3 * (n : ℝ) * S.pal (τ 0 * S.ρ ^ 2) - S.pairs (τ 0 * S.ρ ^ 2)) /
        ((n : ℝ) * n)) := by
    simp only [QRow.lhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [val_aVar P S hng, val_rVar P S hng]
    push_cast [sq_cast]
    simp only [hτdef]
    field_simp
    ring
  unfold QRow.Holds
  rw [lhs_append, lhs_append, QRow.lhs_cells, Finset.sum_congr rfl hcell,
    Finset.sum_neg_distrib, ← Finset.sum_div, htail]
  simp only [QRow.lhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [val_dV, val_eV]
  have hyb := sq_mul_ybar S
  have hny := mul_le_mul_of_nonneg_left hy (sq_nonneg (n : ℝ))
  set X := ∑ i ∈ range (P.ng - 1), (τ (i + 1) - τ i) *
    (3 * (n : ℝ) * S.pal (τ (i + 1) * S.ρ ^ 2) - S.pairs (τ (i + 1) * S.ρ ^ 2))
  set Y := τ 0 * (3 * (n : ℝ) * S.pal (τ 0 * S.ρ ^ 2) - S.pairs (τ 0 * S.ρ ^ 2))
  have hZ : (n : ℝ) ^ 2 * (Ylo : ℝ) - (n : ℝ) ^ 2 * (1 - (sig : ℝ) ^ 2) +
      4 * (n : ℝ) * (3 * S.D - (n : ℝ) + 1) ≤ X + Y := by linarith
  have hdiv := div_le_div_of_nonneg_right hZ (by positivity : (0 : ℝ) ≤ (n : ℝ) * n)
  have he : ((n : ℝ) ^ 2 * (Ylo : ℝ) - (n : ℝ) ^ 2 * (1 - (sig : ℝ) ^ 2) +
      4 * (n : ℝ) * (3 * S.D - (n : ℝ) + 1)) / ((n : ℝ) * n) =
      (Ylo : ℝ) - (1 - (sig : ℝ) ^ 2) + 12 * (S.D / n) - 4 + 4 * (1 / n) := by
    field_simp
    ring
  rw [add_div X Y] at hdiv
  push_cast [wid]
  linarith

/-- Soundness of the row `CASEhi` of Theorem S4 in the case `yMean ≤ Y_hi` (the lower Riemann sum
of the centroid defect identity), `-12 D/n - 4/n + 2 Lo ≤ Y_hi - W - 4` with
`Lo = Σ_cells ((b² - a²)/2) 𝒳(a)`, `𝒳 = 3ℛ - 𝒜` and `W = 1 - sBar²`. The Lean lemma
`lower_sum_le_mul_sum_centroid_sq_div_sub` (with `τ i = gᵢ²`, `k = ng - 1`, `σ = sBar`) is the
bound `W - 4𝔮 + 2 Lo ≤ yMean` times `n²`, by
`n² yMean = n Σᵢ |pᵢ - c|²/ρ² - n² sBar²`; the builder checks
`0 < ng`, `0 ≤ g₀²`, the monotonicity of the grid and `g_{ng-1}² ≤ 4`. -/
theorem Params.rowCaseHi_sound {n : ℕ} (P : Params) (S : Setting n) {Yhi : ℚ} {r : QRow}
    (h : P.rowCaseHi Yhi = some r) (hy : S.ybar ≤ (Yhi : ℝ)) : r.Holds (val P S) := by
  unfold Params.rowCaseHi at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq] at hc
  obtain ⟨⟨⟨hng, hsq0⟩, hmono⟩, hsqk⟩ := hc
  cases h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast S.n_pos
  set τ : ℕ → ℝ := fun i ↦ ((P.g i : ℚ) : ℝ) ^ 2 with hτdef
  have hτ0 : 0 ≤ τ 0 := by
    simp only [hτdef, ← sq_cast]
    exact_mod_cast hsq0
  have hτ : ∀ i < P.ng - 1, τ i ≤ τ (i + 1) := by
    intro i hi
    have := real_sq_le_of_gridMono P hmono i hi
    simpa only [Nat.zero_add] using this
  have hτk : τ (P.ng - 1) ≤ 4 := by
    simp only [hτdef, ← sq_cast]
    exact_mod_cast hsqk
  have L : (n : ℝ) ^ 2 * (1 - (sig : ℝ) ^ 2) - 4 * (n : ℝ) * (3 * S.D - (n : ℝ) + 1) +
        ∑ i ∈ range (P.ng - 1), (τ (i + 1) - τ i) *
          (3 * (n : ℝ) * S.pal (τ i * S.ρ ^ 2) - S.pairs (τ i * S.ρ ^ 2)) ≤
      (n : ℝ) * (∑ i, dist (S.p i) S.c ^ 2 / S.ρ ^ 2) - (n : ℝ) ^ 2 * (sig : ℝ) ^ 2 :=
    lower_sum_le_mul_sum_centroid_sq_div_sub S.n_pos S.hcap S.hρ S.hρsq (sig : ℝ) τ hτ0 hτ hτk
  have hcell : ∀ i ∈ range (P.ng - 1), QRow.lhs ⟨P.loCell (0 + i), Yhi - wid - 4⟩ (val P S) =
      (τ (i + 1) - τ i) * (3 * (n : ℝ) * S.pal (τ i * S.ρ ^ 2) - S.pairs (τ i * S.ρ ^ 2)) /
        ((n : ℝ) * n) := by
    intro i hi
    have hi' : i < P.ng := by have := Finset.mem_range.mp hi; omega
    simp only [Nat.zero_add, QRow.lhs, Params.loCell, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    rw [val_aVar P S hi', val_rVar P S hi']
    push_cast [sq_cast]
    simp only [hτdef]
    field_simp
    ring
  unfold QRow.Holds
  rw [lhs_append, QRow.lhs_cells, Finset.sum_congr rfl hcell, ← Finset.sum_div]
  simp only [QRow.lhs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [val_dV, val_eV]
  have hyb := sq_mul_ybar S
  have hny := mul_le_mul_of_nonneg_left hy (sq_nonneg (n : ℝ))
  set X := ∑ i ∈ range (P.ng - 1), (τ (i + 1) - τ i) *
    (3 * (n : ℝ) * S.pal (τ i * S.ρ ^ 2) - S.pairs (τ i * S.ρ ^ 2))
  have hZ : X ≤ (n : ℝ) ^ 2 * (Yhi : ℝ) - (n : ℝ) ^ 2 * (1 - (sig : ℝ) ^ 2) +
      4 * (n : ℝ) * (3 * S.D - (n : ℝ) + 1) := by linarith
  have hdiv := div_le_div_of_nonneg_right hZ (by positivity : (0 : ℝ) ≤ (n : ℝ) * n)
  have he : ((n : ℝ) ^ 2 * (Yhi : ℝ) - (n : ℝ) ^ 2 * (1 - (sig : ℝ) ^ 2) +
      4 * (n : ℝ) * (3 * S.D - (n : ℝ) + 1)) / ((n : ℝ) * n) =
      (Yhi : ℝ) - (1 - (sig : ℝ) ^ 2) + 12 * (S.D / n) - 4 + 4 * (1 / n) := by
    field_simp
    ring
  push_cast [wid]
  linarith

end Esgk.S4
