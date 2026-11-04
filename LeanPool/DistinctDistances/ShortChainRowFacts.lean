/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.PalettePairCounting
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Row facts for the short exact chain

Formalizes, in count form, the facts used by rows 7–15 and the box of
`docs/results/short-chain-constant-gain-1-60-2026-10-21.md` (§1–§3; the S2 file
`docs/results/explicit-constant-gain-5-239-2026-10-20.md`, F1 and F2).
Thresholds are squared distances. Write

* `P(t) = Σ_j (N_j(t) - 1)` for the ordered pairs of distinct indices at squared
  distance at most `t`, where `N_j(t)` counts the indices `q` with `|p_j p_q|² ≤ t`
  (including `j` itself);
* `R(t)` for the number of palette values `r` with `r² ≤ t`;
* `D` for the palette size and `Q = 3D - n + 1` for the degree deficit at every vertex.

The normalized quantities of the source are `𝒜 = P/n²`, `ℛ = R/n`, `𝔡 = D/n` and
`𝒳 = 3ℛ - 𝒜`. This file proves:

* `P` is nondecreasing in the threshold;
* `P(t) ≤ n · 3R(t)` for `t ≥ 0` (that is, `𝒳 ≥ 0`);
* `P(t') - P(t) ≤ n · 3(R(t') - R(t))` for `0 ≤ t ≤ t'` (that is, `𝒳` is
  nondecreasing);
* the box: `0 ≤ P(t) ≤ n² - n` for `t ≥ 0`, and `R(t) ≤ D`.

The degree cap three is the only geometric input.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry

variable {n : ℕ}

/-- The ordered close-pair count `P(t) = Σ_j (N_j(t) - 1)` is nondecreasing in the
squared threshold `t`. -/
theorem sum_closedBall_sq_card_sub_one_mono (p : Config n) {t t' : ℝ} (h : t ≤ t') :
    ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) ≤
      ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t')).card : ℝ) - 1) := by
  apply Finset.sum_le_sum
  intro j _
  have hle : ((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card ≤
      ((Finset.univ : Finset (Fin n)).filter (fun q ↦ dist (p j) (p q) ^ 2 ≤ t')).card :=
    Finset.card_le_card fun q hq ↦ by
      rw [Finset.mem_filter] at hq ⊢
      exact ⟨hq.1, hq.2.trans h⟩
  have hleR : (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) ≤
      (((Finset.univ : Finset (Fin n)).filter (fun q ↦ dist (p j) (p q) ^ 2 ≤ t')).card : ℝ) := by
    exact_mod_cast hle
  linarith

/-- Row bound (B1), upper side, summed over the points: with the degree cap three,
`P(t) ≤ n · 3R(t)` for every squared threshold `t ≥ 0`. In normalized form this is
`𝒳(t) ≥ 0`. -/
theorem sum_closedBall_sq_card_sub_one_le_three_mul_palette {p : Config n}
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) {t : ℝ} (ht : 0 ≤ t) :
    ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) ≤
      (n : ℝ) * (3 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ)) := by
  have h := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) ↦
    closedBall_sq_card_sub_one_le_three_mul_palette hcap ht j
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h

/-- At one point, a close-pair row is three times the palette count below the
threshold minus the deficits of the palette values below the threshold. -/
private lemma closePairRow_card_eq_three_mul_palette_sub_deficit (p : Config n)
    (j : Fin n) (T : ℝ) :
    ((ClosePairRow p j T).card : ℝ) =
      3 * (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ T)).card : ℝ) -
        ∑ r ∈ (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ T),
          (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) := by
  rw [closePairRow_card_eq_sum]
  push_cast
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- At one point, with the degree cap three, the closed ball grows between two
squared thresholds `0 ≤ t ≤ t'` by at most three times the growth of the palette
count. -/
private lemma closedBall_sq_card_sub_le_three_mul_palette_sub {p : Config n}
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) {t t' : ℝ}
    (ht : 0 ≤ t) (htt' : t ≤ t') (j : Fin n) :
    ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t')).card : ℝ) - 1) -
      ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) ≤
      3 * ((((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t')).card : ℝ) -
        (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ)) := by
  have ht' : 0 ≤ t' := ht.trans htt'
  have hsub : (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t) ⊆
      (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t') := fun r hr ↦ by
    rw [Finset.mem_filter] at hr ⊢
    exact ⟨hr.1, hr.2.trans htt'⟩
  have hdef : ∑ r ∈ (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t),
        (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) ≤
      ∑ r ∈ (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t'),
        (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro r _ _
    have hc : ((DistanceOutNeighborsAtValue p j r).card : ℝ) ≤ 3 := by
      exact_mod_cast hcap j r
    linarith
  have hrow := closePairRow_card_eq_three_mul_palette_sub_deficit p j t
  have hrow' := closePairRow_card_eq_three_mul_palette_sub_deficit p j t'
  have hball : (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) = ((ClosePairRow p j t).card : ℝ) + 1 := by
    rw [closedBall_sq_card_eq_closePairRow_card_add_one p ht j, Nat.cast_add, Nat.cast_one]
  have hball' : (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ dist (p j) (p q) ^ 2 ≤ t')).card : ℝ) =
      ((ClosePairRow p j t').card : ℝ) + 1 := by
    rw [closedBall_sq_card_eq_closePairRow_card_add_one p ht' j, Nat.cast_add, Nat.cast_one]
  linarith

/-- With the degree cap three, the ordered close-pair count grows between two squared
thresholds `0 ≤ t ≤ t'` by at most `n · 3(R(t') - R(t))`. In normalized form this
says that `𝒳 = 3ℛ - 𝒜` is nondecreasing. -/
theorem sum_closedBall_sq_card_sub_one_sub_le_three_mul_palette_sub {p : Config n}
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) {t t' : ℝ}
    (ht : 0 ≤ t) (htt' : t ≤ t') :
    ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t')).card : ℝ) - 1) -
      ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) ≤
      (n : ℝ) * (3 * ((((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t')).card : ℝ) -
        (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ))) := by
  rw [← Finset.sum_sub_distrib]
  have h := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) ↦
    closedBall_sq_card_sub_le_three_mul_palette_sub hcap ht htt' j
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h

/-- For a squared threshold `t ≥ 0`, the ordered close-pair count `P(t)` is
nonnegative: every closed ball contains its center. -/
theorem sum_closedBall_sq_card_sub_one_nonneg (p : Config n) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) := by
  apply Finset.sum_nonneg
  intro j _
  rw [closedBall_sq_card_eq_closePairRow_card_add_one p ht j, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right]
  exact Nat.cast_nonneg _

/-- The ordered close-pair count `P(t)` is at most the number `n² - n` of ordered
pairs of distinct indices. -/
theorem sum_closedBall_sq_card_sub_one_le_mul_self_sub (p : Config n) (t : ℝ) :
    ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) ≤ (n : ℝ) * (n : ℝ) - (n : ℝ) := by
  have h : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) - 1) ≤ (n : ℝ) - 1 := by
    intro j _
    have hc : ((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card ≤ n := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n))
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)
    have hcR : (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ t)).card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hc
    linarith
  have hs := Finset.sum_le_sum h
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  linarith

/-- The palette count `R(t)` below any squared threshold is at most the palette
size `D`. -/
theorem palette_card_le_numDistancesOrdered (p : Config n) (t : ℝ) :
    (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ t)).card : ℝ) ≤
      (NumDistancesOrdered p : ℝ) := by
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

end Esgk
