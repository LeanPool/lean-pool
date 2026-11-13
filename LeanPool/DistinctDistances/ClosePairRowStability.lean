/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.AnnularClosePairCounting
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Close-pair rows near the `n/3` threshold

Step 1 of `docs/results/explicit-constant-gain-2026-10-18.md`. A close-pair row
is a sum of local distance degrees over the palette values below the threshold.
Every degree is at most three, and the missing amounts at one vertex sum to
`Q = 3D - n + 1`; so two rows at one threshold differ by at most `Q`. With the
close-pair density of the thin annulus, every ball of radius `ρ/20` about a
point then holds at least `2n - 5D - 1` points.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry

variable {n : ℕ}

/-- The close-pair row of one vertex at an inclusive squared threshold. -/
noncomputable def ClosePairRow (p : Config n) (i : Fin n) (T : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j ↦ i ≠ j ∧ dist (p i) (p j) ^ 2 ≤ T)

/-- The ordered close-pair count is the sum of the rows. -/
theorem orderedClosePairs_card_eq_sum_row (p : Config n) (T : ℝ) :
    (OrderedClosePairs p T).card = ∑ i, (ClosePairRow p i T).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro i _hi
  refine Finset.card_bij (fun ij _ ↦ ij.2) ?_ ?_ ?_
  · intro ij hij
    simp only [OrderedClosePairs, Finset.mem_filter, Finset.mem_offDiag,
      Finset.mem_univ, true_and] at hij
    simp only [ClosePairRow, Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨⟨hne, hd⟩, rfl⟩ := hij
    exact ⟨hne, hd⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter] at ha hb
    exact Prod.ext (ha.2.trans hb.2.symm) hab
  · intro j hj
    simp only [ClosePairRow, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨(i, j), ?_, rfl⟩
    simpa [OrderedClosePairs, Finset.mem_offDiag] using hj

/-- A close-pair row is the sum of the local degrees over the palette values
below the threshold. -/
theorem closePairRow_card_eq_sum (p : Config n) (i : Fin n) (T : ℝ) :
    (ClosePairRow p i T).card =
      ∑ r ∈ (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ T),
        (DistanceOutNeighborsAtValue p i r).card := by
  classical
  have hmaps : ∀ j ∈ ClosePairRow p i T, dist (p i) (p j) ∈
      (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ T) := by
    intro j hj
    simp only [ClosePairRow, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine Finset.mem_filter.mpr ⟨?_, hj.2⟩
    rw [OrderedDistanceValues, Finset.mem_image]
    exact ⟨(i, j), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hj.1⟩, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro r hr
  have hrT := (Finset.mem_filter.mp hr).2
  congr 1
  ext j
  simp only [ClosePairRow, DistanceOutNeighborsAtValue, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hne, _⟩, hd⟩
    exact ⟨hne, hd⟩
  · rintro ⟨hne, hd⟩
    exact ⟨⟨hne, by rw [hd]; exact hrT⟩, hd⟩

/-- Two close-pair rows at one threshold differ by at most the total degree
deficit `Q = 3D - n + 1`. -/
theorem closePairRow_card_stability {p : Config n} (hn : 0 < n)
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    (i j : Fin n) (T : ℝ) :
    ((ClosePairRow p i T).card : ℝ) -
        (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) ≤
      ((ClosePairRow p j T).card : ℝ) := by
  set RT := (OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ T) with hRT
  have hi : ((ClosePairRow p i T).card : ℝ) ≤ 3 * (RT.card : ℝ) := by
    rw [closePairRow_card_eq_sum]
    push_cast
    calc ∑ r ∈ RT, ((DistanceOutNeighborsAtValue p i r).card : ℝ) ≤
          ∑ _r ∈ RT, (3 : ℝ) :=
          Finset.sum_le_sum (fun r _ ↦ by exact_mod_cast hcap i r)
      _ = 3 * (RT.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hdef : ∑ r ∈ RT, (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) ≤
      3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1 := by
    rw [← sum_distanceDegreeDeficit p hn j]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro r _ _
    have hc : ((DistanceOutNeighborsAtValue p j r).card : ℝ) ≤ 3 := by
      exact_mod_cast hcap j r
    linarith
  have hj : ((ClosePairRow p j T).card : ℝ) = 3 * (RT.card : ℝ) -
      ∑ r ∈ RT, (3 - ((DistanceOutNeighborsAtValue p j r).card : ℝ)) := by
    rw [closePairRow_card_eq_sum]
    push_cast
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  linarith

/-- Every ball of radius `r` about a point holds at least `2n - 5D - 1` points
when `D ≤ (1/3 + δ)n`, `12δ + 4/n ≤ 3/4` and the close-pair scale
`4(12δ + 4/n)ρ²` is at most `r²`. -/
theorem closedBall_card_lower_bound {p : Config n}
    (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hgp4 : ∀ T ⊆ Config.toFinset p, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (hn : 2 ≤ n) {δ r : ℝ}
    (hD : (NumDistances p : ℝ) ≤ (1 / 3 + δ) * (n : ℝ))
    (hx34 : 12 * δ + 4 / (n : ℝ) ≤ 3 / 4) (hr0 : 0 ≤ r)
    (hr : 4 * (12 * δ + 4 / (n : ℝ)) * distanceAnnulusRadius p ^ 2 ≤ r ^ 2) (j : Fin n) :
    2 * (n : ℝ) - 5 * (NumDistances p : ℝ) - 1 ≤
      (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ≤ r)).card : ℝ) := by
  classical
  have hn0 : 0 < n := by omega
  have hcap := distanceOutNeighborsAtValue_card_le_three_of_noFourCocircular hp hgp4
  set T₀ := 4 * (12 * δ + 4 / (n : ℝ)) * distanceAnnulusRadius p ^ 2 with hT₀
  have hL := thin_annulus_close_pairs_lower_bound hp hgp3 hgp4 hn hD hx34
  rw [← hT₀, orderedClosePairs_card_eq_sum_row] at hL
  push_cast at hL
  have hDo : (NumDistances p : ℝ) = (NumDistancesOrdered p : ℝ) := by
    rw [numDistances_eq_numDistancesOrdered_of_injective hp]
  obtain ⟨i, -, hi⟩ : ∃ i ∈ (Finset.univ : Finset (Fin n)),
      (n : ℝ) - 1 - 2 * (NumDistances p : ℝ) ≤ ((ClosePairRow p i T₀).card : ℝ) := by
    apply Finset.exists_le_of_sum_le ⟨⟨0, hn0⟩, Finset.mem_univ _⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact hL
  have hstab := closePairRow_card_stability hn0 hcap i j T₀
  have hsub : insert j (ClosePairRow p j T₀) ⊆
      (Finset.univ : Finset (Fin n)).filter (fun q ↦ dist (p j) (p q) ≤ r) := by
    intro q hq
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · rw [dist_self]
      exact hr0
    · simp only [ClosePairRow, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hsq := hq.2.trans hr
      nlinarith [dist_nonneg (x := p j) (y := p q)]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [ClosePairRow])] at hcard
  have hcardR : ((ClosePairRow p j T₀).card : ℝ) + 1 ≤
      (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ≤ r)).card : ℝ) := by
    exact_mod_cast hcard
  rw [← hDo] at hstab
  linarith

end Esgk
