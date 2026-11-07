/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.RegularDistanceCocircular
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Ordered squared-distance counting under no four cocircular points

This module isolates the no-four-cocircular part of the elementary distance-multiplicity
ceiling. It also records the centered weighted squared-distance ledger and uses the two
facts to exclude the numerical identity arising in the order-two radial-square argument.

No no-three-collinear hypothesis is used.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry
open scoped BigOperators

variable {n : ℕ}

/-- At most three configuration points lie at a fixed distance from a center under the raw
no-four-cocircular hypothesis. -/
theorem fixedDistance_card_le_three_of_noFourCocircular {A : Config n}
    (hgp4 : ∀ T ⊆ Config.toFinset A, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (c : Point) (r : ℝ) :
    ((Config.toFinset A).filter (fun x ↦ dist x c = r)).card ≤ 3 := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq
      (s := (Config.toFinset A).filter (fun x ↦ dist x c = r))
      (n := 4) (by omega)
  have hTA : T ⊆ Config.toFinset A := hTsub.trans (Finset.filter_subset _ _)
  have hcos : Cospherical (SetLike.coe T) := by
    refine ⟨c, r, ?_⟩
    intro x hx
    have hxT : x ∈ T := by simpa using hx
    exact (Finset.mem_filter.mp (hTsub hxT)).2
  exact hgp4 T hTA hTcard hcos

/-- Raw no-four-cocircularity bounds each fixed-distance out-degree by three.
No no-three-collinear hypothesis is needed. -/
theorem distanceOutNeighborsAtValue_card_le_three_of_noFourCocircular
    {A : Config n} (hA : Function.Injective A)
    (hgp4 : ∀ T ⊆ Config.toFinset A, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (i : Fin n) (r : ℝ) :
    (DistanceOutNeighborsAtValue A i r).card ≤ 3 := by
  classical
  let S : Finset Point := (Config.toFinset A).filter (fun x ↦ dist x (A i) = r)
  have hcard_le : (DistanceOutNeighborsAtValue A i r).card ≤ S.card := by
    refine Finset.card_le_card_of_injOn (fun j ↦ A j) ?_ ?_
    · intro j hj
      simp only [Finset.mem_coe, DistanceOutNeighborsAtValue, Finset.mem_filter,
        Finset.mem_univ, true_and] at hj
      obtain ⟨_hne, hdist⟩ := hj
      change A j ∈ (Config.toFinset A).filter (fun x ↦ dist x (A i) = r)
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩,
        by simpa [dist_comm] using hdist⟩
    · intro _a _ha _b _hb hab
      exact hA hab
  exact hcard_le.trans (fixedDistance_card_le_three_of_noFourCocircular hgp4 (A i) r)

/-- Raw no-four-cocircularity bounds every ordered distance multiplicity by `3 * n`.
No no-three-collinear hypothesis is required. -/
theorem orderedMultiplicity_le_three_mul_of_noFourCocircular {A : Config n}
    (hA : Function.Injective A)
    (hgp4 : ∀ T ⊆ Config.toFinset A, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (r : ℝ) :
    OrderedMultiplicity A r ≤ 3 * n := by
  rw [orderedMultiplicity_eq_sum_outNeighbor_card]
  calc
    ∑ i, (DistanceOutNeighborsAtValue A i r).card ≤ ∑ _i : Fin n, 3 := by
      exact Finset.sum_le_sum fun i _ ↦
        distanceOutNeighborsAtValue_card_le_three_of_noFourCocircular hA hgp4 i r
    _ = 3 * n := by simp [Finset.sum_const, mul_comm]

/-- Exact centered ledger for ordered squared-distance multiplicities. -/
theorem weightedOrderedSquaredDistance_eq_two_mul_n_mul_sum_norm_sq
    (A : Config n) (hcenter : ∑ i, A i = 0) :
    ∑ r ∈ OrderedDistanceValues A, (OrderedMultiplicity A r : ℝ) * r ^ 2 =
      2 * (n : ℝ) * ∑ i, ‖A i‖ ^ 2 := by
  calc
    ∑ r ∈ OrderedDistanceValues A, (OrderedMultiplicity A r : ℝ) * r ^ 2 =
        ∑ r ∈ OrderedDistanceValues A,
          ∑ i, ((DistanceOutNeighborsAtValue A i r).card : ℝ) * r ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [orderedMultiplicity_eq_sum_outNeighbor_card]
      push_cast
      rw [Finset.sum_mul]
    _ = ∑ i, ∑ r ∈ OrderedDistanceValues A,
          ((DistanceOutNeighborsAtValue A i r).card : ℝ) * r ^ 2 := by
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, dist (A i) (A j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact (sum_sqDistance_eq_sum_outDegree_mul A i).symm
    _ = ∑ i, ((n : ℝ) * ‖A i‖ ^ 2 + ∑ j, ‖A j‖ ^ 2 -
          2 * @inner ℝ Point _ (A i) (∑ j, A j)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact sum_sqDistance_expand A i
    _ = 2 * (n : ℝ) * ∑ i, ‖A i‖ ^ 2 := by
      simp only [hcenter, inner_zero_right, mul_zero, sub_zero]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring

/-- In an injective centered configuration of at least two points, raw no-four-cocircularity
excludes the numerical identity forced by an order-two radial square. -/
theorem three_mul_n_mul_sum_orderedDistanceValues_sq_ne_n_add_two_mul_sum_norm_sq
    {A : Config n} (hA : Function.Injective A)
    (hgp4 : ∀ T ⊆ Config.toFinset A, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (hn : 2 ≤ n) (hcenter : ∑ i, A i = 0) :
    3 * (n : ℝ) * (∑ r ∈ OrderedDistanceValues A, r ^ 2) ≠
      ((n : ℝ) + 2) * ∑ i, ‖A i‖ ^ 2 := by
  let S : ℝ := ∑ r ∈ OrderedDistanceValues A, r ^ 2
  let R : ℝ := ∑ i, ‖A i‖ ^ 2
  let W : ℝ :=
    ∑ r ∈ OrderedDistanceValues A, (OrderedMultiplicity A r : ℝ) * r ^ 2
  intro hidentity
  have hidentity' : 3 * (n : ℝ) * S = ((n : ℝ) + 2) * R := by
    simpa only [S, R] using hidentity
  have hledger : W = 2 * (n : ℝ) * R := by
    simpa only [W, R] using
      weightedOrderedSquaredDistance_eq_two_mul_n_mul_sum_norm_sq A hcenter
  have hordered : 6 * (n : ℝ) ^ 2 * S = ((n : ℝ) + 2) * W := by
    calc
      6 * (n : ℝ) ^ 2 * S = 2 * (n : ℝ) * (3 * (n : ℝ) * S) := by ring
      _ = 2 * (n : ℝ) * (((n : ℝ) + 2) * R) := by rw [hidentity']
      _ = ((n : ℝ) + 2) * (2 * (n : ℝ) * R) := by ring
      _ = ((n : ℝ) + 2) * W := by rw [hledger]
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hi₀i₁ : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    norm_num [i₀, i₁] at this
  have hAi₀i₁ : A i₀ ≠ A i₁ := fun h ↦ hi₀i₁ (hA h)
  have hdist_pos : 0 < dist (A i₀) (A i₁) := dist_pos.mpr hAi₀i₁
  have hdist_mem : dist (A i₀) (A i₁) ∈ OrderedDistanceValues A := by
    rw [OrderedDistanceValues, Finset.mem_image]
    exact ⟨(i₀, i₁), by simp [hi₀i₁], rfl⟩
  have hdist_sq_le : dist (A i₀) (A i₁) ^ 2 ≤ S := by
    dsimp only [S]
    exact Finset.single_le_sum (fun r _hr ↦ sq_nonneg r) hdist_mem
  have hSpos : 0 < S :=
    lt_of_lt_of_le (sq_pos_of_pos hdist_pos) hdist_sq_le
  by_cases hn2 : n = 2
  · subst n
    have hmass : OrderedDistanceMass A = 2 := by
      simpa using orderedDistanceMass_eq_n_mul_pred A
    have hmult_le_two : ∀ r ∈ OrderedDistanceValues A, OrderedMultiplicity A r ≤ 2 := by
      intro r hr
      have hle : OrderedMultiplicity A r ≤ OrderedDistanceMass A := by
        unfold OrderedDistanceMass
        exact Finset.single_le_sum
          (fun x _hx ↦ Nat.zero_le (OrderedMultiplicity A x)) hr
      omega
    have hWle : W ≤ 2 * S := by
      dsimp only [W, S]
      calc
        ∑ r ∈ OrderedDistanceValues A, (OrderedMultiplicity A r : ℝ) * r ^ 2 ≤
            ∑ r ∈ OrderedDistanceValues A, 2 * r ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro r hr
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmult_le_two r hr) (sq_nonneg r)
        _ = 2 * ∑ r ∈ OrderedDistanceValues A, r ^ 2 := by
          rw [Finset.mul_sum]
    norm_num at hordered
    nlinarith
  · have hn3 : 3 ≤ n := by omega
    have hWle : W ≤ 3 * (n : ℝ) * S := by
      dsimp only [W, S]
      calc
        ∑ r ∈ OrderedDistanceValues A, (OrderedMultiplicity A r : ℝ) * r ^ 2 ≤
            ∑ r ∈ OrderedDistanceValues A, (3 * (n : ℝ)) * r ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro r _hr
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast orderedMultiplicity_le_three_mul_of_noFourCocircular hA hgp4 r)
            (sq_nonneg r)
        _ = 3 * (n : ℝ) * ∑ r ∈ OrderedDistanceValues A, r ^ 2 := by
          rw [Finset.mul_sum]
    have hnlt : (n : ℝ) + 2 < 2 * (n : ℝ) := by
      exact_mod_cast (show n + 2 < 2 * n by omega)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn3)
    have hscale_pos : 0 < 3 * (n : ℝ) * S := by positivity
    have hscaled : ((n : ℝ) + 2) * W ≤
        ((n : ℝ) + 2) * (3 * (n : ℝ) * S) := by
      exact mul_le_mul_of_nonneg_left hWle (by positivity)
    have hstrict : ((n : ℝ) + 2) * (3 * (n : ℝ) * S) <
        6 * (n : ℝ) ^ 2 * S := by
      calc
        ((n : ℝ) + 2) * (3 * (n : ℝ) * S) <
            (2 * (n : ℝ)) * (3 * (n : ℝ) * S) :=
          mul_lt_mul_of_pos_right hnlt hscale_pos
        _ = 6 * (n : ℝ) ^ 2 * S := by ring
    nlinarith

end Esgk
