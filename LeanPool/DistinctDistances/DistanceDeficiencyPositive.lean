/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.DistanceMultiplicityDefectBudget
public import Mathlib.Tactic.Ring

/-!
# Positivity of the ordered distance deficiency

The raw multiplicity cap gives the usual lower bound `n - 1 ≤ 3 * NumDistancesOrdered A`.
If equality held for a general-position configuration with at least four points, the exact defect
budget would force every realized ordered multiplicity to attain `3 * n`. The resulting regular
distance graphs contradict the general-position saturation obstruction. Thus the bound is strict,
without using a diameter-graph theorem.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry
open scoped BigOperators

variable {n : ℕ}

/-- An injective general-position configuration of at least four points has enough realized
ordered distances to satisfy `n ≤ 3 * NumDistancesOrdered A`.

The extra unit over the elementary mass/cap bound excludes exact saturation using the regular
distance-graph obstruction; no diameter-graph theorem is used. -/
theorem numPoints_le_three_mul_numDistancesOrdered {A : Config n}
    (hA : Function.Injective A) (hgp : InGeneralPosition (Config.toFinset A))
    (hn : 4 ≤ n) :
    n ≤ 3 * NumDistancesOrdered A := by
  have hmass :
      ∑ r ∈ OrderedDistanceValues A, OrderedMultiplicity A r = n * (n - 1) := by
    simpa [OrderedDistanceMass] using orderedDistanceMass_eq_n_mul_pred A
  have hcapSum :
      ∑ r ∈ OrderedDistanceValues A, OrderedMultiplicity A r ≤
        (3 * n) * (OrderedDistanceValues A).card := by
    calc
      ∑ r ∈ OrderedDistanceValues A, OrderedMultiplicity A r ≤
          ∑ _r ∈ OrderedDistanceValues A, 3 * n := by
        exact Finset.sum_le_sum fun r _hr ↦ orderedMultiplicity_le_three_mul hA hgp r
      _ = (3 * n) * (OrderedDistanceValues A).card := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact Nat.mul_comm _ _
  have hmul : n * (n - 1) ≤ n * (3 * NumDistancesOrdered A) := by
    calc
      n * (n - 1) =
          ∑ r ∈ OrderedDistanceValues A, OrderedMultiplicity A r := hmass.symm
      _ ≤ (3 * n) * (OrderedDistanceValues A).card := hcapSum
      _ = n * (3 * NumDistancesOrdered A) := by
        unfold NumDistancesOrdered
        ring
  have hpred : n - 1 ≤ 3 * NumDistancesOrdered A := by
    exact le_of_mul_le_mul_left hmul (by omega)
  by_contra hbound
  have hledger : (n - 1) + 0 = 3 * NumDistancesOrdered A := by
    omega
  have hdefectSum :
      ∑ r ∈ OrderedDistanceValues A, OrderedMultiplicityDefect A r = 0 := by
    simpa using
      (sum_orderedMultiplicityDefect_eq_n_mul A hA hgp.2 (σ := 0) hledger)
  have hmult : ∀ r ∈ OrderedDistanceValues A, OrderedMultiplicity A r = 3 * n := by
    intro r hr
    have hdefectLe :
        OrderedMultiplicityDefect A r ≤
          ∑ s ∈ OrderedDistanceValues A, OrderedMultiplicityDefect A s := by
      exact Finset.single_le_sum
        (s := OrderedDistanceValues A)
        (f := fun s ↦ OrderedMultiplicityDefect A s)
        (fun _s _hs ↦ Nat.zero_le _) hr
    have hdefect : OrderedMultiplicityDefect A r = 0 := by
      omega
    have hfill := orderedMultiplicity_add_defect_eq_three_mul A hA hgp.2 r
    omega
  exact (not_regular_distance_degrees_of_generalPosition hA hgp hn)
    (regular_distance_degrees_of_all_multiplicities_eq_three_mul hA hgp hmult)

/-- In the distance-deficiency ledger, the deficiency is positive for an injective
general-position configuration of at least four points. -/
theorem distanceDeficiency_pos {A : Config n} (hA : Function.Injective A)
    (hgp : InGeneralPosition (Config.toFinset A)) (hn : 4 ≤ n) {σ : ℕ}
    (hσ : (n - 1) + σ = 3 * NumDistancesOrdered A) :
    0 < σ := by
  have hbound := numPoints_le_three_mul_numDistancesOrdered hA hgp hn
  omega

/-- The order parameter `σ + 1` in the distance-deficiency ledger is at least two. -/
theorem two_le_distanceDeficiency_add_one {A : Config n} (hA : Function.Injective A)
    (hgp : InGeneralPosition (Config.toFinset A)) (hn : 4 ≤ n) {σ : ℕ}
    (hσ : (n - 1) + σ = 3 * NumDistancesOrdered A) :
    2 ≤ σ + 1 := by
  have hpositive := distanceDeficiency_pos hA hgp hn hσ
  omega

end Esgk
