/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.GP4OrderedSquaredDistanceLedger
public import LeanPool.DistinctDistances.DistanceDesign
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Ordered distance-multiplicity defect budget

Raw no-four-cocircularity bounds each ordered distance multiplicity by `3 * n`.  This module
records the unused capacity of every realized distance class and sums it exactly under the
distance-deficiency ledger `(n - 1) + σ = 3 * NumDistancesOrdered A`.

The result is combinatorial bookkeeping.  It does not use the planar diameter-graph theorem and
does not improve the distinct-distance bound.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry
open scoped BigOperators

variable {n : ℕ}

/-- The unused ordered-pair capacity in one realized distance class under the raw GP4 cap. -/
noncomputable def OrderedMultiplicityDefect (A : Config n) (r : ℝ) : ℕ :=
  3 * n - OrderedMultiplicity A r

/-- Under injectivity and raw no-four-cocircularity, observed multiplicity plus its defect is the
full `3 * n` capacity. -/
theorem orderedMultiplicity_add_defect_eq_three_mul
    (A : Config n) (hA : Function.Injective A)
    (hgp4 : ∀ T ⊆ Config.toFinset A, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (r : ℝ) :
    OrderedMultiplicity A r + OrderedMultiplicityDefect A r = 3 * n := by
  unfold OrderedMultiplicityDefect
  have hcap := orderedMultiplicity_le_three_mul_of_noFourCocircular hA hgp4 r
  omega

/-- The total distance-class capacity defect is exactly `n * σ` under the deficiency ledger. -/
theorem sum_orderedMultiplicityDefect_eq_n_mul
    (A : Config n) (hA : Function.Injective A)
    (hgp4 : ∀ T ⊆ Config.toFinset A, T.card = 4 → ¬Cospherical (SetLike.coe T))
    {σ : ℕ} (hσ : (n - 1) + σ = 3 * NumDistancesOrdered A) :
    ∑ r ∈ OrderedDistanceValues A, OrderedMultiplicityDefect A r = n * σ := by
  classical
  have hsum :
      (∑ r ∈ OrderedDistanceValues A, OrderedMultiplicity A r) +
          ∑ r ∈ OrderedDistanceValues A, OrderedMultiplicityDefect A r =
        (3 * n) * (OrderedDistanceValues A).card := by
    rw [← Finset.sum_add_distrib]
    calc
      ∑ r ∈ OrderedDistanceValues A,
          (OrderedMultiplicity A r + OrderedMultiplicityDefect A r) =
          ∑ _r ∈ OrderedDistanceValues A, 3 * n := by
        exact Finset.sum_congr rfl fun r _hr ↦
          orderedMultiplicity_add_defect_eq_three_mul A hA hgp4 r
      _ = (3 * n) * (OrderedDistanceValues A).card := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact Nat.mul_comm _ _
  have hmass :
      ∑ r ∈ OrderedDistanceValues A, OrderedMultiplicity A r = n * (n - 1) := by
    simpa [OrderedDistanceMass] using orderedDistanceMass_eq_n_mul_pred A
  have hscaled := congrArg (fun k : ℕ ↦ n * k) hσ
  simp only [Nat.mul_add] at hscaled
  change (n - 1) + σ = 3 * (OrderedDistanceValues A).card at hσ
  rw [hmass] at hsum
  nlinarith

/-- For any real weight on distance values, the observed weighted mass plus the weighted defect
is the full `3 * n` weighted capacity. -/
theorem weightedOrderedMultiplicity_add_defect_eq_three_mul
    (A : Config n) (hA : Function.Injective A)
    (hgp4 : ∀ T ⊆ Config.toFinset A, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (w : ℝ → ℝ) :
    (∑ r ∈ OrderedDistanceValues A, (OrderedMultiplicity A r : ℝ) * w r) +
        ∑ r ∈ OrderedDistanceValues A, (OrderedMultiplicityDefect A r : ℝ) * w r =
      3 * (n : ℝ) * ∑ r ∈ OrderedDistanceValues A, w r := by
  rw [← Finset.sum_add_distrib]
  calc
    ∑ r ∈ OrderedDistanceValues A,
        ((OrderedMultiplicity A r : ℝ) * w r +
          (OrderedMultiplicityDefect A r : ℝ) * w r) =
        ∑ r ∈ OrderedDistanceValues A, (3 * (n : ℝ)) * w r := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [← add_mul, ← Nat.cast_add,
        orderedMultiplicity_add_defect_eq_three_mul A hA hgp4 r]
      norm_num
    _ = 3 * (n : ℝ) * ∑ r ∈ OrderedDistanceValues A, w r := by
      rw [Finset.mul_sum]

/-- With a nonnegative weight, the observed weighted multiplicity is bounded by the full
`3 * n` capacity; the difference is the explicit nonnegative defect sum. -/
theorem weightedOrderedMultiplicity_le_three_mul
    (A : Config n) (hA : Function.Injective A)
    (hgp4 : ∀ T ⊆ Config.toFinset A, T.card = 4 → ¬Cospherical (SetLike.coe T))
    (w : ℝ → ℝ) (hw : ∀ r ∈ OrderedDistanceValues A, 0 ≤ w r) :
    ∑ r ∈ OrderedDistanceValues A, (OrderedMultiplicity A r : ℝ) * w r ≤
      3 * (n : ℝ) * ∑ r ∈ OrderedDistanceValues A, w r := by
  have hidentity := weightedOrderedMultiplicity_add_defect_eq_three_mul A hA hgp4 w
  have hdefectNonneg :
      0 ≤ ∑ r ∈ OrderedDistanceValues A,
        (OrderedMultiplicityDefect A r : ℝ) * w r := by
    exact Finset.sum_nonneg fun r hr ↦
      mul_nonneg (Nat.cast_nonneg _) (hw r hr)
  nlinarith

end Esgk
