/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import LeanPool.ScottMeasurement.LinearInequalities.Definitions
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Scott's explicit finite sequence conditions
-/

@[expose] public section

open scoped BigOperators

namespace Scott1964.MeasurementStructures.LinearInequalities

variable {L : Type*} [AddCommGroup L] [Module ℝ L]

/-- A realizing functional satisfies Scott's positive-weight condition (2). -/
theorem Realizable.weightedSequenceCancellation {X N : Set L}
    (hreal : Realizable X N) (hsym : Symmetric X) :
    WeightedSequenceCancellation X N := by
  obtain ⟨φ, hφ⟩ := hreal
  intro n x c hx hN hc hsum
  have hnonneg : ∀ i, 0 ≤ c i * φ (x i) :=
    fun i ↦ mul_nonneg (hc i).le ((hφ (x i) (hx i)).mp (hN i))
  have hzero : ∑ i, c i * φ (x i) = 0 := by
    have := congrArg φ hsum
    simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using this
  intro j
  have hxzero : φ (x j) = 0 := by
    have hterm : c j * φ (x j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hnonneg i).mp hzero j (Finset.mem_univ j)
    exact (mul_eq_zero.mp hterm).resolve_left (hc j).ne'
  apply (hφ (-x j) (hsym (hx j))).mpr
  simp [hxzero]

/-- Condition (2) immediately implies the unit-weight condition (4). -/
theorem WeightedSequenceCancellation.unweighted {X N : Set L}
    (h : WeightedSequenceCancellation X N) :
    UnweightedSequenceCancellation X N := by
  intro n x hx hN hsum
  apply h n x (fun _ ↦ 1) hx hN (fun _ ↦ zero_lt_one)
  simpa using hsum

/-- A realizing relation satisfies Scott's paired equal-sums condition (6). -/
theorem RelationRealizable.sequenceCancellation {Y : Set L} {R : L → L → Prop}
    (hreal : RelationRealizable Y R) : RelationSequenceCancellation Y R := by
  obtain ⟨φ, hφ⟩ := hreal
  intro n x y hx hy hR hsum
  have hle : ∀ i, φ (y i) ≤ φ (x i) :=
    fun i ↦ (hφ (x i) (hx i) (y i) (hy i)).mp (hR i)
  have hsumφ : ∑ i, φ (x i) = ∑ i, φ (y i) := by
    simpa only [map_sum] using congrArg φ hsum
  intro j
  have hhead : φ (x j) ≤ φ (y j) := by
    have hall :=
      (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
        (fun i _ ↦ hle i)).mp hsumφ.symm
    exact (hall j (Finset.mem_univ j)).ge
  exact (hφ (y j) (hy j) (x j) (hx j)).mpr hhead

end Scott1964.MeasurementStructures.LinearInequalities
