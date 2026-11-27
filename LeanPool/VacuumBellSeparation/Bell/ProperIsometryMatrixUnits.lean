/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.Defs

/-!
# Matrix units from one proper isometry

For an isometry v in a unital star ring, its defect p=1-vv* is a projection.
The actual elements e_ij=v^i p(v*)^j satisfy the matrix-unit relations.
For a proper isometry their diagonal projections are all nonzero. This
algebraic construction uses no halving theorem or assumed infinite corner.
-/

@[expose] public section

namespace VacuumBellSeparation
namespace ProperIsometry

variable {R : Type*} [Ring R] [StarRing R]

/-- The actual range-complement projection. -/
def defect (v : R) : R := 1 - v * star v

/-- Actual matrix-unit candidates, all inside the algebra of v. -/
def matrixUnit (v : R) (i j : ℕ) : R := v ^ i * defect v * star (v ^ j)

theorem pow_cancel {v : R} (hv : star v * v = 1) (n : ℕ) :
    star (v ^ n) * v ^ n = 1 := by
  rw [star_pow]
  exact pow_mul_pow_eq_one n hv

theorem range_projection {v : R} (hv : star v * v = 1) :
    IsStarProjection (v * star v) := by
  apply isStarProjection_iff'.mpr
  constructor
  · calc
      (v * star v) * (v * star v) = v * (star v * v) * star v := by noncomm_ring
      _ = v * star v := by rw [hv, mul_one]
  · simp only [star_mul, star_star]

theorem defect_projection {v : R} (hv : star v * v = 1) :
    IsStarProjection (defect v) :=
  (range_projection hv).one_sub

theorem defect_star {v : R} (hv : star v * v = 1) : star (defect v) = defect v :=
  (defect_projection hv).isSelfAdjoint.star_eq

theorem defect_sq {v : R} (hv : star v * v = 1) : defect v * defect v = defect v :=
  (isStarProjection_iff'.mp (defect_projection hv)).1

theorem defect_ne_zero {v : R} (hv : v * star v ≠ 1) : defect v ≠ 0 := by
  intro h
  exact hv (sub_eq_zero.mp h).symm

theorem defect_mul {v : R} (hv : star v * v = 1) : defect v * v = 0 := by
  calc
    defect v * v = v - v * (star v * v) := by unfold defect; noncomm_ring
    _ = 0 := by rw [hv, mul_one, sub_self]

theorem defect_mul_pow {v : R} (hv : star v * v = 1) {n : ℕ} (hn : 0 < n) :
    defect v * v ^ n = 0 := by
  cases n with
  | zero => omega
  | succ n => rw [pow_succ', ← mul_assoc, defect_mul hv, zero_mul]

theorem pow_cancel_of_le {v : R} (hv : star v * v = 1) {i j : ℕ} (hij : i ≤ j) :
    star (v ^ i) * v ^ j = v ^ (j - i) := by
  calc
    star (v ^ i) * v ^ j = star (v ^ i) * (v ^ i * v ^ (j - i)) := by
      rw [← pow_add, Nat.add_sub_of_le hij]
    _ = (star (v ^ i) * v ^ i) * v ^ (j - i) := by noncomm_ring
    _ = v ^ (j - i) := by rw [pow_cancel hv, one_mul]

theorem defect_sandwich_zero_of_lt {v : R} (hv : star v * v = 1)
    {i j : ℕ} (hij : i < j) :
    defect v * star (v ^ i) * v ^ j * defect v = 0 := by
  calc
    defect v * star (v ^ i) * v ^ j * defect v =
        (defect v * (star (v ^ i) * v ^ j)) * defect v := by noncomm_ring
    _ = (defect v * v ^ (j - i)) * defect v := by rw [pow_cancel_of_le hv hij.le]
    _ = 0 := by rw [defect_mul_pow hv (Nat.sub_pos_of_lt hij), zero_mul]

theorem defect_sandwich_zero {v : R} (hv : star v * v = 1)
    {i j : ℕ} (hij : i ≠ j) :
    defect v * star (v ^ i) * v ^ j * defect v = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact defect_sandwich_zero_of_lt hv hlt
  · have h := congrArg star (defect_sandwich_zero_of_lt hv hgt)
    simpa only [star_mul, star_star, defect_star hv, star_zero, mul_assoc] using h

theorem defect_sandwich_self {v : R} (hv : star v * v = 1) (i : ℕ) :
    defect v * star (v ^ i) * v ^ i * defect v = defect v := by
  calc
    defect v * star (v ^ i) * v ^ i * defect v =
        defect v * (star (v ^ i) * v ^ i) * defect v := by noncomm_ring
    _ = defect v := by rw [pow_cancel hv, mul_one, defect_sq hv]

theorem matrixUnit_star {v : R} (hv : star v * v = 1) (i j : ℕ) :
    star (matrixUnit v i j) = matrixUnit v j i := by
  simp only [matrixUnit, star_mul, star_star, defect_star hv, mul_assoc]

theorem matrixUnit_mul {v : R} (hv : star v * v = 1) (i j k l : ℕ) :
    matrixUnit v i j * matrixUnit v k l = if j = k then matrixUnit v i l else 0 := by
  classical
  have he : matrixUnit v i j * matrixUnit v k l =
      v ^ i * (defect v * star (v ^ j) * v ^ k * defect v) * star (v ^ l) := by
    unfold matrixUnit
    noncomm_ring
  rw [he]
  by_cases hjk : j = k
  · subst k
    rw [ite_eq_left rfl, defect_sandwich_self hv]
    rfl
  · rw [ite_eq_right hjk, defect_sandwich_zero hv hjk, mul_zero, zero_mul]

theorem diagonal_projection {v : R} (hv : star v * v = 1) (i : ℕ) :
    IsStarProjection (matrixUnit v i i) := by
  apply isStarProjection_iff'.mpr
  exact ⟨by rw [matrixUnit_mul hv, ite_eq_left rfl], matrixUnit_star hv i i⟩

theorem diagonal_ne_zero {v : R} (hv : star v * v = 1) (hproper : v * star v ≠ 1)
    (i : ℕ) : matrixUnit v i i ≠ 0 := by
  have hc : star (v ^ i) * matrixUnit v i i * v ^ i = defect v := by
    calc
      star (v ^ i) * matrixUnit v i i * v ^ i =
          (star (v ^ i) * v ^ i) * defect v * (star (v ^ i) * v ^ i) := by
        unfold matrixUnit
        noncomm_ring
      _ = defect v := by rw [pow_cancel hv, one_mul, mul_one]
  intro hz
  rw [hz, mul_zero, zero_mul] at hc
  exact defect_ne_zero hproper hc.symm

theorem diagonal_orthogonal {v : R} (hv : star v * v = 1)
    {i j : ℕ} (hij : i ≠ j) : matrixUnit v i i * matrixUnit v j j = 0 := by
  rw [matrixUnit_mul hv, ite_eq_right hij]

theorem adjacent_initial {v : R} (hv : star v * v = 1) (n : ℕ) :
    star (matrixUnit v (n + 1) n) * matrixUnit v (n + 1) n = matrixUnit v n n := by
  rw [matrixUnit_star hv, matrixUnit_mul hv, ite_eq_left rfl]

theorem adjacent_final {v : R} (hv : star v * v = 1) (n : ℕ) :
    matrixUnit v (n + 1) n * star (matrixUnit v (n + 1) n) =
      matrixUnit v (n + 1) (n + 1) := by
  rw [matrixUnit_star hv, matrixUnit_mul hv, ite_eq_left rfl]

theorem adjacent_square_zero {v : R} (hv : star v * v = 1) (n : ℕ) :
    matrixUnit v (n + 1) n * matrixUnit v (n + 1) n = 0 := by
  rw [matrixUnit_mul hv, ite_eq_right (show n ≠ n + 1 by omega)]

theorem adjacent_ne_zero {v : R} (hv : star v * v = 1) (hproper : v * star v ≠ 1)
    (n : ℕ) : matrixUnit v (n + 1) n ≠ 0 := by
  intro hz
  have h := adjacent_initial hv n
  rw [hz, star_zero, zero_mul] at h
  exact diagonal_ne_zero hv hproper n h.symm

theorem adjacent_corner_projection {v : R} (hv : star v * v = 1) (n : ℕ) :
    IsStarProjection (matrixUnit v n n + matrixUnit v (n + 1) (n + 1)) :=
  (diagonal_projection hv n).add (diagonal_projection hv (n + 1))
    (diagonal_orthogonal hv (show n ≠ n + 1 by omega))

end ProperIsometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- All constructed matrix units stay in the original local algebra. -/
theorem properIsometry_matrixUnit_mem (A : VonNeumannAlgebra H)
    {v : H →L[ℂ] H} (hv : v ∈ A) (i j : ℕ) : ProperIsometry.matrixUnit v i j ∈ A := by
  unfold ProperIsometry.matrixUnit ProperIsometry.defect
  exact mul_mem (mul_mem (pow_mem hv i) (sub_mem (one_mem A)
    (mul_mem hv (star_mem hv)))) (star_mem (pow_mem hv j))

end VacuumBellSeparation
