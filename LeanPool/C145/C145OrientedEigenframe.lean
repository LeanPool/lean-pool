/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145CyclicSpectral
public import LeanPool.C145.C145CoordinatePermutation
public import LeanPool.C145.C145SignedGroundPulseCalibration

/-! Elementary sign orientation, reindexing and reconstruction of the original matrix. -/

@[expose] public section

noncomputable section
namespace C145.OrientedEigenframe
open scoped BigOperators
open Matrix

/-- The sign used to orient a mode, positive for a positive overlap and negative otherwise. -/
def orientation (a : ℝ) : ℝ := if 0 < a then 1 else -1

theorem orientation_sq (a : ℝ) : orientation a * orientation a = 1 := by
  unfold orientation; split <;> norm_num

theorem oriented_pos (a : ℝ) (ha : a ≠ 0) : 0 < orientation a * a := by
  unfold orientation
  split_ifs with h
  · simpa using h
  · have : a < 0 := lt_of_le_of_ne (le_of_not_gt h) ha
    simpa using neg_pos.mpr this

theorem oriented_frame {n : ℕ} (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (e : Fin (n + 1) ≃ Fin (n + 1)) (s : Fin (n + 1) → ℝ)
    (hs : ∀ i, s i * s i = 1) :
    C145PhysicalFrame.ColumnOrthonormal (fun v i => s i * Q v (e i)) := by
  intro i j
  calc
    (∑ v, (s i * Q v (e i)) * (s j * Q v (e j))) =
        s i * s j * (∑ v, Q v (e i) * Q v (e j)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
    _ = if i = j then 1 else 0 := by
      rw [hQ]
      by_cases h : i = j
      · subst j; simp [hs]
      · simp [h, e.injective.ne h]

theorem generator_eq_of_eigenframe {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ) (rates : Fin (n + 1) → ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (he : ∀ i, A *ᵥ (fun v => Q v i) = (-rates i) • (fun v => Q v i)) :
    C145CoordinatePermutation.spectralGenerator rates Q = A := by
  funext v u
  have hev : ∀ i, ∑ w, A v w * Q w i = -rates i * Q v i := by
    intro i; exact congrFun (he i) v
  calc
    -(∑ i, rates i * Q v i * Q u i) =
        ∑ i, (∑ w, A v w * Q w i) * Q u i := by
      simp only [hev, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    _ = ∑ w, A v w * (∑ i, Q w i * Q u i) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro w _
      apply Finset.sum_congr rfl; intro i _; ring
    _ = A v u := by
      simp_rw [C145PhysicalFrame.columnOrthonormal_rowComplete Q hQ _ _]
      simp

end C145.OrientedEigenframe

end
