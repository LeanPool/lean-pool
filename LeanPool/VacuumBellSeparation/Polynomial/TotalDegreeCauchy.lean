/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Polynomial.CauchyTaylorDefs
public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscReconstruction
public import Mathlib.Data.Fintype.Pi

/-!
# Actual total-degree Cauchy truncations

The truncation uses all natural multiindices of total degree below N.
The coefficients are the iterated contour integrals already reconstructed
in `Gaussian.PolydiscReconstruction`. No approximation theorem is an input.
-/

@[expose] public section

open scoped BigOperators

namespace VacuumBellSeparation

open Gaussian



@[simp] theorem mem_multiIndexBelow {d N : ℕ} (k : Fin d → ℕ) :
    k ∈ multiIndexBelow d N ↔ ∑ j, k j < N := by
  classical
  simp only [multiIndexBelow, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    intro j
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans_lt h

@[simp] theorem multiIndexBelow_zero (d : ℕ) : multiIndexBelow d 0 = ∅ := by
  classical
  ext k
  simp

/-- A total-degree geometric tail costs only the full 2^d half-geometric sum. -/
theorem totalDegree_tail_norm_le {d N : ℕ} {M q : ℝ}
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2)
    (a : (Fin d → ℕ) → ℂ) (ha : Summable (fun k => ‖a k‖))
    (hbound : ∀ k, ‖a k‖ ≤ M * q ^ (∑ j, k j)) :
    ‖(∑' k, a k) - ∑ k ∈ multiIndexBelow d N, a k‖ ≤
      M * (2 * q) ^ N * 2 ^ d := by
  classical
  let C := M * (2 * q) ^ N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hg := (hasSum_half_multiIndex d).mul_left C
  have hb (k : {k : Fin d → ℕ // k ∉ multiIndexBelow d N}) :
      ‖a k‖ ≤ C * (1 / 2 : ℝ) ^ (∑ j, k.val j) := by
    have hNk : N ≤ ∑ j, k.val j := by
      simpa only [mem_multiIndexBelow, not_lt] using k.property
    calc
      _ ≤ M * q ^ (∑ j, k.val j) := hbound k
      _ = M * ((2 * q) ^ (∑ j, k.val j) * (1 / 2 : ℝ) ^ (∑ j, k.val j)) := by
        rw [← mul_pow]
        congr 2
        ring
      _ ≤ M * ((2 * q) ^ N * (1 / 2 : ℝ) ^ (∑ j, k.val j)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one (by positivity) (by linarith) hNk) (by positivity)) hM
      _ = C * (1 / 2 : ℝ) ^ (∑ j, k.val j) := by dsimp [C]; ring
  rw [← ha.of_norm.sum_add_tsum_subtype_compl (multiIndexBelow d N),
    add_sub_cancel_left]
  calc
    _ ≤ ∑' k : {k : Fin d → ℕ // k ∉ multiIndexBelow d N}, ‖a k‖ :=
      norm_tsum_le_tsum_norm (ha.subtype _)
    _ ≤ ∑' k : {k : Fin d → ℕ // k ∉ multiIndexBelow d N},
        C * (1 / 2 : ℝ) ^ (∑ j, k.val j) :=
      (ha.subtype _).tsum_le_tsum hb (hg.summable.subtype _)
    _ ≤ ∑' k : Fin d → ℕ, C * (1 / 2 : ℝ) ^ (∑ j, k j) :=
      hg.summable.tsum_subtype_le _ {k | k ∉ multiIndexBelow d N} (fun _ => by positivity)
    _ = M * (2 * q) ^ N * 2 ^ d := hg.tsum_eq



@[simp] theorem cauchyTaylor_zero (d : ℕ) (R : ℝ)
    (F : (Fin d → ℂ) → ℂ) (x : Fin d → ℂ) : cauchyTaylor d 0 R F x = 0 := by
  simp [cauchyTaylor]

/-- Uniform actual remainder on a smaller polydisc. -/
theorem cauchyTaylor_remainder_le (d N : ℕ) {R r M : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R / 2) (hM : 0 ≤ M)
    (F : (Fin d → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc d R, DifferentiableAt ℂ F z)
    (hbound : ∀ z ∈ coordinateClosedPolydisc d R, ‖F z‖ ≤ M)
    (x : Fin d → ℂ) (hx : ∀ j, ‖x j‖ ≤ r) :
    ‖F x - cauchyTaylor d N R F x‖ ≤ M * (2 * (r / R)) ^ N * 2 ^ d := by
  have hx' : ∀ j, ‖x j‖ < R := fun j => (hx j).trans_lt (by linarith)
  obtain ⟨hs, ha⟩ := polydiscCoefficient_expansion d hR hM F hF hbound x hx'
  rw [← hs.tsum_eq]
  apply totalDegree_tail_norm_le hM (div_nonneg hr hR.le)
    ((div_le_iff₀ hR).mpr (by linarith)) _ ha
  intro k
  apply (polydiscCoefficient_monomial_norm_le d hR hM F hbound k x).trans
  rw [← Finset.prod_pow_eq_pow_sum]
  apply mul_le_mul_of_nonneg_left _ hM
  apply Finset.prod_le_prod₀
  · intro j _
    positivity
  · intro j _
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (hx j) hR.le) _

/-- Growth of the finite Taylor polynomial on an arbitrary polydisc. This
is needed on the three unwanted components of the joint spatial region. -/
theorem cauchyTaylor_norm_le (d N : ℕ) {R r M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (F : (Fin d → ℂ) → ℂ)
    (hbound : ∀ z ∈ coordinateClosedPolydisc d R, ‖F z‖ ≤ M)
    (x : Fin d → ℂ) (hx : ∀ j, ‖x j‖ ≤ r) :
    ‖cauchyTaylor d N R F x‖ ≤ M * (2 * max 1 (r / R)) ^ N * 2 ^ d := by
  classical
  let B := max 1 (r / R)
  let C := M * (2 * B) ^ N
  have hB : 1 ≤ B := le_max_left _ _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hg := (hasSum_half_multiIndex d).mul_left C
  have hb (k : Fin d → ℕ) (hk : k ∈ multiIndexBelow d N) :
      ‖polydiscCoefficient d R F k * ∏ j, x j ^ k j‖ ≤
        C * (1 / 2 : ℝ) ^ (∑ j, k j) := by
    have hkN := (mem_multiIndexBelow k).mp hk
    calc
      _ ≤ M * ∏ j, (‖x j‖ / R) ^ k j :=
        polydiscCoefficient_monomial_norm_le d hR hM F hbound k x
      _ ≤ M * ∏ j, B ^ k j := by
        apply mul_le_mul_of_nonneg_left _ hM
        apply Finset.prod_le_prod₀
        · intro j _
          positivity
        · intro j _
          exact pow_le_pow_left₀ (by positivity)
            ((div_le_div_of_nonneg_right (hx j) hR.le).trans (le_max_right _ _)) _
      _ = M * B ^ (∑ j, k j) := by rw [Finset.prod_pow_eq_pow_sum]
      _ = M * ((2 * B) ^ (∑ j, k j) * (1 / 2 : ℝ) ^ (∑ j, k j)) := by
        rw [← mul_pow]
        congr 2
        ring
      _ ≤ M * ((2 * B) ^ N * (1 / 2 : ℝ) ^ (∑ j, k j)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) hkN.le)
            (by positivity)) hM
      _ = C * (1 / 2 : ℝ) ^ (∑ j, k j) := by dsimp [C]; ring
  calc
    _ ≤ ∑ k ∈ multiIndexBelow d N,
        ‖polydiscCoefficient d R F k * ∏ j, x j ^ k j‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ multiIndexBelow d N, C * (1 / 2 : ℝ) ^ (∑ j, k j) :=
      Finset.sum_le_sum hb
    _ ≤ ∑' k : Fin d → ℕ, C * (1 / 2 : ℝ) ^ (∑ j, k j) :=
      hg.summable.sum_le_tsum _ (fun _ _ => by positivity)
    _ = M * (2 * max 1 (r / R)) ^ N * 2 ^ d := hg.tsum_eq

end VacuumBellSeparation
