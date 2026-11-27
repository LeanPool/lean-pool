/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.ClosedSpectralThreshold

/-! Scalar Darboux bounds for the exact uniform spectral-threshold grid. -/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory ReflectionApprox

theorem antitone_threshold_integral_bounds {f : ℝ → ℝ} (hf : Antitone f)
    {N : ℕ} (hN : 0 < N) :
    0 ≤ (2 / (N : ℝ)) * (∑ k ∈ Finset.range N, f (threshold N k)) -
      (∫ u in (-1 : ℝ)..1, f u) ∧
    (2 / (N : ℝ)) * (∑ k ∈ Finset.range N, f (threshold N k)) -
      (∫ u in (-1 : ℝ)..1, f u) ≤
        (2 / (N : ℝ)) * (f (-1) - f 1) := by
  have hlow (k : ℕ) :
      (2 / (N : ℝ)) * f (threshold N (k + 1)) ≤
        ∫ u in threshold N k..threshold N (k + 1), f u := by
    have h := intervalIntegral.integral_mono_on (μ := volume)
      (f := fun _ : ℝ => f (threshold N (k + 1))) (g := f) (threshold_le_succ N k)
      intervalIntegrable_const hf.intervalIntegrable
      (fun u hu => hf hu.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, threshold_succ,
      add_sub_cancel_left] using h
  have hupp (k : ℕ) :
      (∫ u in threshold N k..threshold N (k + 1), f u) ≤
        (2 / (N : ℝ)) * f (threshold N k) := by
    have h := intervalIntegral.integral_mono_on (μ := volume)
      (f := f) (g := fun _ : ℝ => f (threshold N k)) (threshold_le_succ N k)
      hf.intervalIntegrable intervalIntegrable_const
      (fun u hu => hf hu.1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, threshold_succ,
      add_sub_cancel_left] using h
  have hsum :
      (∑ k ∈ Finset.range N, ∫ u in threshold N k..threshold N (k + 1), f u) =
        ∫ u in (-1 : ℝ)..1, f u := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun _ _ => hf.intervalIntegrable), threshold_zero, threshold_self hN]
  have hl := Finset.sum_le_sum (s := Finset.range N) (fun k _ => hlow k)
  have hu := Finset.sum_le_sum (s := Finset.range N) (fun k _ => hupp k)
  rw [← Finset.mul_sum, hsum] at hl
  rw [← Finset.mul_sum, hsum] at hu
  have htel (n : ℕ) :
      (∑ k ∈ Finset.range n, (f (threshold N k) - f (threshold N (k + 1)))) =
        f (threshold N 0) - f (threshold N n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have he : (2 / (N : ℝ)) * (∑ k ∈ Finset.range N, f (threshold N k)) -
      (2 / (N : ℝ)) * (∑ k ∈ Finset.range N, f (threshold N (k + 1))) =
        (2 / (N : ℝ)) * (f (-1) - f 1) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, htel N, threshold_zero, threshold_self hN]
  constructor <;> linarith

end VacuumBellSeparation
