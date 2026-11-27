/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointPolynomialErrorOperators

/-!
# The actual polynomial obtained by subtracting two error patches

The zero-order Taylor polynomial vanishes. Subtraction therefore removes
the component kernel identically, before the genuine cutoff partition
reconstructs the original physical polynomial on the joint test support.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian MvPolynomial Metric Set
open scoped SchwartzMap

@[simp] theorem jointMidpointPolynomial_zero (F : (Fin 6 → ℂ) → ℂ) :
    jointMidpointPolynomial F 0 = 0 := by
  simp [jointMidpointPolynomial, jointMidpointOriented, cauchyTaylorPolynomial]

theorem jointCenterIndex_separated {s : ℝ} (hs : 600 ≤ s) :
    5 ≤ dist (jointCenterIndex s 0) (jointCenterIndex s 1) := by
  have h := PiLp.norm_apply_le (jointCenterIndex s 0 - jointCenterIndex s 1) (0 : Fin 3)
  have hs₀ : 0 ≤ s := by linarith
  change ‖(0 : ℝ) - (s + 0)‖ ≤ ‖jointCenterIndex s 0 - jointCenterIndex s 1‖ at h
  simp only [add_zero, zero_sub, norm_neg, Real.norm_eq_abs, abs_of_nonneg hs₀] at h
  rw [dist_eq_norm]
  linarith

theorem jointPolynomialErrorPatch_sub_apply {s : ℝ} (hs : 600 ≤ s)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), AnalyticAt ℂ F z)
    (n : ℕ) (i j : Fin 2) (x : JointKernelSpace) :
    (jointPolynomialErrorPatch hs F hF 0 i j - jointPolynomialErrorPatch hs F hF n i j) x =
      jointSmoothCutoff (jointCenterIndex s i) (jointCenterIndex s j) x *
        eval (jointPhysicalMidpoint s (jointComplexCoordinates x))
          (jointMidpointPolynomial F n) := by
  change jointSmoothCutoff (jointCenterIndex s i) (jointCenterIndex s j) x *
      jointRealPolynomialError F s 0 (decide (i = 1)) (decide (j = 1)) x -
    jointSmoothCutoff (jointCenterIndex s i) (jointCenterIndex s j) x *
      jointRealPolynomialError F s n (decide (i = 1)) (decide (j = 1)) x = _
  simp only [jointRealPolynomialError, Function.comp_apply, jointPhysicalPolynomialError,
    jointMidpointPolynomial_zero, map_zero, sub_zero]
  ring

theorem jointPolynomialErrorPatch_sub_sum {s : ℝ} (hs : 600 ≤ s)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), AnalyticAt ℂ F z)
    (n : ℕ) (x : JointKernelSpace)
    (hx : x.fst ∈ closedBall (jointCenterIndex s 0) 1 ∪ closedBall (jointCenterIndex s 1) 1)
    (hy : x.snd ∈ closedBall (jointCenterIndex s 0) 1 ∪ closedBall (jointCenterIndex s 1) 1) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      (jointPolynomialErrorPatch hs F hF 0 i j - jointPolynomialErrorPatch hs F hF n i j) x) =
        eval (jointPhysicalMidpoint s (jointComplexCoordinates x))
          (jointMidpointPolynomial F n) := by
  simp only [jointPolynomialErrorPatch_sub_apply, jointSmoothCutoff_apply]
  calc
    _ = ((∑ i : Fin 2, ((jointUnitCutoffTest (jointCenterIndex s i)).1 x.fst : ℂ)) *
        (∑ j : Fin 2, ((jointUnitCutoffTest (jointCenterIndex s j)).1 x.snd : ℂ))) *
          eval (jointPhysicalMidpoint s (jointComplexCoordinates x))
            (jointMidpointPolynomial F n) := by
      rw [Fintype.sum_mul_sum]
      simp only [Finset.sum_mul]
    _ = _ := by
      rw [jointUnitCutoffTest_sum_eq_one _ (jointCenterIndex_separated hs) _ hx,
        jointUnitCutoffTest_sum_eq_one _ (jointCenterIndex_separated hs) _ hy, one_mul, one_mul]

end VacuumBellSeparation
