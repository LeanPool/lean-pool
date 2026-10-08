/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.Meridional
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CIVAxisymmetric.Setting.RotationLemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Meridional Norm

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- The Euclidean norm of a meridional vector `(x₁, 0, x₃)` reduces to the 2D Euclidean norm
of `(x₁, x₃)`. -/
theorem vec3EuclideanNorm_meridional (x₁ x₃ : ℝ) :
    vec3EuclideanNorm (meridional x₁ x₃) = Real.sqrt (x₁ ^ 2 + x₃ ^ 2) := by
  unfold vec3EuclideanNorm meridional
  simp [Fin.sum_univ_three]

/-- A meridional vector lies in the Euclidean ball of radius `r` centred at the origin iff
`x₁² + x₃² < r²` and `r > 0`. For `r ≤ 0` the ball is empty, so the equivalence holds
vacuously on both sides. -/
theorem meridional_mem_vec3Ball_zero_iff (x₁ x₃ r : ℝ) :
    meridional x₁ x₃ ∈ vec3Ball 0 r ↔ x₁ ^ 2 + x₃ ^ 2 < r ^ 2 ∧ 0 < r := by
  have hsq_nonneg : 0 ≤ x₁ ^ 2 + x₃ ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hnorm : vec3EuclideanNorm (meridional x₁ x₃) = Real.sqrt (x₁ ^ 2 + x₃ ^ 2) :=
    vec3EuclideanNorm_meridional x₁ x₃
  simp only [mem_vec3Ball, sub_zero, hnorm]
  constructor
  · intro h
    have hrpos : 0 < r := by
      by_contra! hle
      have hsqrt_nonneg : 0 ≤ Real.sqrt (x₁ ^ 2 + x₃ ^ 2) := Real.sqrt_nonneg _
      linarith only [h, hsqrt_nonneg, hle]
    refine ⟨?_, hrpos⟩
    rwa [Real.sqrt_lt' hrpos] at h
  · rintro ⟨h, hrpos⟩
    rwa [Real.sqrt_lt' hrpos]

/-- A point `(meridional x₁ x₃, t)` lies in the unit cylinder `B(1) × (-1, 0)` iff
`x₁² + x₃² < 1` and `-1 < t < 0`. -/
theorem meridional_mem_unitCylinder_iff (x₁ x₃ t : ℝ) :
    (meridional x₁ x₃, t) ∈ unitCylinder ↔ x₁ ^ 2 + x₃ ^ 2 < 1 ∧ -1 < t ∧ t < 0 := by
  have hsq_nonneg : 0 ≤ x₁ ^ 2 + x₃ ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsqrt : vec3EuclideanNorm (meridional x₁ x₃) = Real.sqrt (x₁ ^ 2 + x₃ ^ 2) :=
    vec3EuclideanNorm_meridional x₁ x₃
  have hpos_one : 0 < (1 : ℝ) := by norm_num
  rw [unitCylinder, spaceTimeSet]
  unfold ParabolicPoint
  rw [Set.mem_prod]
  simp only [mem_vec3Ball, Set.mem_Ioo, sub_zero]
  rw [hsqrt]
  constructor
  · rintro ⟨hnorm_lt_one, hlow, hhigh⟩
    have hsq_lt_one : x₁ ^ 2 + x₃ ^ 2 < 1 := by
      have := (Real.sqrt_lt' hpos_one).mp hnorm_lt_one
      simpa [one_pow] using this
    exact ⟨hsq_lt_one, hlow, hhigh⟩
  · rintro ⟨hsq_lt_one, hlow, hhigh⟩
    have hnorm_lt_one : Real.sqrt (x₁ ^ 2 + x₃ ^ 2) < 1 :=
      (Real.sqrt_lt' hpos_one).mpr (by simpa [one_pow] using hsq_lt_one)
    exact ⟨hnorm_lt_one, hlow, hhigh⟩

end CIV
