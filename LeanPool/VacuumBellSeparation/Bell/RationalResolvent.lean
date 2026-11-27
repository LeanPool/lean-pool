/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The uniformly bounded quadratic resolvent of a selfadjoint operator

The actual real functional calculus of x ↦ (1+x²)⁻¹ gives the inverse of
1+A². Both this resolvent and its product with A have norm at most one,
uniformly over all bounded selfadjoint A, with no common bound on ‖A‖.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Quadratic resolvent function given by `1 / (1 + x ^ 2)`. -/
noncomputable def quadraticResolventFunction (x : ℝ) : ℝ := 1 / (1 + x ^ 2)

theorem quadraticResolventFunction_continuous : Continuous quadraticResolventFunction := by
  change Continuous (fun x : ℝ => 1 / (1 + x ^ 2))
  apply continuous_const.div (continuous_const.add (continuous_id.pow 2))
  intro x
  exact (show 0 < (1 : ℝ) + x ^ 2 by positivity).ne'

theorem quadraticResolventFunction_bounds (x : ℝ) :
    0 ≤ quadraticResolventFunction x ∧ quadraticResolventFunction x ≤ 1 := by
  constructor
  · unfold quadraticResolventFunction; positivity
  · rw [quadraticResolventFunction, div_le_one (by positivity : 0 < 1 + x ^ 2)]
    nlinarith [sq_nonneg x]

/-- Quadratic resolvent obtained from `cfc`. -/
noncomputable def quadraticResolvent (A : H →L[ℂ] H) : H →L[ℂ] H :=
  cfc quadraticResolventFunction A

theorem quadraticResolvent_nonneg (A : H →L[ℂ] H) : 0 ≤ quadraticResolvent A :=
  cfc_nonneg (fun x _ => (quadraticResolventFunction_bounds x).1)

theorem quadraticResolvent_le_one {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    quadraticResolvent A ≤ 1 := by
  have h := (cfc_le_iff quadraticResolventFunction (fun _ : ℝ => 1) A
    quadraticResolventFunction_continuous.continuousOn continuousOn_const hA).mpr
    (fun x _ => (quadraticResolventFunction_bounds x).2)
  simpa only [quadraticResolvent, cfc_const_one ℝ A hA] using h

theorem quadraticResolvent_norm_le (A : H →L[ℂ] H) : ‖quadraticResolvent A‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (quadraticResolventFunction_bounds x).1]
  exact (quadraticResolventFunction_bounds x).2

theorem quadraticResolvent_mul_denominator {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    quadraticResolvent A * (1 + A ^ 2) = 1 := by
  have hden : cfc (fun x : ℝ => 1 + x ^ 2) A = 1 + A ^ 2 := by
    rw [cfc_add A (fun _ : ℝ => 1) (fun x : ℝ => x ^ 2)
      continuousOn_const (continuous_id.pow 2).continuousOn,
      cfc_const_one ℝ A hA, cfc_pow_id A 2 hA]
  rw [quadraticResolvent, ← hden, ← cfc_mul quadraticResolventFunction
    (fun x : ℝ => 1 + x ^ 2) A quadraticResolventFunction_continuous.continuousOn
    (by fun_prop)]
  calc
    cfc (fun x : ℝ => quadraticResolventFunction x * (1 + x ^ 2)) A =
        cfc (fun _ : ℝ => 1) A := cfc_congr (fun x _ => by
          exact div_mul_cancel₀ 1 (by positivity : (1 + x ^ 2 : ℝ) ≠ 0))
    _ = 1 := cfc_const_one ℝ A hA

theorem denominator_mul_quadraticResolvent {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    (1 + A ^ 2) * quadraticResolvent A = 1 := by
  have h := congrArg star (quadraticResolvent_mul_denominator hA)
  simpa only [star_mul, star_add, star_one, star_pow, hA.star_eq,
    (quadraticResolvent_nonneg A).isSelfAdjoint.star_eq] using h

theorem quadraticResolvent_mul_norm_le {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    ‖quadraticResolvent A * A‖ ≤ 1 := by
  have he : quadraticResolvent A * A = cfc (fun x : ℝ => quadraticResolventFunction x * x) A := by
    change cfc quadraticResolventFunction A * A =
      cfc (fun x : ℝ => quadraticResolventFunction x * id x) A
    rw [cfc_mul quadraticResolventFunction id A
      quadraticResolventFunction_continuous.continuousOn continuousOn_id,
      cfc_id ℝ A hA]
  rw [he]
  apply norm_cfc_le zero_le_one
  intro x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (quadraticResolventFunction_bounds x).1,
    quadraticResolventFunction, one_div_mul_eq_div, div_le_one (by positivity : 0 < 1 + x ^ 2)]
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

/-- The noncommuting resolvent identity with the two strongly controlled differences. -/
theorem quadraticResolvent_sub {A B : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    quadraticResolvent A - quadraticResolvent B =
      (quadraticResolvent A * A) * (B - A) * quadraticResolvent B +
        quadraticResolvent A * (B - A) * B * quadraticResolvent B := by
  calc
    quadraticResolvent A - quadraticResolvent B =
        quadraticResolvent A * (1 + B ^ 2) * quadraticResolvent B -
          quadraticResolvent A * (1 + A ^ 2) * quadraticResolvent B := by
      rw [mul_assoc, denominator_mul_quadraticResolvent hB,
        quadraticResolvent_mul_denominator hA, mul_one, one_mul]
    _ = _ := by noncomm_ring

end VacuumBellSeparation
