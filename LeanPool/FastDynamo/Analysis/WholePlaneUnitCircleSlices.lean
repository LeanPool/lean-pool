/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WholePlanePiecewiseSliceIBP

/-!
# Coordinate slices of the whole-plane unit circle

This file supplies the geometric input for the coordinate-slice integration-by-parts
argument in `WholePlanePiecewiseSliceIBP`.  In the parametrization
`wholePlaneSliceEquiv j (x, t)`, the second real variable is the physical coordinate selected
by `j`, while `x` is the remaining transverse coordinate.  Consequently the squared norm is
`x ^ 2 + t ^ 2`, and the values of `t` at which the slice meets the unit circle form a set of
cardinality at most two.

No Sobolev, integration-by-parts, or Ponomarenko-specific assertion is made here.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Metric Set

/-- On every coordinate slice, the selected physical coordinate is the inner variable. -/
@[simp] theorem wholePlaneSliceEquiv_apply_selected
    (j : Fin 2) (x t : ℝ) :
    wholePlaneSliceEquiv j (x, t) j = t := by
  fin_cases j <;> simp

/-- The squared Euclidean norm in slice coordinates. -/
theorem norm_sq_wholePlaneSliceEquiv
    (j : Fin 2) (x t : ℝ) :
    ‖wholePlaneSliceEquiv j (x, t)‖ ^ 2 = x ^ 2 + t ^ 2 := by
  fin_cases j <;>
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, add_comm]

/-- The affine coordinate slice is a line with velocity `wholePlaneBasis j`. -/
theorem wholePlaneSliceEquiv_eq_base_add
    (j : Fin 2) (x t : ℝ) :
    wholePlaneSliceEquiv j (x, t) =
      wholePlaneSliceEquiv j (x, 0) + t • wholePlaneBasis j := by
  fin_cases j <;>
    ext k <;> fin_cases k <;> simp [wholePlaneBasis]

/-- Differentiating a coordinate slice in its inner variable gives the selected coordinate
basis vector. -/
theorem wholePlaneSliceEquiv_hasDerivAt
    (j : Fin 2) (x t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ wholePlaneSliceEquiv j (x, u))
      (wholePlaneBasis j) t := by
  have h := (hasDerivAt_id (x := t)).smul_const (wholePlaneBasis j)
  have h' := h.const_add (wholePlaneSliceEquiv j (x, 0))
  simpa only [one_smul] using h'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u ↦
      wholePlaneSliceEquiv_eq_base_add j x u)

/-- Values of the inner slice coordinate at which the corresponding point lies on the unit
circle. -/
def wholePlaneUnitCircleSliceExceptional (j : Fin 2) (x : ℝ) : Set ℝ :=
  {t : ℝ | ‖wholePlaneSliceEquiv j (x, t)‖ = 1}

/-- On the affine slice with outer coordinate `x`, the inner coordinate `t` hits the unit circle
exactly when `x² + t² = 1`; this turns the geometric exceptional set into an elementary quadratic
condition. -/
theorem mem_wholePlaneUnitCircleSliceExceptional_iff
    {j : Fin 2} {x t : ℝ} :
    t ∈ wholePlaneUnitCircleSliceExceptional j x ↔ x ^ 2 + t ^ 2 = 1 := by
  change (‖wholePlaneSliceEquiv j (x, t)‖ = 1) ↔ x ^ 2 + t ^ 2 = 1
  constructor
  · intro h
    calc
      x ^ 2 + t ^ 2 = ‖wholePlaneSliceEquiv j (x, t)‖ ^ 2 :=
        (norm_sq_wholePlaneSliceEquiv j x t).symm
      _ = 1 := by rw [h]; norm_num
  · intro h
    have hsq : ‖wholePlaneSliceEquiv j (x, t)‖ ^ 2 = 1 := by
      rw [norm_sq_wholePlaneSliceEquiv]
      exact h
    nlinarith [norm_nonneg (wholePlaneSliceEquiv j (x, t))]

/-- Set-theoretic identification of the geometric exceptional set with the elementary
quadratic fiber already used by the slice-IBP layer. -/
theorem wholePlaneUnitCircleSliceExceptional_eq
    (j : Fin 2) (x : ℝ) :
    wholePlaneUnitCircleSliceExceptional j x =
      {t : ℝ | x ^ 2 + t ^ 2 = 1} := by
  ext t
  exact mem_wholePlaneUnitCircleSliceExceptional_iff

/-- A coordinate line meets the whole-plane unit circle in a finite set. -/
theorem finite_wholePlaneUnitCircleSliceExceptional
    (j : Fin 2) (x : ℝ) :
    (wholePlaneUnitCircleSliceExceptional j x).Finite := by
  rw [wholePlaneUnitCircleSliceExceptional_eq]
  exact finite_setOf_sq_add_sq_eq x 1

/-- In particular, the exceptional set on every coordinate slice is countable, exactly as
required by the one-dimensional off-countable fundamental theorem of calculus. -/
theorem countable_wholePlaneUnitCircleSliceExceptional
    (j : Fin 2) (x : ℝ) :
    (wholePlaneUnitCircleSliceExceptional j x).Countable :=
  (finite_wholePlaneUnitCircleSliceExceptional j x).countable

end

end FastDynamo
