/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.Coordinates
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Tensor semantics

Every continuous symmetric trilinear form on the Euclidean plane is uniquely
represented by the four coefficients used in the obstruction calculation.
The trilinear form is curried into three continuous linear maps.
-/

@[expose] public section

noncomputable section

namespace PlanarMidpoint

open scoped ContDiff

/-- Continuous trilinear forms on the Euclidean plane, represented as curried maps. -/
abbrev CubicTensor := E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))

/-- Invariance of a trilinear form under the two adjacent transpositions. -/
def IsTotallySymmetric (T : CubicTensor) : Prop :=
  (∀ u v w, T u v w = T v u w) ∧ (∀ u v w, T u v w = T u w v)

/-- The four independent coordinate values of a symmetric planar cubic tensor. -/
def tensorCoefficients (T : CubicTensor) : Coeff :=
  ![T (vec 1 0) (vec 1 0) (vec 1 0), T (vec 1 0) (vec 1 0) (vec 0 1),
    T (vec 1 0) (vec 0 1) (vec 0 1), T (vec 0 1) (vec 0 1) (vec 0 1)]

theorem tensor_eq_cubic (T : CubicTensor) (hT : IsTotallySymmetric T) (u v w : E) :
    T u v w = cubic (tensorCoefficients T) u v w := by
  have h100 := (hT.1 (vec 0 1) (vec 1 0) (vec 1 0)).trans
    (hT.2 (vec 1 0) (vec 0 1) (vec 1 0))
  have h010 := hT.2 (vec 1 0) (vec 0 1) (vec 1 0)
  have h101 := hT.1 (vec 0 1) (vec 1 0) (vec 0 1)
  have h110 := (hT.2 (vec 0 1) (vec 0 1) (vec 1 0)).trans h101
  conv_lhs => rw [vec_decomp u, vec_decomp v, vec_decomp w]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  simp only [h100, h010, h101, h110, cubic, tensorCoefficients,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

theorem symmetric_tensor_ext {T U : CubicTensor}
    (hT : IsTotallySymmetric T) (hU : IsTotallySymmetric U)
    (h : tensorCoefficients T = tensorCoefficients U) : T = U := by
  ext u v w
  rw [tensor_eq_cubic T hT, tensor_eq_cubic U hU, h]

theorem contDiffAt_tensorCoefficients {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {n : ℕ∞ω} {T : A → CubicTensor} {p : A}
    (hT : ∀ u v w, ContDiffAt ℝ n (fun x => T x u v w) p) :
    ContDiffAt ℝ n (fun x => tensorCoefficients (T x)) p := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> exact hT _ _ _

end PlanarMidpoint
