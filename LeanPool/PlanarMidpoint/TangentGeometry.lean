/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.Coordinates
public import LeanPool.PlanarMidpoint.ExceptionalGeometry
public import LeanPool.PlanarMidpoint.TangentAlgebra
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Vanishing of exceptional tangent derivatives

The derivative of either rational graph intersects the obstruction kernel
only in zero. Denominators are cleared using the strictly positive squared
trace length; the remaining identities are polynomial certificates.
-/

@[expose] public section

namespace PlanarMidpoint


private theorem kernel_smul (c : Coeff) (z : DerivativeArray) (α β : ℝ)
    (h : Algebra.Kernel (c 0) (c 1) (c 2) (c 3) z) :
    Algebra.Kernel ((α • c) 0) ((α • c) 1) ((α • c) 2) ((α • c) 3) (β • z) := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  simp only [Algebra.Kernel, Pi.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination α * β * h0
  · linear_combination α * β * h1
  · linear_combination α * β * h2
  · linear_combination α * β * h3
  · linear_combination α * β * h4
  · linear_combination α * β * h5
  · linear_combination α * β * h6
  · linear_combination α * β * h7
  · linear_combination α * β * h8
  · linear_combination α * β * h9

private def traceDerivativeArray (A : E →L[ℝ] E) : Fin 4 → ℝ :=
  ![A (vec 1 0) 0, A (vec 1 0) 1, A (vec 0 1) 0, A (vec 0 1) 1]

private theorem traceDerivativeArray_eq_zero (A : E →L[ℝ] E)
    (h : traceDerivativeArray A = 0) : A = 0 := by
  have h0 : A (vec 1 0) = 0 := by
    apply vec_ext
    · simpa [traceDerivativeArray] using congrFun h 0
    · simpa [traceDerivativeArray] using congrFun h 1
  have h1 : A (vec 0 1) = 0 := by
    apply vec_ext
    · simpa [traceDerivativeArray] using congrFun h 2
    · simpa [traceDerivativeArray] using congrFun h 3
  ext v i
  conv_lhs => rw [vec_decomp v]
  simp [h0, h1]

theorem Q_tangent_obstruction_zero {τ : E} (hτ : τ ≠ 0) (A : E →L[ℝ] E)
    (h : ∀ v, obstruction (Q τ) ((QDeriv τ).comp A) v = 0) :
    (QDeriv τ).comp A = 0 := by
  have hρ := radiusSq_ne_zero hτ
  have hk := kernel_of_obstruction_zero (Q τ) ((QDeriv τ).comp A) h
  have hs := kernel_smul (Q τ) (derivativeArray ((QDeriv τ).comp A))
    (radiusSq τ) (radiusSq τ ^ 2) hk
  have hc : radiusSq τ • Q τ =
      ![τ 0 ^ 3, τ 0 ^ 2 * τ 1, τ 0 * τ 1 ^ 2, τ 1 ^ 3] := by
    ext i
    fin_cases i <;> simp [Q] <;> field_simp [hρ]
  have hz : radiusSq τ ^ 2 • derivativeArray ((QDeriv τ).comp A) =
      qTangentArray (τ 0) (τ 1) (traceDerivativeArray A) := by
    ext i
    fin_cases i <;>
      norm_num [derivativeArray, qTangentArray, traceDerivativeArray,
        QDeriv_apply, QNum, ContinuousLinearMap.comp_apply, Pi.smul_apply, smul_eq_mul] <;>
      field_simp [hρ] <;> ring
  rw [hc, hz] at hs
  have hw := q_tangent_kernel (τ 0) (τ 1) (traceDerivativeArray A) hρ hs
  rw [traceDerivativeArray_eq_zero A hw]
  simp

theorem R_tangent_obstruction_zero {τ : E} (hτ : τ ≠ 0) (A : E →L[ℝ] E)
    (h : ∀ v, obstruction (R τ) ((RDeriv τ).comp A) v = 0) :
    (RDeriv τ).comp A = 0 := by
  have hρ := radiusSq_ne_zero hτ
  have hk := kernel_of_obstruction_zero (R τ) ((RDeriv τ).comp A) h
  have hs := kernel_smul (R τ) (derivativeArray ((RDeriv τ).comp A))
    (radiusSq τ) (radiusSq τ ^ 2) hk
  have hc : radiusSq τ • R τ =
      ![3 * τ 0 * τ 1 ^ 2, -2 * τ 0 ^ 2 * τ 1 + τ 1 ^ 3,
        τ 0 ^ 3 - 2 * τ 0 * τ 1 ^ 2, 3 * τ 0 ^ 2 * τ 1] := by
    ext i
    fin_cases i <;> simp [R, Q] <;> field_simp [hρ] <;> simp [radiusSq] <;> ring_nf <;> simp
  have hz : radiusSq τ ^ 2 • derivativeArray ((RDeriv τ).comp A) =
      rTangentArray (τ 0) (τ 1) (traceDerivativeArray A) := by
    ext i
    fin_cases i <;>
      norm_num [derivativeArray, rTangentArray, traceDerivativeArray,
        RDeriv_apply hτ, RNum, ContinuousLinearMap.comp_apply, Pi.smul_apply, smul_eq_mul] <;>
      field_simp [hρ]
  rw [hc, hz] at hs
  have hw := r_tangent_kernel (τ 0) (τ 1) (traceDerivativeArray A) hρ hs
  rw [traceDerivativeArray_eq_zero A hw]
  simp

end PlanarMidpoint
