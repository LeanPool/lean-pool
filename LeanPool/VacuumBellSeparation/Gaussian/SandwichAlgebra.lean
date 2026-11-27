/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Matrix algebra of the inverse Gaussian sandwich

Appendix A, between `eq:Ctau-inverse` and `eq:trace-derived`, uses a matrix
inverse identity and its determinant. Here `C` corresponds to `V_ρ + I/2`,
`T` to the positive diagonal dilation `𝕋_σ`, and `S` to `T² - I`.
The gap `T S⁻¹ T - C` then equals `T_τ - V_ρ`.

We prove the algebra for arbitrary invertible real matrices `S,T,C` and an
invertible gap, without requiring commutation. This proves only the matrix
algebra, not the Gaussian kernel, trace-class criterion, thermal covariance
identification, or positivity of the gap.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The precision matrix in the inverse sandwich, with `S = T² - I`. -/
noncomputable def sandwichPrecision (S T C : Matrix n n ℝ) : Matrix n n ℝ :=
  -S + T * C⁻¹ * T

/-- The matrix gap controlling existence of the inverse sandwich. -/
noncomputable def sandwichGap (S T C : Matrix n n ℝ) : Matrix n n ℝ :=
  T * S⁻¹ * T - C

/-- Exact factorization of the sandwich precision. In the Gaussian application,
it is the matrix-algebra input to both the covariance and determinant formulas. -/
theorem sandwichPrecision_factorization (S T C : Matrix n n ℝ)
    (hS : IsUnit S) (hT : IsUnit T) (hC : IsUnit C) :
    sandwichPrecision S T C = T * C⁻¹ * sandwichGap S T C * T⁻¹ * S := by
  have hSi := S.nonsing_inv_mul ((isUnit_iff_isUnit_det S).mp hS)
  have hTi := T.mul_nonsing_inv ((isUnit_iff_isUnit_det T).mp hT)
  have hCi := C.nonsing_inv_mul ((isUnit_iff_isUnit_det C).mp hC)
  symm
  calc
    T * C⁻¹ * sandwichGap S T C * T⁻¹ * S =
        T * C⁻¹ * T * (S⁻¹ * (T * T⁻¹) * S) - T * (C⁻¹ * C) * T⁻¹ * S := by
      dsimp [sandwichGap]
      noncomm_ring
    _ = sandwichPrecision S T C := by
      simp only [hTi, hCi, mul_one, one_mul, hSi]
      dsimp [sandwichPrecision]
      abel

/-- Product form of the inverse precision matrix. -/
theorem sandwichPrecision_inv_factorization (S T C : Matrix n n ℝ)
    (hS : IsUnit S) (hT : IsUnit T) (hC : IsUnit C) :
    (sandwichPrecision S T C)⁻¹ = S⁻¹ * T * (sandwichGap S T C)⁻¹ * C * T⁻¹ := by
  rw [sandwichPrecision_factorization S T C hS hT hC]
  simp only [Matrix.mul_inv_rev,
    T.nonsing_inv_nonsing_inv ((isUnit_iff_isUnit_det T).mp hT),
    C.nonsing_inv_nonsing_inv ((isUnit_iff_isUnit_det C).mp hC), mul_assoc]

/-- The Woodbury covariance formula used in Appendix A. With `S = T²-I`
and `L = T S⁻¹ = S⁻¹ T`, the conclusion is `C_τ = -S⁻¹ + L gap⁻¹ L`.
Invertibility assumptions here are ordinary matrix-domain conditions and
do not assume a Gaussian or operator-algebra result. -/
theorem sandwichPrecision_inv (S T C : Matrix n n ℝ)
    (hS : IsUnit S) (hT : IsUnit T) (hC : IsUnit C)
    (hgap : IsUnit (sandwichGap S T C)) :
    (sandwichPrecision S T C)⁻¹ =
      -S⁻¹ + S⁻¹ * T * (sandwichGap S T C)⁻¹ * T * S⁻¹ := by
  have hTi := T.mul_nonsing_inv ((isUnit_iff_isUnit_det T).mp hT)
  have hDi := (sandwichGap S T C).nonsing_inv_mul
    ((isUnit_iff_isUnit_det _).mp hgap)
  have hCeq : C = T * S⁻¹ * T - sandwichGap S T C := by
    dsimp [sandwichGap]
    abel
  rw [sandwichPrecision_inv_factorization S T C hS hT hC]
  calc
    S⁻¹ * T * (sandwichGap S T C)⁻¹ * C * T⁻¹ =
        S⁻¹ * T * (sandwichGap S T C)⁻¹ * (T * S⁻¹ * T - sandwichGap S T C) * T⁻¹ :=
      congrArg (fun X => S⁻¹ * T * (sandwichGap S T C)⁻¹ * X * T⁻¹) hCeq
    _ = S⁻¹ * T * (sandwichGap S T C)⁻¹ * T * S⁻¹ * (T * T⁻¹) -
        S⁻¹ * T * ((sandwichGap S T C)⁻¹ * sandwichGap S T C) * T⁻¹ := by
      noncomm_ring
    _ = -S⁻¹ + S⁻¹ * T * (sandwichGap S T C)⁻¹ * T * S⁻¹ := by
      rw [hTi, hDi]
      simp only [mul_one]
      rw [mul_assoc S⁻¹ T T⁻¹, hTi, mul_one]
      abel

/-- The determinant ratio occurring in the Gaussian trace formula. This is a
matrix identity alone; the relation to an operator trace is a separate theorem. -/
theorem sandwichPrecision_inv_det_div (S T C : Matrix n n ℝ)
    (hS : IsUnit S) (hT : IsUnit T) (hC : IsUnit C)
    (hgap : IsUnit (sandwichGap S T C)) :
    (sandwichPrecision S T C)⁻¹.det / C.det =
      1 / (S.det * (sandwichGap S T C).det) := by
  have hSd := ((isUnit_iff_isUnit_det S).mp hS).ne_zero
  have hTd := ((isUnit_iff_isUnit_det T).mp hT).ne_zero
  have hCd := ((isUnit_iff_isUnit_det C).mp hC).ne_zero
  have hDd := ((isUnit_iff_isUnit_det _).mp hgap).ne_zero
  rw [sandwichPrecision_inv_factorization S T C hS hT hC]
  simp only [det_mul, det_nonsing_inv, Ring.inverse_eq_inv]
  field_simp [hSd, hTd, hCd, hDd]

/-- A covariance perturbation normalized by an invertible square-root factor
`R`: the manuscript specializes to `R = H^(1/2)` and `D = V_ρ - V_σ`. -/
noncomputable def normalizedPerturbation (R D : Matrix n n ℝ) : Matrix n n ℝ :=
  R⁻¹ * D * R⁻¹

/-- The exact factorization `T_τ - V_ρ = H - (V_ρ - V_σ) = H^(1/2) (I-Z) H^(1/2)`, expressed
algebraically for an arbitrary invertible square-root factor `R`. -/
theorem perturbation_factorization (R D : Matrix n n ℝ) (hR : IsUnit R) :
    R * R - D = R * (1 - normalizedPerturbation R D) * R := by
  have hRi := R.mul_nonsing_inv ((isUnit_iff_isUnit_det R).mp hR)
  have hiR := R.nonsing_inv_mul ((isUnit_iff_isUnit_det R).mp hR)
  symm
  calc
    R * (1 - normalizedPerturbation R D) * R =
        R * R - (R * R⁻¹) * D * (R⁻¹ * R) := by
      dsimp [normalizedPerturbation]
      noncomm_ring
    _ = R * R - D := by rw [hRi, hiR, one_mul, mul_one]

/-- Determinant factorization used in the last equality of Appendix A's
`eq:trace-derived`. -/
theorem det_perturbation (R D : Matrix n n ℝ) (hR : IsUnit R) :
    (R * R - D).det = (R * R).det * (1 - normalizedPerturbation R D).det := by
  rw [perturbation_factorization R D hR]
  simp only [det_mul]
  ring

/-- The normalized determinant ratio, without assuming positivity or a
Gaussian trace formula. -/
theorem det_div_det_perturbation (R D : Matrix n n ℝ) (hR : IsUnit R) :
    (R * R).det / (R * R - D).det =
      1 / (1 - normalizedPerturbation R D).det := by
  have hRd := ((isUnit_iff_isUnit_det R).mp hR).ne_zero
  rw [det_perturbation R D hR, det_mul]
  by_cases hz : (1 - normalizedPerturbation R D).det = 0
  · simp [hz]
  · field_simp [hRd, hz]

end VacuumBellSeparation.Gaussian
