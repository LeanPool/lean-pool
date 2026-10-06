/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.RelativeSize
public import LeanPool.HighContrastHomogenization.Geometry.SqrtOrder

/-!
# High-contrast homogenization: Geometry.GeometricMean

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The matrix geometric mean

For positive matrices `A` and `B` of the same size the reference text sets
`A # B := A^{1/2}(A^{-1/2} B A^{-1/2})^{1/2} A^{1/2}` and characterizes it as the
unique positive solution `X` of the Riccati equation `X A^{-1} X = B`; the mean
and its properties are the ones used in `p.global.selection`.  This file carries
out that characterization and the algebraic rules that follow from it: symmetry,
the inverse formula, congruence, joint monotonicity, homogeneity, and the
determinant.

The characterization is the substitution `Y := A^{-1/2} X A^{-1/2}`, under which
`X A^{-1} X = B` becomes `Y^2 = A^{-1/2} B A^{-1/2}`; since a positive matrix has
exactly one positive square root, the solution is unique and is the displayed
formula.  Every clause of the toolkit except monotonicity is then a one-line
manipulation of the Riccati equation followed by uniqueness.  Monotonicity uses
operator monotonicity of the square root, which is `matSqrt_le_matSqrt`.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix geometric mean `A # B = A^{1/2}(A^{-1/2} B A^{-1/2})^{1/2} A^{1/2}`
of the reference text. -/
@[expose]
def matGeomMean (A B : Matrix n n ℝ) : Matrix n n ℝ :=
  matSqrt A * matSqrt (matSqrt A⁻¹ * B * matSqrt A⁻¹) * matSqrt A

/-! ## Bookkeeping for the two square roots -/

section Roots

variable {A : Matrix n n ℝ}

/-- The inverse square root cancels the square root. -/
theorem matSqrt_inv_mul_matSqrt (hA : A.PosDef) :
    matSqrt A⁻¹ * matSqrt A = 1 := by
  rw [matSqrt_inv hA]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt hA))

/-- The square root cancels the inverse square root. -/
theorem matSqrt_mul_matSqrt_inv (hA : A.PosDef) :
    matSqrt A * matSqrt A⁻¹ = 1 := by
  rw [matSqrt_inv hA]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt hA))

/-- The inverse square root squares to the inverse. -/
theorem matSqrt_inv_mul_self (hA : A.PosDef) :
    matSqrt A⁻¹ * matSqrt A⁻¹ = A⁻¹ :=
  (matSqrt_spec hA.inv.posSemidef).2

/-- The square root is symmetric. -/
theorem conjTranspose_matSqrt {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (matSqrt A)ᴴ = matSqrt A := (matSqrt_spec hA).1.isHermitian

end Roots

/-! ## The Riccati characterization -/

/-- The geometric mean is positive definite. -/
theorem posDef_matGeomMean {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (matGeomMean A B).PosDef := by
  have hC : (matSqrt A⁻¹ * B * matSqrt A⁻¹).PosDef := posDef_normalize hB hA
  have hroot : (matSqrt (matSqrt A⁻¹ * B * matSqrt A⁻¹)).PosDef := posDef_matSqrt hC
  have hc := hroot.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit (isUnit_matSqrt hA))
  rwa [conjTranspose_matSqrt hA.posSemidef] at hc

/-- The algebraic core of the Riccati identity, with the two roots abstracted:
`P` and `R` are inverse to one another and `S` squares to `R B R`. -/
private theorem riccati_of_roots {P R S B : Matrix n n ℝ}
    (hPR : P * R = 1) (hRP : R * P = 1) (hSS : S * S = R * B * R) :
    P * S * P * (R * R) * (P * S * P) = B := by
  calc P * S * P * (R * R) * (P * S * P)
      = P * S * ((P * R) * (R * P)) * S * P := by noncomm_ring
    _ = P * (S * S) * P := by rw [hPR, hRP]; noncomm_ring
    _ = (P * R) * B * (R * P) := by rw [hSS]; noncomm_ring
    _ = B := by rw [hPR, hRP, Matrix.one_mul, Matrix.mul_one]

/-- **The Riccati equation**: the geometric mean solves `X A^{-1} X = B`. -/
theorem matGeomMean_riccati {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    matGeomMean A B * A⁻¹ * matGeomMean A B = B := by
  have hSS : matSqrt (matSqrt A⁻¹ * B * matSqrt A⁻¹) *
      matSqrt (matSqrt A⁻¹ * B * matSqrt A⁻¹) = matSqrt A⁻¹ * B * matSqrt A⁻¹ :=
    (matSqrt_spec (posDef_normalize hB hA).posSemidef).2
  have key := riccati_of_roots (matSqrt_mul_matSqrt_inv hA) (matSqrt_inv_mul_matSqrt hA) hSS
  rw [matSqrt_inv_mul_self hA] at key
  rw [matGeomMean]
  exact key

/-- **Riccati uniqueness.**  A positive solution of `X A^{-1} X = B` is the
geometric mean. -/
theorem eq_matGeomMean_of_riccati {A B X : Matrix n n ℝ} (hA : A.PosDef)
    (hX : X.PosDef) (h : X * A⁻¹ * X = B) : X = matGeomMean A B := by
  set R : Matrix n n ℝ := matSqrt A⁻¹ with hRdef
  have hRsymm : Rᴴ = R := conjTranspose_matSqrt hA.inv.posSemidef
  have hRR : R * R = A⁻¹ := matSqrt_inv_mul_self hA
  have hRu : IsUnit R := isUnit_matSqrt hA.inv
  set Y : Matrix n n ℝ := R * X * R with hYdef
  have hY : Y.PosDef := by
    have hc := hX.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hRu)
    rwa [hRsymm] at hc
  have hYY : Y * Y = R * B * R := by
    rw [hYdef, ← h]
    calc R * X * R * (R * X * R) = R * X * (R * R) * X * R := by noncomm_ring
      _ = R * (X * A⁻¹ * X) * R := by rw [hRR]; noncomm_ring
  have hBpd : B.PosDef := by
    have hc := hA.inv.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hX.isUnit)
    rw [hX.isHermitian] at hc
    rwa [h] at hc
  have hRBRpsd : (R * B * R).PosSemidef := by
    have hc := hBpd.posSemidef.conjTranspose_mul_mul_same R
    rwa [hRsymm] at hc
  have hYsqrt : matSqrt (R * B * R) = Y := matSqrt_eq hRBRpsd hY.posSemidef hYY
  have hAcancel : matSqrt A * R = 1 := matSqrt_mul_matSqrt_inv hA
  have hAcancel' : R * matSqrt A = 1 := matSqrt_inv_mul_matSqrt hA
  calc X = (matSqrt A * R) * X * (R * matSqrt A) := by
        rw [hAcancel, hAcancel', Matrix.one_mul, Matrix.mul_one]
    _ = matSqrt A * (R * X * R) * matSqrt A := by noncomm_ring
    _ = matSqrt A * matSqrt (R * B * R) * matSqrt A := by rw [← hYdef, hYsqrt]
    _ = matGeomMean A B := by rw [matGeomMean, hRdef]

/-- **The Riccati characterization, existence and uniqueness.**  The geometric
mean is the unique positive solution of the Riccati equation. -/
theorem existsUnique_riccati {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    ∃! X : Matrix n n ℝ, X.PosDef ∧ X * A⁻¹ * X = B :=
  ⟨matGeomMean A B, ⟨posDef_matGeomMean hA hB, matGeomMean_riccati hA hB⟩,
    fun _ hY => eq_matGeomMean_of_riccati hA hY.1 hY.2⟩

end

end HighContrast
end HCPolySupport
