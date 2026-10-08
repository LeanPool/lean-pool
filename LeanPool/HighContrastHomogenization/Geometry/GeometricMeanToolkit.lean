/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.GeometricMean

/-!
# High-contrast homogenization: Geometry.GeometricMeanToolkit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The geometric-mean toolkit

The algebraic rules for the matrix geometric mean: it is symmetric, commutes
with inversion, is equivariant under congruence, is jointly
monotone for the Loewner order, is homogeneous of degree one half in each
argument, and has determinant the geometric mean of the two determinants.

Except for monotonicity, each clause is obtained by exhibiting the candidate as a
positive solution of the Riccati equation of the target pair and appealing to
`eq_matGeomMean_of_riccati`.  Monotonicity is read off the defining formula, and
is where operator monotonicity of the square root enters.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Idempotence, symmetry, inversion -/

/-- The geometric mean of a matrix with itself is that matrix. -/
theorem matGeomMean_self {A : Matrix n n ℝ} (hA : A.PosDef) :
    matGeomMean A A = A := by
  refine (eq_matGeomMean_of_riccati hA hA ?_).symm
  rw [Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hA), Matrix.one_mul]

/-- Inverting the Riccati equation of the pair `(A, B)` gives the Riccati
equation of the pair `(A⁻¹, B⁻¹)` for the inverse mean. -/
theorem inv_riccati {A B X : Matrix n n ℝ} (h : X * A⁻¹ * X = B) :
    X⁻¹ * (A⁻¹)⁻¹ * X⁻¹ = B⁻¹ := by
  rw [← h, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]

/-- **The inverse formula** `(A # B)⁻¹ = A⁻¹ # B⁻¹`. -/
theorem matGeomMean_inv {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (matGeomMean A B)⁻¹ = matGeomMean A⁻¹ B⁻¹ :=
  eq_matGeomMean_of_riccati hA.inv (posDef_matGeomMean hA hB).inv
    (inv_riccati (matGeomMean_riccati hA hB))

/-- **Symmetry** `A # B = B # A`. -/
theorem matGeomMean_comm {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    matGeomMean A B = matGeomMean B A := by
  set X : Matrix n n ℝ := matGeomMean A B with hXdef
  have hX : X.PosDef := posDef_matGeomMean hA hB
  have hXu : IsUnit X.det := isUnit_det_of_posDef hX
  have hBu : IsUnit B.det := isUnit_det_of_posDef hB
  have hric : X * A⁻¹ * X = B := matGeomMean_riccati hA hB
  have hinv : X⁻¹ * A * X⁻¹ = B⁻¹ := by
    have h := inv_riccati hric
    rwa [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hA)] at h
  refine eq_matGeomMean_of_riccati hB hX ?_
  have hstep : X * (X⁻¹ * A * X⁻¹) * X = A := by
    calc X * (X⁻¹ * A * X⁻¹) * X = (X * X⁻¹) * A * (X⁻¹ * X) := by noncomm_ring
      _ = A := by
          rw [Matrix.mul_nonsing_inv _ hXu, Matrix.nonsing_inv_mul _ hXu,
            Matrix.one_mul, Matrix.mul_one]
  rw [← hstep, hinv]

/-! ## Congruence -/

/-- **Congruence equivariance** `(Cᵗ A C) # (Cᵗ B C) = Cᵗ (A # B) C`. -/
theorem matGeomMean_conj {A B C : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (hC : IsUnit C) :
    matGeomMean (Cᴴ * A * C) (Cᴴ * B * C) = Cᴴ * matGeomMean A B * C := by
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det _).mp hC
  have hCHdet : IsUnit (Cᴴ).det := by
    rw [Matrix.det_conjTranspose]
    simpa using hCdet.star
  have hinj : Function.Injective C.mulVec := Matrix.mulVec_injective_of_isUnit hC
  have hAC : (Cᴴ * A * C).PosDef := hA.conjTranspose_mul_mul_same hinj
  have hX : (Cᴴ * matGeomMean A B * C).PosDef :=
    (posDef_matGeomMean hA hB).conjTranspose_mul_mul_same hinj
  refine (eq_matGeomMean_of_riccati hAC hX ?_).symm
  have hACinv : (Cᴴ * A * C)⁻¹ = C⁻¹ * A⁻¹ * (Cᴴ)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    noncomm_ring
  rw [hACinv]
  calc Cᴴ * matGeomMean A B * C * (C⁻¹ * A⁻¹ * (Cᴴ)⁻¹) * (Cᴴ * matGeomMean A B * C)
      = Cᴴ * matGeomMean A B * (C * C⁻¹) * A⁻¹ * ((Cᴴ)⁻¹ * Cᴴ) *
          matGeomMean A B * C := by noncomm_ring
    _ = Cᴴ * (matGeomMean A B * A⁻¹ * matGeomMean A B) * C := by
        rw [Matrix.mul_nonsing_inv _ hCdet, Matrix.nonsing_inv_mul _ hCHdet]
        noncomm_ring
    _ = Cᴴ * B * C := by rw [matGeomMean_riccati hA hB]

/-! ## Monotonicity -/

/-- The geometric mean is monotone in its second argument. -/
theorem matGeomMean_mono_right {A B₀ B₁ : Matrix n n ℝ} (hA : A.PosDef)
    (hB₀ : B₀.PosDef) (hB₁ : B₁.PosDef) (h : B₀ ≤ B₁) :
    matGeomMean A B₀ ≤ matGeomMean A B₁ := by
  have hRsymm : (matSqrt A⁻¹)ᴴ = matSqrt A⁻¹ := conjTranspose_matSqrt hA.inv.posSemidef
  have hPsymm : (matSqrt A)ᴴ = matSqrt A := conjTranspose_matSqrt hA.posSemidef
  have hnorm : matSqrt A⁻¹ * B₀ * matSqrt A⁻¹ ≤ matSqrt A⁻¹ * B₁ * matSqrt A⁻¹ :=
    conj_le_conj' hRsymm h
  have hroot : matSqrt (matSqrt A⁻¹ * B₀ * matSqrt A⁻¹) ≤
      matSqrt (matSqrt A⁻¹ * B₁ * matSqrt A⁻¹) :=
    matSqrt_le_matSqrt (posDef_normalize hB₀ hA).posSemidef (posDef_normalize hB₁ hA) hnorm
  exact conj_le_conj' hPsymm hroot

/-- **Joint monotonicity** of the geometric mean. -/
theorem matGeomMean_mono {A₀ A₁ B₀ B₁ : Matrix n n ℝ} (hA₀ : A₀.PosDef)
    (hA₁ : A₁.PosDef) (hB₀ : B₀.PosDef) (hB₁ : B₁.PosDef)
    (hA : A₀ ≤ A₁) (hB : B₀ ≤ B₁) :
    matGeomMean A₀ B₀ ≤ matGeomMean A₁ B₁ := by
  have h1 : matGeomMean A₀ B₀ ≤ matGeomMean A₀ B₁ :=
    matGeomMean_mono_right hA₀ hB₀ hB₁ hB
  have h2 : matGeomMean B₁ A₀ ≤ matGeomMean B₁ A₁ :=
    matGeomMean_mono_right hB₁ hA₀ hA₁ hA
  rw [← matGeomMean_comm hA₀ hB₁] at h2
  rw [matGeomMean_comm hB₁ hA₁] at h2
  exact h1.trans h2

/-! ## Homogeneity and the determinant -/

omit [DecidableEq n] in
omit [Fintype n] in
/-- The dilation of a positive definite matrix by a positive scalar is positive
definite. -/
theorem posDef_smul {A : Matrix n n ℝ} (hA : A.PosDef) {c : ℝ} (hc : 0 < c) :
    (c • A).PosDef := hA.smul hc

/-- A real-number step used twice below: an inverse-sandwiched square. -/
private theorem sq_eq_of_inv_mul {x p q : ℝ} (hp : p ≠ 0) (h : x * p⁻¹ * x = q) :
    x ^ 2 = p * q := by
  have h2 : x * p⁻¹ * x * p = q * p := by rw [h]
  have h3 : x * p⁻¹ * x * p = x ^ 2 := by field_simp
  rw [h3] at h2
  rw [h2]; ring

/-- **Homogeneity** `(a A) # (b B) = (a b)^{1/2} (A # B)`. -/
theorem matGeomMean_smul {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    matGeomMean (a • A) (b • B) = Real.sqrt (a * b) • matGeomMean A B := by
  have hab : 0 < a * b := mul_pos ha hb
  have hAu : IsUnit A.det := isUnit_det_of_posDef hA
  set s : ℝ := Real.sqrt (a * b) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hab
  have hss : s * s = a * b := by rw [hsdef]; exact Real.mul_self_sqrt hab.le
  clear_value s
  have hX : (s • matGeomMean A B).PosDef := posDef_smul (posDef_matGeomMean hA hB) hs
  refine (eq_matGeomMean_of_riccati (posDef_smul hA ha) hX ?_).symm
  have hainv : (a • A)⁻¹ = a⁻¹ • A⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hAu,
      mul_inv_cancel₀ ha.ne', one_smul]
  rw [hainv]
  have hscal : s • matGeomMean A B * (a⁻¹ • A⁻¹) * (s • matGeomMean A B) =
      (s * a⁻¹ * s) • (matGeomMean A B * A⁻¹ * matGeomMean A B) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_assoc]
  rw [hscal, matGeomMean_riccati hA hB]
  congr 1
  have hre : s * a⁻¹ * s = s * s * a⁻¹ := by ring
  rw [hre, hss]
  field_simp

/-- **The determinant of the geometric mean** is the geometric mean of the
determinants. -/
theorem det_matGeomMean {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    (matGeomMean A B).det = Real.sqrt (A.det * B.det) := by
  have hX : (matGeomMean A B).PosDef := posDef_matGeomMean hA hB
  have hXpos : 0 < (matGeomMean A B).det := hX.det_pos
  have hApos : 0 < A.det := hA.det_pos
  have hdetinv : (A⁻¹).det = (A.det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hdet := congrArg Matrix.det (matGeomMean_riccati hA hB)
  rw [Matrix.det_mul, Matrix.det_mul, hdetinv] at hdet
  have hsq : (matGeomMean A B).det ^ 2 = A.det * B.det :=
    sq_eq_of_inv_mul (ne_of_gt hApos) hdet
  rw [← hsq, Real.sqrt_sq hXpos.le]

end

end HighContrast
end HCPolySupport
