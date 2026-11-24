/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.TriangularSeries

/-!
# Right logarithmic derivative of a positive formal exponential

The auxiliary exponential curve identities descend through finite evaluation
to each total degree. The adjoint and exponential factors remain as blocks.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PowerSeries

variable {A : Type*} [Ring A] [Algebra ℚ A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Formal exponential has the negative exponential as a right inverse. -/
theorem formalExp_mul_neg (W : PowerSeries A) (hW : constantCoeff W = 0) :
    formalExp W * formalExp (-W) = 1 := by
  have h := congrArg evaluateTriangular (exponentialCurve_mul_neg W)
  rw [evaluateTriangular_mul _ _ (triangular_exponentialCurve W hW)
    (triangular_exponentialCurve (-W) (by simp [hW])),
    evaluateTriangular_exponentialCurve W hW,
    evaluateTriangular_exponentialCurve (-W) (by simp [hW]), evaluateTriangular_one] at h
  exact h

/-- Every homogeneous coefficient of formal conjugation is a finite adjoint sum. -/
theorem coeff_formalExp_conjugate (W V : PowerSeries A) (hW : constantCoeff W = 0)
    (n : ℕ) :
    coeff n (formalExp W * V * formalExp (-W)) =
      ∑ j ∈ range (n + 1), (Nat.factorial j : ℚ)⁻¹ •
        coeff n ((LieAlgebra.ad ℚ (PowerSeries A) W ^ j) V) := by
  have hF : evaluateTriangular (exponentialCurve W * C V * exponentialCurve (-W)) =
      formalExp W * V * formalExp (-W) := by
    rw [evaluateTriangular_mul _ _
      ((triangular_exponentialCurve W hW).mul (triangular_C V))
      (triangular_exponentialCurve (-W) (by simp [hW])),
      evaluateTriangular_mul _ _ (triangular_exponentialCurve W hW) (triangular_C V),
      evaluateTriangular_C, evaluateTriangular_exponentialCurve W hW,
      evaluateTriangular_exponentialCurve (-W) (by simp [hW])]
  rw [← hF, coeff_evaluateTriangular]
  simp only [coeff_conjugate_exponentialCurve, coeff_smul]

/-- The differential exponential identity, in every homogeneous degree over a rational algebra. -/
theorem coeff_rightLogarithmicDerivative_formalExp (D : A →ₗ[ℚ] A)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b)
    (W : PowerSeries A) (hW : constantCoeff W = 0) (n : ℕ) :
    coeff n (mapSeriesLinear D (formalExp W) * formalExp (-W)) =
      ∑ j ∈ range n, (Nat.factorial (j + 1) : ℚ)⁻¹ •
        coeff n ((LieAlgebra.ad ℚ (PowerSeries A) W ^ j) (mapSeriesLinear D W)) := by
  have hd := mapSeriesLinear_mul D hD
  have hF : evaluateTriangular
      (mapSeriesLinear (mapSeriesLinear D) (exponentialCurve W) * exponentialCurve (-W)) =
      mapSeriesLinear D (formalExp W) * formalExp (-W) := by
    rw [evaluateTriangular_mul _ _ ((triangular_exponentialCurve W hW).mapSeriesLinear D)
      (triangular_exponentialCurve (-W) (by simp [hW])),
      evaluateTriangular_mapSeriesLinear, evaluateTriangular_exponentialCurve W hW,
      evaluateTriangular_exponentialCurve (-W) (by simp [hW])]
  rw [← hF, coeff_evaluateTriangular, sum_range_succ']
  have hD1 : D 1 = 0 := by
    have h := hD 1 1
    simp only [mul_one, one_mul] at h
    exact add_left_cancel (h.symm.trans (add_zero (D 1)).symm)
  simp only [coeff_succ_rightLogarithmicDerivative (mapSeriesLinear D) hd, coeff_smul]
  simp
  split_ifs <;> simp [hD1]

omit [Algebra ℚ A] in
/-- Powers of a single monomial need no commutativity of the coefficient algebra. -/
theorem monomial_pow_noncomm (m : ℕ) (a : A) (j : ℕ) :
    (PowerSeries.monomial m a) ^ j = PowerSeries.monomial (m * j) (a ^ j) := by
  rw [← Polynomial.coe_monomial, ← Polynomial.coe_pow, Polynomial.monomial_pow]
  simp only [Polynomial.coe_monomial]

/-- The usual exponential curve is the formal exponential of a degree-one series. -/
theorem formalExp_monomial_one (a : A) :
    formalExp (PowerSeries.monomial 1 a) = exponentialCurve a := by
  apply PowerSeries.ext
  intro n
  have hz : constantCoeff (PowerSeries.monomial 1 a) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [PowerSeries.coeff_monomial]
  simp only [formalExp, scalarSeriesApply, coeff_mk, coeff_exp,
    Algebra.algebraMap_self, RingHom.id_apply, one_div]
  simp only [← coeff_positiveSeries_pow]
  rw [positiveSeries_coeff _ hz]
  simp only [monomial_pow_noncomm, one_mul, PowerSeries.coeff_monomial, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq]
  simp [coeff_exponentialCurve]

end FQFP
