/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.FormalExpLog
public import LeanPool.SuzukiCancellation.RingTheory.PowerSeries.Noncommutative.ExponentialCurve

/-!
# Finite evaluation of triangular double series

For a double series in `s` and `t`, triangularity means that the coefficient
of `s^j` starts in total degree at least `j` in `t`. Thus evaluation at `s = 1`
is finite in every `t` degree. This construction uses polynomial truncation,
not analytic evaluation or convergence.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PowerSeries

variable {A : Type*} [Ring A]

/-- Transpose the two coefficient indices of an iterated formal series. -/
def transposeSeries (p : PowerSeries (PowerSeries A)) : PowerSeries (PowerSeries A) :=
  mk fun n ↦ mk fun j ↦ coeff n (coeff j p)

@[simp]
theorem coeff_coeff_transposeSeries (p : PowerSeries (PowerSeries A)) (n j : ℕ) :
    coeff j (coeff n (transposeSeries p)) = coeff n (coeff j p) := by
  simp [transposeSeries]

/-- Transposition respects noncommutative multiplication. -/
theorem transposeSeries_mul (p q : PowerSeries (PowerSeries A)) :
    transposeSeries (p * q) = transposeSeries p * transposeSeries q := by
  ext n j
  simp only [coeff_coeff_transposeSeries, coeff_mul, map_sum]
  rw [sum_comm]

/-- Outer exponent `j` has inner total degree at least `j`. -/
def Triangular (p : PowerSeries (PowerSeries A)) : Prop :=
  ∀ j n, n < j → coeff n (coeff j p) = 0

theorem Triangular.mul {p q : PowerSeries (PowerSeries A)}
    (hp : Triangular p) (hq : Triangular q) : Triangular (p * q) := by
  intro j n hnj
  simp only [coeff_mul, map_sum]
  apply sum_eq_zero
  intro ab hab
  have hab' := mem_antidiagonal.mp hab
  apply sum_eq_zero
  intro ik hik
  have hik' := mem_antidiagonal.mp hik
  by_cases hi : ik.1 < ab.1
  · rw [hp _ _ hi, zero_mul]
  · rw [hq ab.2 ik.2 (by lia), mul_zero]

/-- A polynomial realization of the transposed coefficients of a triangular double series. -/
def polynomialTranspose (p : PowerSeries (PowerSeries A)) : PowerSeries (Polynomial A) :=
  mk fun n ↦ trunc (n + 1) (coeff n (transposeSeries p))

theorem map_polynomialTranspose (p : PowerSeries (PowerSeries A)) (hp : Triangular p) :
    PowerSeries.map (Polynomial.coeToPowerSeries.ringHom (R := A)) (polynomialTranspose p) =
      transposeSeries p := by
  ext n j
  simp only [coeff_map, polynomialTranspose, coeff_mk,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, coeff_trunc,
    coeff_coeff_transposeSeries]
  split_ifs with hj
  · rfl
  · exact (hp j n (by lia)).symm

private theorem polynomialTranspose_mul (p q : PowerSeries (PowerSeries A))
    (hp : Triangular p) (hq : Triangular q) :
    polynomialTranspose (p * q) = polynomialTranspose p * polynomialTranspose q := by
  apply PowerSeries.map_injective (Polynomial.coeToPowerSeries.ringHom (R := A))
    (Polynomial.coe_injective A)
  rw [map_mul, map_polynomialTranspose _ (hp.mul hq),
    map_polynomialTranspose _ hp, map_polynomialTranspose _ hq, transposeSeries_mul]

/-- Finite evaluation of the auxiliary variable at one, through each homogeneous degree. -/
def evaluateTriangular (p : PowerSeries (PowerSeries A)) : PowerSeries A :=
  PowerSeries.map (Polynomial.eval₂RingHom' (RingHom.id A) 1 (fun a ↦ Commute.one_right a))
    (polynomialTranspose p)

/-- Evaluation in each homogeneous degree is an explicit finite sum. -/
theorem coeff_evaluateTriangular (p : PowerSeries (PowerSeries A)) (n : ℕ) :
    coeff n (evaluateTriangular p) = ∑ j ∈ range (n + 1), coeff n (coeff j p) := by
  simp only [evaluateTriangular, coeff_map, polynomialTranspose, coeff_mk]
  change (trunc (n + 1) (coeff n (transposeSeries p))).eval₂ (RingHom.id A) 1 = _
  simp only [PowerSeries.eval₂_trunc_eq_sum_range, RingHom.id_apply,
    one_pow, mul_one, coeff_coeff_transposeSeries]

/-- Finite auxiliary evaluation preserves multiplication of triangular double series. -/
theorem evaluateTriangular_mul (p q : PowerSeries (PowerSeries A))
    (hp : Triangular p) (hq : Triangular q) :
    evaluateTriangular (p * q) = evaluateTriangular p * evaluateTriangular q := by
  simp only [evaluateTriangular, polynomialTranspose_mul p q hp hq, map_mul]

/-- A constant curve evaluates to its value. -/
theorem evaluateTriangular_C (p : PowerSeries A) : evaluateTriangular (C p) = p := by
  ext n
  rw [coeff_evaluateTriangular]
  simp only [coeff_C, apply_ite (coeff n), map_zero]
  simp

theorem triangular_C (p : PowerSeries A) : Triangular (C p) := by
  intro j n hn
  simp [coeff_C, show j ≠ 0 by lia]

@[simp]
theorem evaluateTriangular_one : evaluateTriangular (1 : PowerSeries (PowerSeries A)) = 1 := by
  simpa using evaluateTriangular_C (1 : PowerSeries A)

variable [Algebra ℚ A]

/-- Coefficientwise maps in the coefficient algebra preserve triangular support. -/
theorem Triangular.mapSeriesLinear {p : PowerSeries (PowerSeries A)} (hp : Triangular p)
    (D : A →ₗ[ℚ] A) : Triangular (mapSeriesLinear (mapSeriesLinear D) p) := by
  intro j n hn
  simp only [coeff_mapSeriesLinear, hp j n hn, map_zero]

/-- Finite evaluation commutes with a linear operation on the coefficient algebra. -/
theorem evaluateTriangular_mapSeriesLinear (D : A →ₗ[ℚ] A)
    (p : PowerSeries (PowerSeries A)) :
    evaluateTriangular (mapSeriesLinear (mapSeriesLinear D) p) =
      mapSeriesLinear D (evaluateTriangular p) := by
  ext n
  simp only [coeff_evaluateTriangular, coeff_mapSeriesLinear, map_sum]

/-- Exponentials of positive series are triangular in the auxiliary parameter. -/
theorem triangular_exponentialCurve (p : PowerSeries A) (hp : constantCoeff p = 0) :
    Triangular (exponentialCurve p) := by
  intro j n hnj
  rw [coeff_exponentialCurve, coeff_smul, ← positiveSeries_coeff p hp,
    coeff_positiveSeries_pow_eq_zero_of_lt _ j n hnj, smul_zero]

/-- Evaluating an exponential curve at auxiliary time one is the formal exponential. -/
theorem evaluateTriangular_exponentialCurve (p : PowerSeries A) (hp : constantCoeff p = 0) :
    evaluateTriangular (exponentialCurve p) = formalExp p := by
  ext n
  rw [coeff_evaluateTriangular]
  simp only [coeff_exponentialCurve, coeff_smul, formalExp, scalarSeriesApply, coeff_mk,
    coeff_exp, Algebra.algebraMap_self, RingHom.id_apply, one_div]
  apply sum_congr rfl
  intro j hj
  rw [← coeff_positiveSeries_pow]
  rw [positiveSeries_coeff p hp]

end FQFP
