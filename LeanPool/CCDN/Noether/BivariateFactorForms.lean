/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.BivariateClosedForms

/-! Explicit closed forms from polynomial factors, including repeated factors.
These supply reducibility obstructions for the differential matrix. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- The inner and outer derivatives of a bivariate polynomial commute. -/
lemma derivative_bivariateCoefficientDerivative {F : Type*} [Field F] (p : F[X][X]) :
    ((bivariateCoefficientDerivative F) p).derivative =
      (bivariateCoefficientDerivative F) p.derivative := by
  ext n
  simp [coeff_derivative, derivative_mul, mul_comm]

/-- The logarithmic differential of a factor gives a closed form for the
whole product after clearing its denominator. -/
theorem bivariate_factor_closed_form {F : Type*} [Field F] (g h : F[X][X]) :
    (bivariateCoefficientDerivative F) (h * g.derivative) * (g * h) -
      (h * g.derivative) * (bivariateCoefficientDerivative F) (g * h) =
    (h * (bivariateCoefficientDerivative F) g).derivative * (g * h) -
      (h * (bivariateCoefficientDerivative F) g) * (g * h).derivative := by
  simp only [Derivation.leibniz, smul_eq_mul, derivative_mul,
    derivative_bivariateCoefficientDerivative]
  ring

/-- A repeated factor gives the closed form dg/g², after clearing f=g²h. -/
private theorem bivariate_square_factor_closed_form {F : Type*} [Field F] (g h : F[X][X]) :
    (bivariateCoefficientDerivative F) (h * g.derivative) * (g ^ 2 * h) -
      (h * g.derivative) * (bivariateCoefficientDerivative F) (g ^ 2 * h) =
    (h * (bivariateCoefficientDerivative F) g).derivative * (g ^ 2 * h) -
      (h * (bivariateCoefficientDerivative F) g) * (g ^ 2 * h).derivative := by
  simp only [pow_two, Derivation.leibniz, smul_eq_mul, derivative_mul,
    derivative_bivariateCoefficientDerivative]
  ring

/-- For coprime factors with a separable first factor and nonzero second
 derivative, the factor's logarithmic numerator cannot be a scalar multiple
 of the derivative of the product. This works in any characteristic. -/
theorem factor_numerator_not_scalar_gradient
    {R : Type*} [CommRing R] [IsDomain R] (g h : R[X])
    (hg : 0 < g.degree) (hgh : IsCoprime g h) (hgg : IsCoprime g g.derivative)
    (hh : h.derivative ≠ 0) (a : R) :
    h * g.derivative ≠ C a * (g * h).derivative := by
  intro he
  have hdiv : g ∣ C (1 - a) * (h * g.derivative) := by
    refine ⟨C a * h.derivative, ?_⟩
    simp only [derivative_mul, map_sub, map_one] at he ⊢
    linear_combination he
  have hcdiv : g ∣ C (1 - a) := (hgh.mul_right hgg).dvd_of_dvd_mul_right hdiv
  have hc : C (1 - a) = (0 : R[X]) := by
    by_contra hn
    exact (not_le_of_gt (degree_C_le.trans_lt hg)) (degree_le_of_dvd hcdiv hn)
  have ha : a = 1 := by
    have h := Polynomial.C_injective (show C (1 - a) = C (0 : R) by simpa using hc)
    exact (sub_eq_zero.mp h).symm
  rw [ha, C_1, one_mul, derivative_mul] at he
  have hz : g * h.derivative = 0 := by linear_combination -he
  have hg0 : g ≠ 0 := by intro h; simp [h] at hg
  exact (mul_ne_zero hg0 hh) hz

/-- The repeated-factor construction works for every multiplicity at least
two, with no restriction on the characteristic or the multiplicity. -/
theorem bivariate_power_factor_closed_form {F : Type*} [Field F]
    (g h : F[X][X]) (k : ℕ) :
    (bivariateCoefficientDerivative F) (g ^ k * h * g.derivative) * (g ^ (k + 2) * h) -
      (g ^ k * h * g.derivative) * (bivariateCoefficientDerivative F) (g ^ (k + 2) * h) =
    (g ^ k * h * (bivariateCoefficientDerivative F) g).derivative * (g ^ (k + 2) * h) -
      (g ^ k * h * (bivariateCoefficientDerivative F) g) * (g ^ (k + 2) * h).derivative := by
  have he : g ^ (k + 2) * h = g ^ 2 * (g ^ k * h) := by rw [pow_add]; ring
  rw [he]
  exact bivariate_square_factor_closed_form g (g ^ k * h)

/-- For a nonconstant separable `g` coprime to `h`, the numerator `g ^ k * h * g'` is not a
scalar multiple of the derivative of `g ^ (k + 2) * h`; cancellation exposes its extra pole. -/
theorem power_factor_numerator_not_scalar_gradient
    {R : Type*} [CommRing R] [IsDomain R] (g h : R[X]) (k : ℕ)
    (hg : 0 < g.degree) (hgh : IsCoprime g h) (hgg : IsCoprime g g.derivative)
    (a : R) : g ^ k * h * g.derivative ≠ C a * (g ^ (k + 2) * h).derivative := by
  intro he
  have hg0 : g ≠ 0 := by intro h; simp [h] at hg
  have hd : (g ^ (k + 2) * h).derivative =
      g ^ k * (g * (C ((k + 2 : ℕ) : R) * g.derivative * h + g * h.derivative)) := by
    rw [derivative_mul, derivative_pow]
    simp only [show k + 2 - 1 = k + 1 by omega, pow_add, pow_one, pow_two]
    ring
  rw [hd] at he
  have he' : h * g.derivative = C a * (g *
      (C ((k + 2 : ℕ) : R) * g.derivative * h + g * h.derivative)) := by
    apply mul_left_cancel₀ (pow_ne_zero k hg0)
    linear_combination he
  have hdiv : g ∣ h * g.derivative := by
    rw [he']
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  have hunit := (hgh.mul_right hgg).isUnit_of_dvd hdiv
  have hz : g.degree = 0 := degree_eq_zero_of_isUnit hunit
  rw [hz] at hg
  exact lt_irrefl _ hg

end
end CCDN
