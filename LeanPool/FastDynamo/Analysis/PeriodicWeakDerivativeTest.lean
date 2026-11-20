/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.PeriodicWeakDerivative

/-!
# Fourier-monomial test formulation of periodic weak derivatives

This file provides the Fourier-monomial test side of the coefficient definition of
`HasTransverseFourierDerivative`: the derivative multiplier `2πi nⱼ` and its
conjugate (Mathlib's complex inner product is conjugate-linear in its first
argument), the pairing of a Fourier monomial with one vector component, which is
exactly the corresponding Fourier coefficient, and finite trigonometric
polynomials with their coefficientwise derivative.

The test family is complete in scalar `L²`, and the componentwise coefficient
functionals separate vector-valued `L²` fields by
`transverseC3L2_ext_coeff`.  No claim about a separately bundled space of all
smooth periodic test functions is made here.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-- Fourier multiplier of the `j`-th derivative at transverse frequency `n`. -/
def transverseFourierDerivMultiplier (j : Fin 2)
    (n : TransverseFrequency) : ℂ :=
  2 * Real.pi * Complex.I * (n j : ℂ)

/-- The derivative multiplier `2πi nⱼ` is purely imaginary, so complex conjugation negates it.
This is the source of the minus sign in integration by parts. -/
@[simp] theorem star_transverseFourierDerivMultiplier
    (j : Fin 2) (n : TransverseFrequency) :
    starRingEnd ℂ (transverseFourierDerivMultiplier j n) =
      -transverseFourierDerivMultiplier j n := by
  unfold transverseFourierDerivMultiplier
  rw [map_mul, map_mul, map_mul, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I, map_intCast]
  ring

/-- Pair one scalar Fourier monomial with one component of a vector-valued
`L²` field.  This is the integral of the conjugate monomial times that
component. -/
def transverseMonomialComponentPairing (n : TransverseFrequency)
    (i : Fin 3) (f : TransverseC3L2) : ℂ :=
  inner ℂ (transverseMonomialL2 n) (transverseCoordL2 i f)

/-- Testing the `i`-th component of a transverse `L²` vector field against the Fourier monomial
of frequency `n` returns exactly its `(n, i)` Fourier coefficient. -/
theorem transverseMonomialComponentPairing_eq_coeff
    (n : TransverseFrequency) (i : Fin 3) (f : TransverseC3L2) :
    transverseMonomialComponentPairing n i f =
      transverseCoeffCLM n i f := by
  rw [transverseMonomialComponentPairing, transverseCoeffCLM,
    ContinuousLinearMap.comp_apply, transverseScalarCoeffCLM_eq_inner]

/-- The monomial/component pairing is the expected integral of the conjugate
test monomial against the selected field component. -/
theorem transverseMonomialComponentPairing_eq_integral
    (n : TransverseFrequency) (i : Fin 3) (f : TransverseC3L2) :
    transverseMonomialComponentPairing n i f =
      ∫ x : TransverseTorus,
        starRingEnd ℂ ((transverseMonomialL2 n) x) *
          (transverseCoordL2 i f) x ∂transverseMeasure := by
  rw [transverseMonomialComponentPairing, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  simp only [RCLike.inner_apply]
  rw [mul_comm]

/-! ## Finite trigonometric-polynomial tests -/

/-- A scalar transverse trigonometric polynomial, bundled by its finitely
supported Fourier coefficients. -/
abbrev TransverseTrigPolynomial := TransverseFrequency →₀ ℂ

/-- Synthesize a finitely supported coefficient family into scalar `L²`. -/
def transverseTrigPolynomialToL2 :
    TransverseTrigPolynomial →ₗ[ℂ] TransverseScalarL2 :=
  Finsupp.linearCombination ℂ transverseMonomialL2

/-- Differentiate a trigonometric polynomial coefficientwise. -/
def transverseTrigPolynomialDeriv (j : Fin 2) :
    TransverseTrigPolynomial →ₗ[ℂ] TransverseTrigPolynomial :=
  Finsupp.linearCombination ℂ fun n ↦
    transverseFourierDerivMultiplier j n • Finsupp.single n 1

/-- Synthesis of a one-term coefficient family: the trigonometric polynomial with single
coefficient `c` at frequency `n` is `c` times the monomial `e_n`. -/
@[simp] theorem transverseTrigPolynomialToL2_single
    (n : TransverseFrequency) (c : ℂ) :
    transverseTrigPolynomialToL2 (Finsupp.single n c) =
      c • transverseMonomialL2 n := by
  exact Finsupp.linearCombination_single ℂ c n

/-- Coefficientwise differentiation of a one-term trigonometric polynomial multiplies its single
coefficient by the derivative multiplier `2πi nⱼ`. -/
@[simp] theorem transverseTrigPolynomialDeriv_single
    (j : Fin 2) (n : TransverseFrequency) (c : ℂ) :
    transverseTrigPolynomialDeriv j (Finsupp.single n c) =
      c • (transverseFourierDerivMultiplier j n •
        Finsupp.single n 1) := by
  exact Finsupp.linearCombination_single ℂ c n

end

end FastDynamo
