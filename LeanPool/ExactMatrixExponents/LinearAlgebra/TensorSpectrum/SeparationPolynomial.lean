/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.SeparationWeights
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorBatching

/-!
# The charged separation polynomial

The zero coefficient is the exact separated sum and the degree depends on
the difference of the branch indices. Evaluation uses a multiplicative map
on the integer coordinate weights.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.TensorSpectrum.Separation

variable {R X Y Z : Type*} [CommSemiring R] {M : ℕ}

/-- The auxiliary pairing has one coordinate on the first leg. -/
def dotPairingX (U : Type*) [DecidableEq U] : Tensor R Unit U U :=
  fun _ u v => if u = v then 1 else 0

/-- Every branch in this output has its own first-leg space. -/
def separated {M : ℕ} (A : Fin M → Tensor R X Y Z) :
    Tensor R (Fin M × (X × Unit)) (Fin M × (Y × Fin M))
      (Fin M × (Z × Fin M)) :=
  Tensor.directSum (fun h => Tensor.product (A h) (dotPairingX (Fin M)))

/-- The integer projected by the finite Fourier average. Labels are numbered
from zero here; translating all four labels by one leaves this phase unchanged. -/
def phase {M : ℕ} (h g u v : Fin M) : ℤ :=
  (u : ℤ) - (v : ℤ) + 2 * ((g : ℤ) - (h : ℤ))

/-- Evaluates `if y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0 then A y.1 x.2.1 y.2.1 z.2.1 else 0`
at the input `x y z`. -/
def projected (A : Fin M → Tensor R X Y Z) :
    Tensor R (Fin M × (X × Unit)) (Fin M × (Y × Fin M))
      (Fin M × (Z × Fin M)) :=
  fun x y z => if y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0
    then A y.1 x.2.1 y.2.1 z.2.1 else 0

/-- The degree of a projected monomial, already known to be nonnegative. -/
def squareDegree (h g : Fin M) : ℕ :=
  squareExponent g h

/-- This is a polynomial array even though the individual local weights used
to realize its nonzero evaluations can be negative. -/
def separationPolynomial (A : Fin M → Tensor R X Y Z) :
    Tensor (Polynomial R) (Fin M × (X × Unit)) (Fin M × (Y × Fin M))
      (Fin M × (Z × Fin M)) :=
  fun x y z => if y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0
    then Polynomial.monomial (squareDegree y.1 x.1) (A y.1 x.2.1 y.2.1 z.2.1)
    else 0

theorem squareDegree_eq_zero_iff (h g : Fin M) : squareDegree h g = 0 ↔ g = h := by
  exact squareExponent_eq_zero_iff g h

/-- The zero coefficient is the full direct sum with an auxiliary dot product. -/
theorem separationPolynomial_constant (A : Fin M → Tensor R X Y Z) :
    (fun x y z => (separationPolynomial A x y z).coeff 0) = separated A := by
  funext x y z
  by_cases hxy : x.1 = y.1
  · by_cases hyz : y.1 = z.1
    · by_cases huv : y.2.2 = z.2.2
      · simp [separationPolynomial, separated, Tensor.directSum, Tensor.product,
          dotPairingX, phase, squareDegree, squareExponent, hxy, hyz, huv]
      · have hp : phase y.1 x.1 y.2.2 z.2.2 ≠ 0 := by
          intro hp
          have heq : (y.2.2 : ℤ) = (z.2.2 : ℤ) := by
            simpa [phase, hxy, sub_eq_zero] using hp
          exact huv (Fin.ext (by exact_mod_cast heq))
        have hsupport : ¬(y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0) :=
          fun h => hp h.2
        simp only [separationPolynomial, ite_eq_right hsupport]
        simp [separated, Tensor.directSum, Tensor.product, dotPairingX, hxy, hyz, huv]
    · have hxz : x.1 ≠ z.1 := by simpa [hxy] using hyz
      simp [separationPolynomial, separated, Tensor.directSum, hyz, hxz]
  · have hdegree : squareDegree y.1 x.1 ≠ 0 := by
      exact fun h => hxy ((squareDegree_eq_zero_iff y.1 x.1).mp h)
    by_cases hs : y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0
    · simp only [separationPolynomial, ite_eq_left hs]
      simp [separated, Tensor.directSum, hxy,
        Polynomial.coeff_monomial, hdegree]
    · simp [separationPolynomial, hs, separated, Tensor.directSum, hxy]

theorem separationPolynomial_degree (A : Fin M → Tensor R X Y Z)
    (x : Fin M × (X × Unit)) (y : Fin M × (Y × Fin M))
    (z : Fin M × (Z × Fin M)) :
    (separationPolynomial A x y z).degree ≤ ((M - 1) ^ 2 : ℕ) := by
  apply Polynomial.degree_le_of_natDegree_le
  unfold separationPolynomial
  split_ifs
  · exact le_trans (Polynomial.natDegree_monomial_le _)
      (squareExponent_le x.1 y.1)
  · simp

/-- The quantity computed by `(x.1 : ℤ) ^ 2`. -/
def weightX (x : Fin M × (X × Unit)) : ℤ := (x.1 : ℤ) ^ 2

/-- The quantity computed by `(y.1 : ℤ) * (y.2.2 : ℤ) - (y.1 : ℤ) ^ 2`. -/
def weightY (y : Fin M × (Y × Fin M)) : ℤ :=
  (y.1 : ℤ) * (y.2.2 : ℤ) - (y.1 : ℤ) ^ 2

/-- The quantity computed by `-(z.1 : ℤ) * (z.2.2 : ℤ)`. -/
def weightZ (z : Fin M × (Z × Fin M)) : ℤ :=
  -(z.1 : ℤ) * (z.2.2 : ℤ)

/-- On the complete projected support, the local weights add to the actual
polynomial degree, including all zero and mismatched coefficients. -/
theorem separationPolynomial_eval (A : Fin M → Tensor R X Y Z)
    (t : R) (integerPower : ℤ → R)
    (hadd : ∀ a b, integerPower (a + b) = integerPower a * integerPower b)
    (hnat : ∀ n : ℕ, integerPower n = t ^ n) :
    (fun x y z => (separationPolynomial A x y z).eval t) =
      fun x y z => integerPower (weightX x) * integerPower (weightY y) *
        integerPower (weightZ z) * projected A x y z := by
  funext x y z
  by_cases hs : y.1 = z.1 ∧ phase y.1 x.1 y.2.2 z.2.2 = 0
  · have hsum : weightX x + weightY y + weightZ z =
        ((x.1 : ℤ) - (y.1 : ℤ)) ^ 2 := by
      dsimp [weightX, weightY, weightZ]
      rw [← hs.1]
      have hp := hs.2
      dsimp [phase] at hp
      nlinarith
    have hcast : (squareDegree y.1 x.1 : ℤ) = ((x.1 : ℤ) - (y.1 : ℤ)) ^ 2 :=
      Int.toNat_of_nonneg (sq_nonneg _)
    simp only [separationPolynomial, projected, ite_eq_left hs, Polynomial.eval_monomial]
    rw [← hadd, ← hadd, hsum, ← hcast, hnat, mul_comm]
  · simp [separationPolynomial, projected, hs]

end MatrixMultiplicationAllFields.TensorSpectrum.Separation
