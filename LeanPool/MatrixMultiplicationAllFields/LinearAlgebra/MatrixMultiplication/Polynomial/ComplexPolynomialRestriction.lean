/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section ConstantRestriction

variable {F X Y Z X' Y' Z' : Type*} [CommSemiring F]
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Restrict a polynomial tensor using coordinate maps with constant polynomial
coefficients. -/
def restrictPolynomial (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) (P : Tensor (Polynomial F) X Y Z) :
    Tensor (Polynomial F) X' Y' Z' :=
  restrict (fun x' x => Polynomial.C (A x' x))
    (fun y' y => Polynomial.C (B y' y))
    (fun z' z => Polynomial.C (C z' z)) P

@[simp] theorem restrictPolynomial_coeff (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) (P : Tensor (Polynomial F) X Y Z) (k : ℕ)
    (x' : X') (y' : Y') (z' : Z') :
    (restrictPolynomial A B C P x' y' z').coeff k =
      restrict A B C (fun x y z => (P x y z).coeff k) x' y' z' := by
  simp only [restrictPolynomial, restrict, Polynomial.finsetSum_coeff,
    mul_assoc, Polynomial.coeff_C_mul]

theorem RankAtMost.restrictPolynomial {P : Tensor (Polynomial F) X Y Z} {r : ℕ}
    (hP : RankAtMost P r) (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) : RankAtMost (restrictPolynomial A B C P) r :=
  hP.restrict (fun x' x => Polynomial.C (A x' x))
    (fun y' y => Polynomial.C (B y' y))
    (fun z' z => Polynomial.C (C z' z))

theorem restrictPolynomial_degree_le (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) (P : Tensor (Polynomial F) X Y Z) (D : ℕ)
    (hdegree : ∀ x y z, (P x y z).degree ≤ D)
    (x' : X') (y' : Y') (z' : Z') :
    (restrictPolynomial A B C P x' y' z').degree ≤ D := by
  apply (Polynomial.degree_le_iff_coeff_zero _ _).2
  intro k hk
  rw [restrictPolynomial_coeff]
  have hzero (x : X) (y : Y) (z : Z) : (P x y z).coeff k = 0 :=
    (Polynomial.degree_le_iff_coeff_zero _ _).1 (hdegree x y z) k hk
  simp only [restrict, hzero, mul_zero, Finset.sum_const_zero]

end ConstantRestriction

namespace PolynomialApproximation

variable {F X Y Z X' Y' Z' : Type*} [Field F]

/-- Regard an exact rank decomposition as a degree-zero polynomial approximation. -/
def ofRankAtMost (T : Tensor F X Y Z) (r : ℕ) (hT : RankAtMost T r) :
    PolynomialApproximation T r 0 0 where
  polynomial := fun x y z => Polynomial.C (T x y z)
  rank_bound := hT.map Polynomial.C
  vanishes := by
    intro x y z k hk
    exact (Nat.not_lt_zero k hk).elim
  leading := by
    intro x y z
    exact Polynomial.coeff_C_zero
  degree_bound := by
    intro x y z
    simpa only [Nat.cast_zero] using (Polynomial.degree_C_le (a := T x y z))

@[simp] theorem ofRankAtMost_polynomial (T : Tensor F X Y Z) (r : ℕ)
    (hT : RankAtMost T r) :
    (ofRankAtMost T r hT).polynomial = (fun x y z => Polynomial.C (T x y z)) := rfl

variable [Fintype X] [Fintype Y] [Fintype Z]
variable {T : Tensor F X Y Z} {r d D : ℕ}

/-- Apply fixed linear coordinate maps to a polynomial approximation. -/
def restrict (W : PolynomialApproximation T r d D)
    (A : X' → X → F) (B : Y' → Y → F) (C : Z' → Z → F) :
    PolynomialApproximation (Tensor.restrict A B C T) r d D where
  polynomial := restrictPolynomial A B C W.polynomial
  rank_bound := W.rank_bound.restrictPolynomial A B C
  vanishes := by
    intro x' y' z' k hk
    rw [restrictPolynomial_coeff]
    have hzero (x : X) (y : Y) (z : Z) : (W.polynomial x y z).coeff k = 0 :=
      W.vanishes x y z k hk
    simp only [Tensor.restrict, hzero, mul_zero, Finset.sum_const_zero]
  leading := by
    intro x' y' z'
    rw [restrictPolynomial_coeff]
    simp only [W.leading]
  degree_bound := restrictPolynomial_degree_le A B C W.polynomial D W.degree_bound

@[simp] theorem restrict_polynomial (W : PolynomialApproximation T r d D)
    (A : X' → X → F) (B : Y' → Y → F) (C : Z' → Z → F) :
    (W.restrict A B C).polynomial = restrictPolynomial A B C W.polynomial := rfl

end PolynomialApproximation

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixMultiplicationAllFields
