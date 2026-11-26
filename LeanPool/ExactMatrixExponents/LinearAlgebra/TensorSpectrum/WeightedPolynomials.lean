/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialTensors
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.LocalTensor

/-!
# Explicit polynomial families for diagonal weight degenerations

The diagonal degeneration has a polynomial coefficient family, not merely a
topological limit. Its constant coefficient is the retained tensor. Its degree
is controlled by the supported total weights. At every nonzero parameter its
evaluation is an exact restriction of the source tensor. These are the inputs
needed to extract tensor powers by finite interpolation.
-/

@[expose] public section

noncomputable section

open scoped BigOperators NNReal
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation
open MatrixMultiplicationAllFields.MatrixExponent
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation.Tensor

namespace MatrixMultiplicationAllFields.TensorSpectrum.PolynomialTensors

variable {K : Type*} [CommSemiring K]

variable {X Y Z : Type*}

/-- The monomial family associated to three integer coordinate weights. -/
def weightedPolynomial (T : Tensor K X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ) :
    Tensor (Polynomial K) X Y Z :=
  fun x y z => Polynomial.monomial (wx x + wy y + wz z).toNat (T x y z)

/-- Polynomial evaluation agrees with the continuous coefficient family used
in the degeneration proof, including at the parameter zero. -/
theorem weightedPolynomial_eval (T : Tensor K X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ) (t : K) :
    (fun x y z => (weightedPolynomial T wx wy wz x y z).eval t) =
      weightedFamily T wx wy wz t := by
  funext x y z
  simp [weightedPolynomial, weightedFamily, Polynomial.eval_monomial, mul_comm]

/-- The constant coefficient keeps precisely the supported weight-zero terms. -/
theorem weightedPolynomial_coeff_zero (T : Tensor K X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 → 0 ≤ wx x + wy y + wz z)
    (x : X) (y : Y) (z : Z) :
    (weightedPolynomial T wx wy wz x y z).coeff 0 =
      weightedLimit T wx wy wz x y z := by
  have heq := (weightedPolynomial_eval T wx wy wz 0).trans
    (weightedFamily_zero T wx wy wz h)
  simpa only [Polynomial.coeff_zero_eq_eval_zero] using
    congrFun (congrFun (congrFun heq x) y) z

/-- A degree bound is needed only on supported coefficients. Unsupported
coordinates are the zero polynomial, regardless of their assigned weights. -/
theorem weightedPolynomial_natDegree_le (T : Tensor K X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ) {D : ℕ}
    (hD : ∀ x y z, T x y z ≠ 0 → (wx x + wy y + wz z).toNat ≤ D)
    (x : X) (y : Y) (z : Z) :
    (weightedPolynomial T wx wy wz x y z).natDegree ≤ D := by
  by_cases hT : T x y z = 0
  · simp [weightedPolynomial, hT]
  · exact (Polynomial.natDegree_monomial_le (T x y z)).trans (hD x y z hT)

/-- The same degree bound in the form used by polynomial interpolation. -/
theorem weightedPolynomial_degree_le (T : Tensor K X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ) {D : ℕ}
    (hD : ∀ x y z, T x y z ≠ 0 → (wx x + wy y + wz z).toNat ≤ D)
    (x : X) (y : Y) (z : Z) :
    (weightedPolynomial T wx wy wz x y z).degree ≤ D :=
  Polynomial.degree_le_of_natDegree_le
    (weightedPolynomial_natDegree_le T wx wy wz hD x y z)

/-- A weight-zero/weight-one support split gives degree at most one. This is
the bound used by the determinant filtration and the three-sector split. -/
theorem weightedPolynomial_degree_le_one (T : Tensor K X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 →
      wx x + wy y + wz z = 0 ∨ wx x + wy y + wz z = 1)
    (x : X) (y : Y) (z : Z) :
    (weightedPolynomial T wx wy wz x y z).degree ≤ (1 : ℕ) := by
  apply weightedPolynomial_degree_le T wx wy wz
  intro u v w hT
  rcases h u v w hT with hw | hw <;> simp [hw]

theorem weightedFamily_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 → 0 ≤ wx x + wy y + wz z)
    (t : K) (power : ℤ → K)
    (hadd : ∀ a b, power (a + b) = power a * power b)
    (hnat : ∀ n : ℕ, power n = t ^ n) :
    weightedFamily T wx wy wz t ∈ LocalTensor.orbit T := by
  classical
  refine ⟨(fun x' x => if x = x' then power (wx x) else 0),
    (fun y' y => if y = y' then power (wy y) else 0),
    (fun z' z => if z = z' then power (wz z) else 0), ?_⟩
  rw [restrict_diagonal]
  funext x y z
  by_cases hT : T x y z = 0
  · simp [weightedFamily, hT]
  · have hnonneg := h x y z hT
    dsimp [weightedFamily]
    rw [← hnat, Int.toNat_of_nonneg hnonneg, hadd, hadd]

end MatrixMultiplicationAllFields.TensorSpectrum.PolynomialTensors
