/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
public import Lean.Elab.Tactic.Omega

/-! # Convolution tensors and diagonal coefficient weights -/

@[expose] public section

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.TensorSpectrum.PolynomialTensors

variable {K : Type*} [CommSemiring K]

/-- Multiplication of polynomials with `a` and `b` coefficients, with every
output coefficient retained. -/
def polynomialTensor (a b : ℕ) :
    Tensor K (Fin a) (Fin b) (Fin (a + b - 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

@[simp] theorem polynomialTensor_apply (a b : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    (polynomialTensor (K := K)) a b i j k = if i.val + j.val = k.val then 1 else 0 := rfl

/-- The tensor coefficient is the coefficient of the product of the two input
monomials. -/
theorem polynomialTensor_eq_coeff (a b : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    polynomialTensor a b i j k =
      ((Polynomial.X : Polynomial K) ^ (i.val + j.val)).coeff k.val := by
  simp [polynomialTensor, Polynomial.coeff_X_pow, eq_comm]

/-- Commuting the input factors only reindexes the equal-sized output space. -/
theorem polynomialTensor_swap (a b : ℕ)
    (i : Fin a) (j : Fin b) (k : Fin (a + b - 1)) :
    (polynomialTensor (K := K)) a b i j k =
      polynomialTensor b a j i (Fin.cast (by omega) k) := by
  simp [polynomialTensor, Nat.add_comm]

/-- With a scalar as the first input, multiplication is the identity pairing
between the second input and output coefficient coordinates. -/
theorem polynomialTensor_one_left (b : ℕ)
    (i : Fin 1) (j : Fin b) (k : Fin (1 + b - 1)) :
    (polynomialTensor (K := K)) 1 b i j k = if j.val = k.val then 1 else 0 := by
  simp [polynomialTensor]

variable {X Y Z : Type*}

/-- The part of a tensor with total diagonal weight zero. -/
def weightedLimit (T : Tensor K X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ) : Tensor K X Y Z :=
  fun x y z => if wx x + wy y + wz z = 0 then T x y z else 0

/-- The polynomial coefficient family. Negative total weights
occur only at zero coefficients in the degeneration theorem. -/
def weightedFamily (T : Tensor K X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (t : K) : Tensor K X Y Z :=
  fun x y z => t ^ (wx x + wy y + wz z).toNat * T x y z

theorem weightedFamily_zero (T : Tensor K X Y Z)
    (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 → 0 ≤ wx x + wy y + wz z) :
    weightedFamily T wx wy wz 0 = weightedLimit T wx wy wz := by
  funext x y z
  by_cases hT : T x y z = 0
  · simp [weightedFamily, weightedLimit, hT]
  · have hnonneg := h x y z hT
    by_cases hw : wx x + wy y + wz z = 0
    · simp [weightedFamily, weightedLimit, hw]
    · have hnatne : (wx x + wy y + wz z).toNat ≠ 0 := by
        intro he
        have hc := Int.toNat_of_nonneg hnonneg
        rw [he] at hc
        exact hw hc.symm
      simp [weightedFamily, weightedLimit, hw, zero_pow hnatne]

/-- Diagonal local coefficient matrices multiply the three corresponding
coefficient factors, with all off-diagonal contributions vanishing. -/
theorem restrict_diagonal [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Tensor K X Y Z) (a : X → K) (b : Y → K) (c : Z → K) :
    Tensor.restrict (fun x' x => if x = x' then a x else 0)
      (fun y' y => if y = y' then b y else 0)
      (fun z' z => if z = z' then c z else 0) T =
      fun x y z => a x * b y * c z * T x y z := by
  classical
  funext x y z
  simp [Tensor.restrict, ite_mul, mul_ite]

end MatrixMultiplicationAllFields.TensorSpectrum.PolynomialTensors
