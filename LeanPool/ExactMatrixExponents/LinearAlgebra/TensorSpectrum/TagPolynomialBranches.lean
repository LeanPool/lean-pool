/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TagHeterogeneous
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialFiltration
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassPermutations

/-!
# Polynomial branches in the heterogeneous tag construction

The determinant branches retain their actual output coordinates; finite
coordinate equivalences identify their classes with polynomial multiplication.
The middle tripling branch is a last-two-leg swap followed by the stated
invertible reversal of the shared first coordinate.
-/

@[expose] public section

noncomputable section

open scoped BigOperators NNReal
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation.Tensor

namespace MatrixMultiplicationAllFields.TensorSpectrum.TagHeterogeneous

variable {K : Type*} [CommRing K]

open PolynomialTensors (polynomialTensor determinantGradedTensor
  triplingReverse triplingReverse_involutive)

/-- The larger retained branch of the determinant filtration. -/
def determinantQuotientTensor (a b : ℕ) :
    Tensor K (Fin (a + 1)) (Fin (b + 3)) (Fin (a + b + 3)) :=
  Tensor.pullback (Equiv.refl _) (Equiv.refl _) (finCongr (by omega))
    (polynomialTensor (a + 1) (b + 3))

/-- The smaller retained branch of the determinant filtration. -/
def determinantKernelTensor (a b : ℕ) :
    Tensor K (Fin (a + 1)) (Fin (b + 1)) (Fin (a + b + 1)) :=
  Tensor.pullback (Equiv.refl _) (Equiv.refl _) (finCongr (by omega))
    (polynomialTensor (a + 1) (b + 1))

theorem determinantGradedTensor_eq_sharedTwo (a b : ℕ) :
    determinantGradedTensor (K := K) a b =
      sharedTwo (determinantQuotientTensor a b) (determinantKernelTensor a b) := by
  funext i j k
  cases j <;> cases k <;> rfl

theorem ofTensor_determinantQuotient (a b : ℕ) :
    TensorClass.ofTensor (determinantQuotientTensor (K := K) a b) =
      TensorClass.ofTensor (polynomialTensor (a + 1) (b + 3)) := by
  apply TensorClass.ofTensor_pullback_equiv

theorem ofTensor_determinantKernel (a b : ℕ) :
    TensorClass.ofTensor (determinantKernelTensor (K := K) a b) =
      TensorClass.ofTensor (polynomialTensor (a + 1) (b + 1)) := by
  apply TensorClass.ofTensor_pullback_equiv

/-- The uniform separation input is the whole graded determinant tensor. -/
theorem ofTensor_determinant_uniform (a b : ℕ) :
    TensorClass.ofTensor (Tensor.sharedFirst
      (twoFamily (determinantQuotientTensor (K := K) a b) (determinantKernelTensor a b))) =
      TensorClass.ofTensor (determinantGradedTensor a b) := by
  rw [ofTensor_shared_twoFamily, determinantGradedTensor_eq_sharedTwo]

/-- Both original polynomial branches survive zero padding exactly. -/
theorem ofTensor_determinant_family (a b : ℕ) (j : Fin 2) :
    TensorClass.ofTensor
      (twoFamily (determinantQuotientTensor (K := K) a b) (determinantKernelTensor a b) j) =
      ![TensorClass.ofTensor (polynomialTensor (a + 1) (b + 3)),
        TensorClass.ofTensor (polynomialTensor (a + 1) (b + 1))] j := by
  rw [ofTensor_twoFamily, ofTensor_determinantQuotient, ofTensor_determinantKernel]

/-- This reversal is an actual equivalence, including the empty finite type. -/
def triplingReverseEquiv (a : ℕ) : Fin a ≃ Fin a where
  toFun := triplingReverse
  invFun := triplingReverse
  left_inv := triplingReverse_involutive
  right_inv := triplingReverse_involutive

/-- The middle branch is evaluated using the permuted character. Its
first-coordinate reversal is removed only by an invertible local map. -/
theorem ofTensor_triplingMiddle (a h : ℕ) :
    TensorClass.ofTensor (triplingMiddleTensor (K := K) a h) =
      TensorClass.swapYZ (TensorClass.ofTensor (polynomialTensor a h)) := by
  have heq : triplingMiddleTensor (K := K) a h =
      Tensor.pullback (triplingReverseEquiv a) (Equiv.refl _) (Equiv.refl _)
        (CoefficientTensor.swapYZ (polynomialTensor a h)) := rfl
  rw [heq, TensorClass.ofTensor_pullback_equiv, TensorClass.swapYZ_ofTensor]

theorem ofTensor_tripling_family (a h : ℕ) (j : Fin 3) :
    TensorClass.ofTensor
      (threeFamily (polynomialTensor (K := K) a h) (triplingMiddleTensor a h)
        (polynomialTensor a h) j) =
      ![TensorClass.ofTensor (polynomialTensor a h),
        TensorClass.swapYZ (TensorClass.ofTensor (polynomialTensor a h)),
        TensorClass.ofTensor (polynomialTensor a h)] j := by
  rw [ofTensor_threeFamily, ofTensor_triplingMiddle]

end MatrixMultiplicationAllFields.TensorSpectrum.TagHeterogeneous
