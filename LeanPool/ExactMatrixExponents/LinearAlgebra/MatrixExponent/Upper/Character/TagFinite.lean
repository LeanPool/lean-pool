/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Character.ChargedSeparation
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Character.DotsPower
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.TagTensorWords
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TagFiberBounds

/-!
# The exact finite-word character inequality

Every count fiber is selected by actual local coordinate maps from a tensor
power of the original shared-input tensor.  Charged separation is then applied
to that finite fiber.  This is the tensor input to the later scalar limit;
neither the separation nor the word restriction is an assumption here.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators NNReal
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass

theorem Character.shared_branch_le (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {s : ℕ} (A : Fin s → Tensor Coeff X Y Z) (i : Fin s) :
    f (ofTensor (A i)) ≤ f (ofTensor (Separation.shared A)) := by
  exact TensorSpectrum.TensorClass.Character.shared_branch_le f A i

theorem Character.one_le_of_tensor_ne_zero (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor Coeff X Y Z) (hT : T ≠ 0) : 1 ≤ f (ofTensor T) := by
  have h := f.monotone' (ofTensor_le
    (CoefficientTensor.nonzero_restricts_natTensor_one hT))
  have hunit : ofTensor (CoefficientTensor.natTensor 1) = (1 : TensorClass) := by
    simpa only [Nat.cast_one] using (natCast_eq_ofTensor_natTensor 1).symm
  calc
    1 = f.toHom (ofTensor (CoefficientTensor.natTensor 1)) := by
      rw [hunit]
      exact f.toHom.map_one.symm
    _ ≤ f.toHom (ofTensor T) := h

/-- The original word-fiber cost, including the fixed factor five.  The
polynomial number of possible count vectors has not yet been removed. -/
theorem Character.tag_count_fiber (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {s N : ℕ} (A : Fin s → Tensor Coeff X Y Z)
    (c : TagWords.CountVector s N) (hc : 0 < (TagWords.fiber c).card) :
    ((TagWords.fiber c).card : ℝ) ^ f.pX *
        TagWords.countWeight (fun i => (f (ofTensor (A i)) : ℝ)) c ≤
      5 * (f (ofTensor (Separation.shared A)) : ℝ) ^ N := by
  apply TensorSpectrum.TensorClass.Character.tag_count_fiber f A c hc 5
  intro M hM B C hvalue
  exact f.charged_separation_equal hM B C hvalue

end MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass
