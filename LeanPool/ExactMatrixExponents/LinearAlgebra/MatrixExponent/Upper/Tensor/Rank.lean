/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.SpectralBooks.Tensor
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorBatching
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Tensor.Blocks
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassRank

/-!
# Actual finite tensor rank

The natural tensor is the diagonal coefficient tensor. Its local restrictions
are exactly the tensors admitting the corresponding number of rank-one terms.
Every finite coefficient tensor has such a decomposition, obtained by expanding
its individual coefficients. Exact rank is therefore a genuine minimum.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper
namespace CoefficientTensor

/-- The diagonal coefficient tensor for independent scalar products. -/
abbrev natTensor := MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor.natTensor
  (K := Coeff)

export MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor
  (restrict_natTensor rankAtMost_natTensor rankAtMost_iff_natTensor_restricts
    natTensor_add_pullback natTensor_add_restricts rankAtMost_blockSum natTensor_restricts_of_le
    rankAtMost_mono rank rank_spec rank_le_iff rank_mono rank_product_le rank_blockSum_le
    rank_eq_zero_iff)

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- A nonzero coefficient can be selected and rescaled to obtain the scalar
unit tensor. No nonzero-rank assumption replaces this actual restriction. -/
theorem nonzero_restricts_natTensor_one {T : Tensor Coeff X Y Z} (hT : T ≠ 0) :
    Restricts T (natTensor 1) := by
  classical
  have hex : ∃ x y z, T x y z ≠ 0 := by
    by_contra h
    apply hT
    funext x y z
    exact Classical.byContradiction (fun hn => h ⟨x, y, z, hn⟩)
  obtain ⟨x, y, z, hxyz⟩ := hex
  refine ⟨fun _ i => if i = x then (T x y z)⁻¹ else 0,
    fun _ j => if j = y then 1 else 0,
    fun _ k => if k = z then 1 else 0, ?_⟩
  funext i j k
  have hij : i = j := Subsingleton.elim _ _
  have hik : i = k := Subsingleton.elim _ _
  subst j
  subst k
  simp [Tensor.restrict, natTensor, TensorSpectrum.CoefficientTensor.natTensor, Tensor.diagonal,
    ite_mul, mul_ite, hxyz]

end CoefficientTensor

namespace TensorRep

/-- The rank of the tensor in its chosen coordinates. -/
abbrev rank (T : TensorRep) := MatrixMultiplicationAllFields.TensorSpectrum.TensorRep.rank T

namespace Restricts

export MatrixMultiplicationAllFields.TensorSpectrum.TensorRep.Restricts
  (rank_le)

end Restricts

namespace Equivalent

export MatrixMultiplicationAllFields.TensorSpectrum.TensorRep.Equivalent
  (rank_eq)

end Equivalent

end TensorRep

namespace TensorClass

export MatrixMultiplicationAllFields.TensorSpectrum.TensorClass
  (rank rank_ofRep rank_mono rank_ofTensor)

/-- The natural tensor on a sum is equivalent to the two diagonal blocks. -/
theorem ofTensor_natTensor_add (r s : ℕ) :
    ofTensor (CoefficientTensor.natTensor (r + s)) =
      ofTensor (CoefficientTensor.blockSum
        (CoefficientTensor.natTensor r) (CoefficientTensor.natTensor s)) :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.ofTensor_natTensor_add (K := Coeff) r s

/-- The one-dimensional diagonal tensor is equivalent to the unit tensor. -/
theorem ofTensor_natTensor_one :
    ofTensor (CoefficientTensor.natTensor 1) =
      ofTensor (fun (_ _ _ : PUnit) => (1 : Coeff)) :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.ofTensor_natTensor_one

/-- The zero-dimensional diagonal tensor is equivalent to the empty tensor. -/
theorem ofTensor_natTensor_zero :
    ofTensor (CoefficientTensor.natTensor 0) =
      ofTensor (0 : Tensor Coeff Empty Empty Empty) :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.ofTensor_natTensor_zero

end TensorClass

end MatrixMultiplicationAllFields.MatrixExponent.Upper
