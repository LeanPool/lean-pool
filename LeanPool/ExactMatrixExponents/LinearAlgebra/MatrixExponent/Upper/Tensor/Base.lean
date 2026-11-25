/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
public import Mathlib.Basic.NNReal.Defs
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClass

/-! # Tensor representatives and classes for the upper bound -/

@[expose] public section

noncomputable section

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper

namespace CoefficientTensor

export MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor
  (Restricts)

namespace Restricts

export MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor.Restricts
  (refl trans pullback rankAtMost)

end Restricts

end CoefficientTensor

/-- Finite tensor representatives over the coefficient ring. -/
abbrev TensorRep := MatrixMultiplicationAllFields.TensorSpectrum.TensorRep Coeff

namespace TensorRep

/-- The first coordinate dimension. -/
abbrev xDim (T : TensorRep) :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorRep.xDim T

/-- The second coordinate dimension. -/
abbrev yDim (T : TensorRep) :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorRep.yDim T

/-- The third coordinate dimension. -/
abbrev zDim (T : TensorRep) :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorRep.zDim T

/-- The coefficient array of a tensor representative. -/
abbrev coeff (T : TensorRep) :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorRep.coeff T

export MatrixMultiplicationAllFields.TensorSpectrum.TensorRep
  (mk ofTensor Restricts Equivalent mutualRestriction restricts_ofTensor
    ofTensor_restricts equivalent_ofTensor_coeff)

namespace Restricts

export MatrixMultiplicationAllFields.TensorSpectrum.TensorRep.Restricts
  (refl trans ofTensor)

end Restricts

end TensorRep

/-- Mutual-restriction classes over the coefficient ring. -/
abbrev TensorClass := MatrixMultiplicationAllFields.TensorSpectrum.TensorClass Coeff

namespace TensorClass

export MatrixMultiplicationAllFields.TensorSpectrum.TensorClass
  (ofRep ofTensor ofRep_eq ofTensor_coeff ofTensor_eq ofTensor_pullback_equiv ofTensor_le)

end TensorClass

end MatrixMultiplicationAllFields.MatrixExponent.Upper
