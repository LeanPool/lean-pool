/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Character.Permutations
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Character.DotsPower
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorCharacterPermutationPowers

/-!
# The exponents of the six permuted characters

The exponent identities below follow from evaluating the actual pairings at
dimension two. In particular, they do not depend on how the power-law witnesses
were chosen. Polynomial multiplication with one scalar input is identified
with the corresponding actual pairing by explicit coordinate equivalences.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass

namespace Character

theorem permuted_pX (f : Character) (i : Fin 6) :
    (f.permuted i).pX = ![f.pX, f.pY, f.pX, f.pY, f.pZ, f.pZ] i :=
  TensorSpectrum.TensorClass.Character.permuted_pX f i

end Character
end MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass
