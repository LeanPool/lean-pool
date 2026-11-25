/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Character.Dots
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.CharacterPower
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorCharacterPowers

/-!
# Character exponents of the auxiliary pairings

The power laws follow from the actual coordinate restrictions and product
identities. Their exponents are constructed here, rather than supplied as
assumptions about a character.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral
    MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.TensorClass.Character

/-- The specialization of `pX` to this coefficient ring. -/
abbrev pX (f : Character) : ℝ :=
  TensorSpectrum.TensorClass.Character.pX f

/-- The specialization of `pY` to this coefficient ring. -/
abbrev pY (f : Character) : ℝ :=
  TensorSpectrum.TensorClass.Character.pY f

/-- The specialization of `pZ` to this coefficient ring. -/
abbrev pZ (f : Character) : ℝ :=
  TensorSpectrum.TensorClass.Character.pZ f

theorem pX_nonneg (f : Character) : 0 ≤ f.pX :=
  TensorSpectrum.TensorClass.Character.pX_nonneg f

theorem pY_nonneg (f : Character) : 0 ≤ f.pY :=
  TensorSpectrum.TensorClass.Character.pY_nonneg f

theorem pZ_nonneg (f : Character) : 0 ≤ f.pZ :=
  TensorSpectrum.TensorClass.Character.pZ_nonneg f

theorem pX_le_one (f : Character) : f.pX ≤ 1 :=
  TensorSpectrum.TensorClass.Character.pX_le_one f

theorem pY_le_one (f : Character) : f.pY ≤ 1 :=
  TensorSpectrum.TensorClass.Character.pY_le_one f

theorem pZ_le_one (f : Character) : f.pZ ≤ 1 :=
  TensorSpectrum.TensorClass.Character.pZ_le_one f

theorem dotXValue_eq_rpow (f : Character) (n : ℕ) (hn : 1 ≤ n) :
    f.dotXValue n = (n : ℝ) ^ f.pX :=
  TensorSpectrum.TensorClass.Character.dotXValue_eq_rpow f n hn

theorem dotYValue_eq_rpow (f : Character) (n : ℕ) (hn : 1 ≤ n) :
    f.dotYValue n = (n : ℝ) ^ f.pY :=
  TensorSpectrum.TensorClass.Character.dotYValue_eq_rpow f n hn

theorem dotZValue_eq_rpow (f : Character) (n : ℕ) (hn : 1 ≤ n) :
    f.dotZValue n = (n : ℝ) ^ f.pZ :=
  TensorSpectrum.TensorClass.Character.dotZValue_eq_rpow f n hn

end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.TensorClass.Character
