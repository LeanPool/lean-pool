/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Arithmetic/RankBound.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; `[IsAlgClosed K]` is assumed by the
declarations that use it.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Existence
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.CharacterRounding
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Inequalities
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The exact-rank exponent bound

Detecting characters exist by Appendix A. The determinant and three-sector
polynomial constructions bound the sum of their dot-product exponents by
`9/4`. Integer rounding then gives the same bound for the exact-rank exponent.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



namespace MatrixMultiplication.AuxiliarySeparation

/-- The polynomial inequalities bound the actual exact-rank exponent. -/
theorem exactRankExponent_le_nine_quarters [IsAlgClosed K] : exactRankExponent K ≤ (9 : ℝ) / 4 := by
  apply exactRankExponent_le_nine_quarters_of_characters
  · intro d hd k hk
    exact exists_detecting_character hd hk
  · intro χ d hd
    rw [χ.value_matrixMultiplication (by omega)]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ d by omega)) χ.exponent_sum_le_nine_quarters

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
