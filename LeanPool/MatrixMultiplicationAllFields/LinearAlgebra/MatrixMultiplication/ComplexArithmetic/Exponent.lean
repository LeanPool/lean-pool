/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.NaiveAlgorithm
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.LowerBound

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Complex arithmetic interfaces specialized from the shared field-generic implementation. -/

@[expose] public section

namespace MatrixMultiplicationAllFields

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic

theorem AdmissibleExponent.mono {τ σ : ℝ} (hτ : AdmissibleExponent τ)
    (hτσ : τ ≤ σ) : AdmissibleExponent σ :=
  MatrixMultiplication.Arithmetic.AdmissibleExponent.mono (F := ℂ) hτ hτσ

theorem omega_le_of_admissibleExponent {τ : ℝ} (hτ : AdmissibleExponent τ) :
    omega ≤ τ :=
  MatrixMultiplication.Arithmetic.omega_le_of_admissibleExponent (F := ℂ) hτ

theorem omega_nonneg : 0 ≤ omega :=
  MatrixMultiplication.Arithmetic.omega_nonneg (F := ℂ)

theorem omega_le_three : omega ≤ 3 :=
  MatrixMultiplication.Arithmetic.omega_le_three (F := ℂ)

theorem omega_admissibleExponent : AdmissibleExponent omega :=
  MatrixMultiplication.Arithmetic.omega_admissibleExponent (F := ℂ)

theorem admissibleExponent_iff_omega_le {τ : ℝ} :
    AdmissibleExponent τ ↔ omega ≤ τ :=
  MatrixMultiplication.Arithmetic.admissibleExponent_iff_omega_le (F := ℂ)

end MatrixMultiplication.Foundation.Arithmetic

end

end MatrixMultiplicationAllFields
