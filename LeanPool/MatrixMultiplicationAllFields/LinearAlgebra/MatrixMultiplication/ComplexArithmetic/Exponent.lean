/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.NaiveAlgorithm
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.LowerBound

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

theorem AdmissibleExponent.mono {τ σ : ℝ} (hτ : AdmissibleExponent τ)
    (hτσ : τ ≤ σ) : AdmissibleExponent σ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (add_le_add_left hτσ ε)

theorem omega_le_of_admissibleExponent {τ : ℝ} (hτ : AdmissibleExponent τ) :
    omega ≤ τ :=
  csInf_le admissibleExponent_bddBelow hτ

theorem omega_nonneg : 0 ≤ omega :=
  le_csInf admissibleExponent_nonempty (fun _ hτ => admissibleExponent_nonneg hτ)

theorem omega_le_three : omega ≤ 3 :=
  omega_le_of_admissibleExponent admissibleExponent_three

theorem omega_admissibleExponent : AdmissibleExponent omega := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨τ, hτ, hclose⟩ := exists_lt_of_csInf_lt admissibleExponent_nonempty
    (show sInf {σ : ℝ | AdmissibleExponent σ} < omega + ε / 2 from
      lt_add_of_pos_right omega hhalf)
  obtain ⟨C, hC, hbound⟩ := hτ (ε / 2) hhalf
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem admissibleExponent_iff_omega_le {τ : ℝ} :
    AdmissibleExponent τ ↔ omega ≤ τ :=
  ⟨omega_le_of_admissibleExponent, omega_admissibleExponent.mono⟩

end MatrixMultiplication.Foundation.Arithmetic

end

end MatrixMultiplicationAllFields
