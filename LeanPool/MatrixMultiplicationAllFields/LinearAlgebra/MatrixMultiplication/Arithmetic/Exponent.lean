/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.NaiveAlgorithm
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.LowerBound
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.Padding

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Division-free arithmetic programs over a field and their operation counts. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

theorem AdmissibleExponent.mono {τ σ : ℝ} (hτ : AdmissibleExponent F τ)
    (hτσ : τ ≤ σ) : AdmissibleExponent F σ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (add_le_add_left hτσ ε)

theorem omega_two_le : 2 ≤ omega F :=
  le_csInf admissibleExponent_nonempty (fun _ hτ => admissibleExponent_two_le hτ)

theorem omega_nonneg : 0 ≤ omega F := le_trans (by norm_num) omega_two_le

theorem omega_le_three : omega F ≤ 3 :=
  omega_le_of_admissibleExponent admissibleExponent_three

theorem omega_admissibleExponent : AdmissibleExponent F (omega F) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨τ, hτ, hclose⟩ := exists_lt_of_csInf_lt admissibleExponent_nonempty
    (show sInf {σ : ℝ | AdmissibleExponent F σ} < omega F + ε / 2 from
      lt_add_of_pos_right (omega F) hhalf)
  obtain ⟨C, hC, hbound⟩ := hτ (ε / 2) hhalf
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem admissibleExponent_iff_omega_le {τ : ℝ} :
    AdmissibleExponent F τ ↔ omega F ≤ τ :=
  ⟨omega_le_of_admissibleExponent, omega_admissibleExponent.mono⟩

theorem RectangularAdmissibleExponent.mono {k τ σ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) (hτσ : τ ≤ σ) :
    RectangularAdmissibleExponent F k σ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (add_le_add_left hτσ ε)

theorem rectangularAdmissibleExponent_of_uniform_costs {k τ C : ℝ} (hC : 0 < C)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n (innerSize n k) n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ τ) :
    RectangularAdmissibleExponent F k τ := by
  intro ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (le_add_of_nonneg_right hε.le)

theorem rectangularAdmissibleExponent_naive (k : ℝ) :
    RectangularAdmissibleExponent F k (2 + max k 0) := by
  apply rectangularAdmissibleExponent_of_uniform_costs (C := 4) (by norm_num)
  intro n hn
  refine ⟨naiveAlgorithm n (innerSize n k) n,
    naiveAlgorithm_correct n (innerSize n k) n, ?_⟩
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hinner : (innerSize n k : ℝ) ≤ 2 * (n : ℝ) ^ max k 0 :=
    (Nat.cast_le.mpr (innerSize_mono hn (le_max_left k 0))).trans
      (innerSize_cast_le hn (le_max_right k 0))
  rw [naiveAlgorithm_cost]
  push_cast
  calc
    2 * (n : ℝ) * innerSize n k * n = 2 * (n : ℝ) ^ 2 * innerSize n k := by ring
    _ ≤ 2 * (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ max k 0) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 4 * (n : ℝ) ^ (2 + max k 0) := by
      rw [Real.rpow_add hnpos]
      norm_num
      ring

theorem rectangularAdmissibleExponent_nonempty (k : ℝ) :
    Set.Nonempty {τ : ℝ | RectangularAdmissibleExponent F k τ} :=
  ⟨2 + max k 0, rectangularAdmissibleExponent_naive k⟩

theorem rectangularOmega_two_le (k : ℝ) : 2 ≤ rectangularOmega F k :=
  le_csInf (rectangularAdmissibleExponent_nonempty k)
    (fun _ hτ => rectangularAdmissibleExponent_two_le hτ)

theorem rectangularOmega_admissibleExponent (k : ℝ) :
    RectangularAdmissibleExponent F k (rectangularOmega F k) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨τ, hτ, hclose⟩ := exists_lt_of_csInf_lt (rectangularAdmissibleExponent_nonempty k)
    (show sInf {σ : ℝ | RectangularAdmissibleExponent F k σ} <
        rectangularOmega F k + ε / 2 from lt_add_of_pos_right (rectangularOmega F k) hhalf)
  obtain ⟨C, hC, hbound⟩ := hτ (ε / 2) hhalf
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem rectangularAdmissibleExponent_iff_omega_le {k τ : ℝ} :
    RectangularAdmissibleExponent F k τ ↔ rectangularOmega F k ≤ τ :=
  ⟨rectangularOmega_le_of_admissibleExponent, (rectangularOmega_admissibleExponent k).mono⟩

theorem rectangularOmega_mono {k l : ℝ} (hkl : k ≤ l) :
    rectangularOmega F k ≤ rectangularOmega F l :=
  rectangularOmega_le_of_admissibleExponent
    ((rectangularOmega_admissibleExponent l).mono_aspect hkl)

@[simp] theorem rectangularOmega_zero : rectangularOmega F 0 = 2 := by
  apply le_antisymm _ (rectangularOmega_two_le 0)
  apply rectangularOmega_le_of_admissibleExponent
  simpa using (rectangularAdmissibleExponent_naive (F := F) 0)

theorem complexAlpha_set_nonempty :
    Set.Nonempty {k : ℝ | k ∈ Set.Icc 0 1 ∧ rectangularOmega ℂ k = 2} :=
  ⟨0, ⟨by norm_num, by norm_num⟩, rectangularOmega_zero⟩

theorem complexAlpha_set_bddAbove :
    BddAbove {k : ℝ | k ∈ Set.Icc 0 1 ∧ rectangularOmega ℂ k = 2} :=
  ⟨1, fun _ h => h.1.2⟩

theorem le_complexAlpha {k : ℝ} (hk : k ∈ Set.Icc 0 1)
    (hω : rectangularOmega ℂ k = 2) : k ≤ complexAlpha :=
  le_csSup complexAlpha_set_bddAbove ⟨hk, hω⟩

theorem complexAlpha_le_one : complexAlpha ≤ 1 :=
  csSup_le complexAlpha_set_nonempty (fun _ h => h.1.2)

theorem complexAlpha_nonneg : 0 ≤ complexAlpha :=
  le_complexAlpha ⟨le_refl 0, by norm_num⟩ rectangularOmega_zero

end MatrixMultiplication.Arithmetic

end

end MatrixMultiplicationAllFields
