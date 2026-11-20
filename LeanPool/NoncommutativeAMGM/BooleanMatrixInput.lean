/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.BooleanVariance

/-! # Constructing the Boolean compression from arbitrary PSD matrix inputs -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix
open scoped BigOperators

/-- The block row consisting of all real Gram factors. -/
noncomputable def gramBlockRow {n : ℕ} {ι : Type*} (S : Fin n → Matrix ι ι ℝ) :
    Matrix ι (Fin n × ι) ℝ := fun i a ↦ S a.1 i a.2

theorem gramBlockRow_mul_transpose {n : ℕ} {ι : Type*} [Fintype ι]
    (S : Fin n → Matrix ι ι ℝ) :
    gramBlockRow S * (gramBlockRow S).transpose = ∑ a, S a * (S a).transpose := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, gramBlockRow, Matrix.sum_apply,
    Fintype.sum_prod_type]

/-- The matrix-valued square-free linear polynomial `Σ zᵢ Eᵢ`. -/
noncomputable def booleanLinearMatrix {n : ℕ} {ι : Type*} (E : Fin n → Matrix ι ι ℝ) :
    Matrix ι ι (BooleanPolynomial n) := fun i j ↦
  ∑ a, booleanVar a * algebraMap ℝ (BooleanPolynomial n) (E a i j)

theorem booleanCompression_blockRow (n d : ℕ) (S : Fin n → Matrix (Fin d) (Fin d) ℝ) :
    booleanCompression n d (gramBlockRow S) =
      booleanLinearMatrix (fun a ↦ S a * (S a).transpose) := by
  apply Matrix.ext
  intro i j
  change ((constantBooleanMatrix n (gramBlockRow S) *
    diagonal (fun a : Fin n × Fin d ↦ booleanVar a.1)) *
      (constantBooleanMatrix n (gramBlockRow S)).transpose) i j = _
  change (∑ a : Fin n × Fin d,
    (constantBooleanMatrix n (gramBlockRow S) *
      diagonal (fun a : Fin n × Fin d ↦ booleanVar a.1)) i a *
        constantBooleanMatrix n (gramBlockRow S) j a) = _
  simp only [Matrix.mul_diagonal]
  simp only [Matrix.transpose_apply, constantBooleanMatrix, Matrix.map_apply,
    gramBlockRow, booleanLinearMatrix, Fintype.sum_prod_type, Matrix.mul_apply, map_sum,
    map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The variance of `Σ zᵢ Eᵢ` has a degree-one Gram factor for any PSD tuple
with sum at most `I`. -/
theorem booleanLinearMatrix_variance_factor {n d : ℕ}
    (E : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (hE : ∀ a, (E a).PosSemidef) (hmean : (1 - ∑ a, E a).PosSemidef) :
    ∃ G : Matrix (Fin d) (Fin n × Fin d) (BooleanPolynomial n),
      (∀ i a, BooleanDegreeLE (G i a) 1) ∧
      booleanLinearMatrix E - booleanLinearMatrix E * booleanLinearMatrix E = booleanGram G := by
  choose S hS using fun a ↦ posSemidef_exists_gram (E a) (hE a)
  have hR : (1 - gramBlockRow S * (gramBlockRow S).transpose).PosSemidef := by
    rw [gramBlockRow_mul_transpose]
    simpa only [← hS] using hmean
  obtain ⟨G, hG, he⟩ := booleanCompression_variance_factor n d (gramBlockRow S) hR
  refine ⟨G, hG, ?_⟩
  simpa only [booleanCompression_blockRow, ← hS] using he

end NoncommutativeAMGM
