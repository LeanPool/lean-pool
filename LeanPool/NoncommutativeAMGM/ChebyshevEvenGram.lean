/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.BooleanMatrixPolynomial

/-! # The even-degree Boolean matrix Chebyshev Gram factors -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix Polynomial Polynomial.Chebyshev

theorem booleanGram_smul {n : ℕ} {ι κ : Type*} [Fintype κ]
    (a : ℝ) (F : Matrix ι κ (BooleanPolynomial n)) :
    booleanGram (a • F) = (a * a) • booleanGram F := by
  change (a • F) * (a • F).transpose = (a * a) • (F * F.transpose)
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem booleanGram_mul {n : ℕ} {ι κ μ : Type*} [Fintype κ] [Fintype μ]
    (U : Matrix ι κ (BooleanPolynomial n)) (F : Matrix κ μ (BooleanPolynomial n)) :
    booleanGram (U * F) = U * booleanGram F * U.transpose := by
  change (U * F) * (U * F).transpose = U * (F * F.transpose) * U.transpose
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- The even plus factor, of degree at most `r`. -/
theorem chebyshev_even_plus_gram {n d : ℕ} (E : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (hE : ∀ a, (E a).PosSemidef) (r : ℕ) :
    ∃ F : Matrix (Fin d) (Fin d) (BooleanPolynomial n),
      (∀ i j, BooleanDegreeLE (F i j) r) ∧
      1 + aeval (booleanChebyshevArgument E) (T ℝ (2 * (r : ℤ))) = booleanGram F := by
  let X := booleanChebyshevArgument E
  let P := aeval X (T ℝ (r : ℤ))
  have hXt : X.transpose = X := booleanChebyshevArgument_transpose E (fun a ↦ by
    simpa only [conjTranspose_eq_transpose_of_trivial] using (hE a).isHermitian.eq)
  have hPt : P.transpose = P := booleanMatrix_aeval_transpose X hXt _
  refine ⟨Real.sqrt 2 • P, ?_, ?_⟩
  · intro i j
    apply booleanDegreeLE_smul
    have hp := booleanMatrix_aeval_degree X (booleanChebyshevArgument_degree E) (T ℝ (r : ℤ))
    simpa only [natDegree_T, Int.natAbs_natCast] using hp i j
  · rw [booleanGram_smul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have he := congrArg (aeval X) (chebyshev_even_plus r)
    simp only [map_add, map_one, map_mul, map_ofNat, map_pow] at he
    change 1 + aeval X (T ℝ (2 * (r : ℤ))) = (2 : ℝ) • (P * P.transpose)
    rw [hPt]
    simpa only [P, Algebra.smul_def, map_ofNat, pow_two] using he

/-- The even minus factor built from the actual input variance, of degree at most `r`. -/
theorem chebyshev_even_minus_gram {n d : ℕ} (E : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (hE : ∀ a, (E a).PosSemidef) (hmean : (1 - ∑ a, E a).PosSemidef)
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ F : Matrix (Fin d) (Fin n × Fin d) (BooleanPolynomial n),
      (∀ i a, BooleanDegreeLE (F i a) r) ∧
      1 - aeval (booleanChebyshevArgument E) (T ℝ (2 * (r : ℤ))) = booleanGram F := by
  classical
  let X := booleanChebyshevArgument E
  let B := booleanLinearMatrix E
  let P := aeval X (U ℝ ((r : ℤ) - 1))
  have hXt : X.transpose = X := booleanChebyshevArgument_transpose E (fun a ↦ by
    simpa only [conjTranspose_eq_transpose_of_trivial] using (hE a).isHermitian.eq)
  have hPt : P.transpose = P := booleanMatrix_aeval_transpose X hXt _
  obtain ⟨G, hG, heG⟩ := booleanLinearMatrix_variance_factor E hE hmean
  refine ⟨Real.sqrt 8 • (P * G), ?_, ?_⟩
  · intro i a
    apply booleanDegreeLE_smul
    have hP : ∀ i j, BooleanDegreeLE (P i j) (r - 1) := by
      have hp := booleanMatrix_aeval_degree X (booleanChebyshevArgument_degree E)
        (U ℝ ((r : ℤ) - 1))
      simpa only [natDegree_U, sub_add_cancel, Int.natAbs_natCast] using hp
    have hh := booleanMatrix_mul_degree P G hP hG i a
    exact booleanDegreeLE_mono hh (by omega)
  · rw [booleanGram_smul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8),
      booleanGram_mul, ← heG, hPt]
    have hpoly : 1 - T ℝ (2 * (r : ℤ)) =
        2 * U ℝ ((r : ℤ) - 1) * (1 - Polynomial.X ^ 2) * U ℝ ((r : ℤ) - 1) := by
      rw [chebyshev_even_minus]
      ring
    have he := congrArg (aeval X) hpoly
    simp only [map_sub, map_one, map_mul, map_ofNat, map_pow, aeval_X] at he
    have hv : 1 - X ^ 2 = (4 : ℝ) • (B - B * B) := by
      simp only [X, booleanChebyshevArgument, B, Algebra.smul_def, map_ofNat]
      noncomm_ring
    rw [hv] at he
    change 1 - aeval X (T ℝ (2 * (r : ℤ))) = (8 : ℝ) • (P * (B - B * B) * P)
    rw [he]
    simp only [P, Algebra.smul_def, map_ofNat]
    noncomm_ring

end NoncommutativeAMGM
