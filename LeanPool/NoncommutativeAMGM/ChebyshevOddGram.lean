/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.BooleanInputGram

/-! # The odd-degree Boolean matrix Chebyshev Gram factors -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The odd minus factor uses the input Gram factor and the fourth-kind polynomial. -/
theorem chebyshev_odd_minus_gram {n d : ℕ} (E : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (hE : ∀ a, (E a).PosSemidef) (r : ℕ) :
    ∃ F : Matrix (Fin d) (Fin n × Fin d) (BooleanPolynomial n),
      (∀ i a, BooleanDegreeLE (F i a) (r + 1)) ∧
      1 - aeval (booleanChebyshevArgument E) (T ℝ (2 * (r : ℤ) + 1)) = booleanGram F := by
  classical
  let X := booleanChebyshevArgument E
  let B := booleanLinearMatrix E
  let P := aeval X (chebyshevMinusFactor r)
  have hXt : X.transpose = X := booleanChebyshevArgument_transpose E (fun a ↦ by
    simpa only [conjTranspose_eq_transpose_of_trivial] using (hE a).isHermitian.eq)
  have hPt : P.transpose = P := booleanMatrix_aeval_transpose X hXt _
  obtain ⟨G, hG, heG⟩ := booleanLinearMatrix_gram E hE
  refine ⟨Real.sqrt 2 • (P * G), ?_, ?_⟩
  · intro i a
    apply booleanDegreeLE_smul
    have hP : ∀ i j, BooleanDegreeLE (P i j) r := fun i j ↦
      booleanDegreeLE_mono (booleanMatrix_aeval_degree X (booleanChebyshevArgument_degree E)
        (chebyshevMinusFactor r) i j) (chebyshevMinusFactor_natDegree r)
    exact booleanMatrix_mul_degree P G hP hG i a
  · rw [booleanGram_smul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      booleanGram_mul, ← heG, hPt]
    have hpoly : 1 - T ℝ (2 * (r : ℤ) + 1) =
        chebyshevMinusFactor r * (1 - Polynomial.X) * chebyshevMinusFactor r := by
      rw [chebyshev_odd_minus]
      ring
    have he := congrArg (aeval X) hpoly
    simp only [map_sub, map_one, map_mul, aeval_X] at he
    have hv : 1 - X = (2 : ℝ) • B := by dsimp [X, booleanChebyshevArgument, B]; abel
    rw [hv] at he
    change 1 - aeval X (T ℝ (2 * (r : ℤ) + 1)) = (2 : ℝ) • (P * B * P)
    rw [he, Matrix.mul_smul, Matrix.smul_mul]

/-- The odd plus factor includes the full slack in the complement Gram factor. -/
theorem chebyshev_odd_plus_gram {n d : ℕ} (E : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (hE : ∀ a, (E a).PosSemidef) (hmean : (1 - ∑ a, E a).PosSemidef) (r : ℕ) :
    ∃ F : Matrix (Fin d) ((Fin n × Fin d) ⊕ Fin d) (BooleanPolynomial n),
      (∀ i a, BooleanDegreeLE (F i a) (r + 1)) ∧
      1 + aeval (booleanChebyshevArgument E) (T ℝ (2 * (r : ℤ) + 1)) = booleanGram F := by
  classical
  let X := booleanChebyshevArgument E
  let B := booleanLinearMatrix E
  let P := aeval X (chebyshevPlusFactor r)
  have hXt : X.transpose = X := booleanChebyshevArgument_transpose E (fun a ↦ by
    simpa only [conjTranspose_eq_transpose_of_trivial] using (hE a).isHermitian.eq)
  have hPt : P.transpose = P := booleanMatrix_aeval_transpose X hXt _
  obtain ⟨G, hG, heG⟩ := booleanLinearMatrix_complement_gram E hE hmean
  refine ⟨Real.sqrt 2 • (P * G), ?_, ?_⟩
  · intro i a
    apply booleanDegreeLE_smul
    have hP : ∀ i j, BooleanDegreeLE (P i j) r := fun i j ↦
      booleanDegreeLE_mono (booleanMatrix_aeval_degree X (booleanChebyshevArgument_degree E)
        (chebyshevPlusFactor r) i j) (chebyshevPlusFactor_natDegree r)
    exact booleanMatrix_mul_degree P G hP hG i a
  · rw [booleanGram_smul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      booleanGram_mul, ← heG, hPt]
    have hpoly : 1 + T ℝ (2 * (r : ℤ) + 1) =
        chebyshevPlusFactor r * (1 + Polynomial.X) * chebyshevPlusFactor r := by
      rw [chebyshev_odd_plus]
      ring
    have he := congrArg (aeval X) hpoly
    simp only [map_add, map_one, map_mul, aeval_X] at he
    have hv : 1 + X = (2 : ℝ) • (1 - B) := by
      simp only [X, booleanChebyshevArgument, B, Algebra.smul_def, map_ofNat]
      noncomm_ring
    rw [hv] at he
    change 1 + aeval X (T ℝ (2 * (r : ℤ) + 1)) = (2 : ℝ) • (P * (1 - B) * P)
    rw [he, Matrix.mul_smul, Matrix.smul_mul]

end NoncommutativeAMGM
