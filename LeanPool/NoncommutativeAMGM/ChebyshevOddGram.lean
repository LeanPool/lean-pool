/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

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
  obtain ⟨G, hG, heG⟩ := booleanLinearMatrix_gram E hE
  obtain ⟨hdegree, hgram⟩ := booleanGram_aeval_smul_mul X hXt
    (booleanChebyshevArgument_degree E) (chebyshevMinusFactor r)
    (chebyshevMinusFactor_natDegree r) 2 (by norm_num) G hG
  refine ⟨Real.sqrt 2 • (P * G), hdegree, ?_⟩
  rw [hgram, ← heG]
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
  obtain ⟨G, hG, heG⟩ := booleanLinearMatrix_complement_gram E hE hmean
  obtain ⟨hdegree, hgram⟩ := booleanGram_aeval_smul_mul X hXt
    (booleanChebyshevArgument_degree E) (chebyshevPlusFactor r)
    (chebyshevPlusFactor_natDegree r) 2 (by norm_num) G hG
  refine ⟨Real.sqrt 2 • (P * G), hdegree, ?_⟩
  rw [hgram, ← heG]
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
