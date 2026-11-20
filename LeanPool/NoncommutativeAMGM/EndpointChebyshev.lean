/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.ZeroSlice

/-! # Endpoint-retaining positivity of the plus Chebyshev matrix expression -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix Polynomial Polynomial.Chebyshev
open scoped BigOperators

theorem booleanMatrixImage_endpoint {n m : ℕ} {ι κ : Type*} (ζ : ℂ)
    (M : Matrix ι κ (BooleanPolynomial n)) :
    booleanMatrixImage (rootEndpointLinearMap n m ζ) M =
      booleanMatrixImage (rootSliceLinearMap n m 1 ζ) M -
        (m : ℝ)⁻¹ • booleanMatrixImage (sliceFunctional n 0) M := by
  apply Matrix.ext
  intro i j
  rfl

/-- The plus Chebyshev expression retains a quantitative endpoint mass. -/
theorem rootSlice_chebyshev_plus_endpoint {ζ : ℂ} {n m dim : ℕ}
    (E : Fin n → Matrix (Fin dim) (Fin dim) ℝ)
    (hE : ∀ a, (E a).PosSemidef) (hmean : (1 - ∑ a, E a).PosSemidef)
    (hn : 0 < n) (hm : 2 ≤ m) (hnd : 2 * ((m + 1) / 2) ^ 2 ≤ n)
    (hζ : IsPrimitiveRoot ζ m) :
    (booleanMatrixImage (rootSliceLinearMap n m 1 ζ)
      (1 + aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ))) -
        (2 / (m : ℝ)) • 1).PosSemidef := by
  let δ := (m + 1) / 2
  have hδpos : 1 ≤ δ := by dsimp [δ]; omega
  have hdn : 2 * δ ≤ n := by change 2 * δ ^ 2 ≤ n at hnd; nlinarith
  have hdm : 2 * δ ≤ m + 1 := by dsimp [δ]; omega
  have happly {κ : Type} [Fintype κ] (F : Matrix (Fin dim) κ (BooleanPolynomial n))
      (hF : ∀ i a, BooleanDegreeLE (F i a) δ) :
      (booleanMatrixImage (rootEndpointLinearMap n m ζ) (booleanGram F)).PosSemidef := by
    apply booleanMatrixImage_gram_posSemidef _ _ F hF
    intro f hf
    exact rootEndpointLinearMap_square_nonneg f hn hm hζ hf hdn hdm hnd
  have hM : (booleanMatrixImage (rootEndpointLinearMap n m ζ)
      (1 + aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ)))).PosSemidef := by
    let r := m / 2
    by_cases heven : m % 2 = 0
    · have hmr : m = 2 * r := by dsimp [r]; omega
      have hδ : δ = r := by dsimp [δ]; omega
      have hmi : (m : ℤ) = 2 * (r : ℤ) := by exact_mod_cast hmr
      rw [hmi]
      obtain ⟨F, hF, he⟩ := chebyshev_even_plus_gram E hE r
      rw [he]
      exact happly F (by simpa only [hδ] using hF)
    · have hmr : m = 2 * r + 1 := by dsimp [r]; omega
      have hδ : δ = r + 1 := by dsimp [δ]; omega
      have hmi : (m : ℤ) = 2 * (r : ℤ) + 1 := by exact_mod_cast hmr
      rw [hmi]
      obtain ⟨F, hF, he⟩ := chebyshev_odd_plus_gram E hE hmean r
      rw [he]
      exact happly F (by simpa only [hδ] using hF)
  have hzero : booleanMatrixImage (sliceFunctional n 0)
      (1 + aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ))) = (2 : ℝ) • 1 := by
    rw [booleanMatrixImage_add, zero_slice_chebyshev,
      booleanMatrixImage_one _ (by rw [sliceFunctional_zero_eval, map_one])]
    simp only [two_smul]
  rw [booleanMatrixImage_endpoint, hzero, smul_smul] at hM
  simpa only [div_eq_mul_inv, mul_comm (m : ℝ)⁻¹ 2] using hM

end NoncommutativeAMGM
