/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.ChebyshevOddGram

/-! # Positivity of the actual Chebyshev matrix root quadratures -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- At the quadratic threshold, both signed Chebyshev matrix expressions have PSD
root-grid slice quadratures. The Gram factors and scalar positivity are constructed. -/
theorem rootSlice_chebyshev_posSemidef {ξ ζ : ℂ} {η : ℝ} {n m dim : ℕ}
    (E : Fin n → Matrix (Fin dim) (Fin dim) ℝ)
    (hE : ∀ a, (E a).PosSemidef) (hmean : (1 - ∑ a, E a).PosSemidef)
    (hn : 0 < n) (hm : 2 ≤ m) (hnd : 2 * ((m + 1) / 2) ^ 2 ≤ n)
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = (η : ℂ)) (hη : η = 1 ∨ η = -1) :
    (booleanMatrixImage (rootSliceLinearMap n m ξ ζ)
      (1 - aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ)))).PosSemidef ∧
    (booleanMatrixImage (rootSliceLinearMap n m ξ ζ)
      (1 + aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ)))).PosSemidef := by
  let δ := (m + 1) / 2
  have hδpos : 1 ≤ δ := by dsimp [δ]; omega
  have hdn : 2 * δ ≤ n := by change 2 * δ ^ 2 ≤ n at hnd; nlinarith
  have hdm : 2 * δ ≤ m + 1 := by dsimp [δ]; omega
  have happly {κ : Type} [Fintype κ] (F : Matrix (Fin dim) κ (BooleanPolynomial n))
      (hF : ∀ i a, BooleanDegreeLE (F i a) δ) :
      (booleanMatrixImage (rootSliceLinearMap n m ξ ζ) (booleanGram F)).PosSemidef :=
    rootSlice_gram_posSemidef F hn hm hζ hξ hη hF hdn hdm hnd
  let r := m / 2
  by_cases heven : m % 2 = 0
  · have hmr : m = 2 * r := by dsimp [r]; omega
    have hδ : δ = r := by dsimp [δ]; omega
    have hmi : (m : ℤ) = 2 * (r : ℤ) := by exact_mod_cast hmr
    have hr : 1 ≤ r := by omega
    rw [hmi]
    obtain ⟨F, hF, hFm⟩ := chebyshev_even_minus_gram E hE hmean r hr
    obtain ⟨G, hG, hGp⟩ := chebyshev_even_plus_gram E hE r
    rw [hFm, hGp]
    constructor
    · exact happly F (by simpa only [hδ] using hF)
    · exact happly G (by simpa only [hδ] using hG)
  · have hmr : m = 2 * r + 1 := by dsimp [r]; omega
    have hδ : δ = r + 1 := by dsimp [δ]; omega
    have hmi : (m : ℤ) = 2 * (r : ℤ) + 1 := by exact_mod_cast hmr
    rw [hmi]
    obtain ⟨F, hF, hFm⟩ := chebyshev_odd_minus_gram E hE r
    obtain ⟨G, hG, hGp⟩ := chebyshev_odd_plus_gram E hE hmean r
    rw [hFm, hGp]
    constructor
    · exact happly F (by simpa only [hδ] using hF)
    · exact happly G (by simpa only [hδ] using hG)

end NoncommutativeAMGM
