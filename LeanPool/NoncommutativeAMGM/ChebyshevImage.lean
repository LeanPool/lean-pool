/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.ChebyshevOddGram

/-! # Chebyshev matrix positivity for any degree-bounded positive Boolean functional -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix Polynomial Polynomial.Chebyshev
open scoped BigOperators

theorem chebyshevImage_posSemidef {n dim m : ℕ} (hm : 1 ≤ m)
    (E : Fin n → Matrix (Fin dim) (Fin dim) ℝ)
    (hE : ∀ a, (E a).PosSemidef) (hmean : (1 - ∑ a, E a).PosSemidef)
    (L : BooleanPolynomial n →ₗ[ℝ] ℝ)
    (hL : ∀ f : BooleanPolynomial n, BooleanDegreeLE f ((m + 1) / 2) → 0 ≤ L (f ^ 2)) :
    (booleanMatrixImage L (1 - aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ)))).PosSemidef ∧
      (booleanMatrixImage L (1 + aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ)))).PosSemidef := by
  let δ := (m + 1) / 2
  have happly {κ : Type} [Fintype κ] (F : Matrix (Fin dim) κ (BooleanPolynomial n))
      (hF : ∀ i a, BooleanDegreeLE (F i a) δ) : (booleanMatrixImage L (booleanGram F)).PosSemidef :=
    booleanMatrixImage_gram_posSemidef L hL F hF
  let r := m / 2
  by_cases heven : m % 2 = 0
  · have hmr : m = 2 * r := by dsimp [r]; omega
    have hδ : δ = r := by dsimp [δ]; omega
    have hmi : (m : ℤ) = 2 * (r : ℤ) := by exact_mod_cast hmr
    rw [hmi]
    obtain ⟨F, hF, heF⟩ := chebyshev_even_minus_gram E hE hmean r (by omega)
    obtain ⟨G, hG, heG⟩ := chebyshev_even_plus_gram E hE r
    rw [heF, heG]
    exact ⟨happly F (by simpa only [hδ] using hF), happly G (by simpa only [hδ] using hG)⟩
  · have hmr : m = 2 * r + 1 := by dsimp [r]; omega
    have hδ : δ = r + 1 := by dsimp [δ]; omega
    have hmi : (m : ℤ) = 2 * (r : ℤ) + 1 := by exact_mod_cast hmr
    rw [hmi]
    obtain ⟨F, hF, heF⟩ := chebyshev_odd_minus_gram E hE r
    obtain ⟨G, hG, heG⟩ := chebyshev_odd_plus_gram E hE hmean r
    rw [heF, heG]
    exact ⟨happly F (by simpa only [hδ] using hF), happly G (by simpa only [hδ] using hG)⟩

end NoncommutativeAMGM
