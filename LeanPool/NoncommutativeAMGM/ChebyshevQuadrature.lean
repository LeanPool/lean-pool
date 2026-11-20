/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.ChebyshevImage
public import LeanPool.NoncommutativeAMGM.MatrixSlicePositivity
public import LeanPool.NoncommutativeAMGM.SliceQuadraturePositivity

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
  apply chebyshevImage_posSemidef (by omega) E hE hmean
  intro f hf
  change 0 ≤ rootSliceFunctional n m ξ ζ (f ^ 2)
  exact rootSliceFunctional_square_nonneg f hn hm hζ hξ hη hf
    (by nlinarith) (by omega) hnd

/-- The quadratic-threshold quadrature maps each actual Boolean matrix Gram sum to a PSD matrix. -/
theorem rootSlice_gram_posSemidef {ξ ζ : ℂ} {η : ℝ} {n m d : ℕ}
    {ι κ : Type*} [Finite ι] [Fintype κ]
    (F : Matrix ι κ (BooleanPolynomial n)) (hn : 0 < n) (hm : 2 ≤ m)
    (hζ : IsPrimitiveRoot ζ m) (hξ : ξ ^ m = (η : ℂ)) (hη : η = 1 ∨ η = -1)
    (hF : ∀ i a, BooleanDegreeLE (F i a) d) (hdn : 2 * d ≤ n)
    (hdm : 2 * d ≤ m + 1) (hnd : 2 * d ^ 2 ≤ n) :
    (booleanMatrixImage (rootSliceLinearMap n m ξ ζ) (booleanGram F)).PosSemidef := by
  apply booleanMatrixImage_gram_posSemidef _ _ F hF
  intro f hf
  exact rootSliceFunctional_square_nonneg f hn hm hζ hξ hη hf hdn hdm hnd

end NoncommutativeAMGM
