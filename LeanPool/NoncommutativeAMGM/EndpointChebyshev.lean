/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.ZeroSlice
public import LeanPool.NoncommutativeAMGM.ChebyshevImage

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
  have hM := (chebyshevImage_posSemidef (by omega) E hE hmean (rootEndpointLinearMap n m ζ)
    (fun f hf ↦ rootEndpointLinearMap_square_nonneg f hn hm hζ hf
      (by nlinarith) (by omega) hnd)).2
  have hzero : booleanMatrixImage (sliceFunctional n 0)
      (1 + aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ))) = (2 : ℝ) • 1 := by
    rw [booleanMatrixImage_add, zero_slice_chebyshev,
      booleanMatrixImage_one _ (by rw [sliceFunctional_zero_eval, map_one])]
    simp only [two_smul]
  rw [booleanMatrixImage_endpoint, hzero, smul_smul] at hM
  simpa only [div_eq_mul_inv, mul_comm (m : ℝ)⁻¹ 2] using hM

end NoncommutativeAMGM
