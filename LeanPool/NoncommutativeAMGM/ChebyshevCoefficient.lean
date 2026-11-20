/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.RootSliceExtraction
public import LeanPool.NoncommutativeAMGM.MatrixCoefficientExtraction
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-! # The leading Boolean coefficient of the actual Chebyshev matrix polynomial -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix Polynomial Polynomial.Chebyshev

/-- The scalar affine argument corresponding to the matrix argument `I-2B`. -/
noncomputable def chebyshevAffine : Polynomial ℝ := 1 - 2 * Polynomial.X

theorem chebyshevAffine_natDegree : chebyshevAffine.natDegree = 1 := by
  have hc : chebyshevAffine.coeff 1 = -2 := by norm_num [chebyshevAffine, coeff_one]
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply (natDegree_sub_le _ _).trans
    have hx : ((2 : Polynomial ℝ) * Polynomial.X).natDegree = 1 := by
      exact natDegree_C_mul_X (2 : ℝ) (by norm_num)
    exact max_le (by norm_num) hx.le
  · rw [hc]
    norm_num

theorem chebyshevAffine_coeff_one : chebyshevAffine.coeff 1 = -2 := by
  norm_num [chebyshevAffine, coeff_one]

theorem chebyshevAffine_leadingCoeff : chebyshevAffine.leadingCoeff = -2 := by
  rw [← coeff_natDegree, chebyshevAffine_natDegree, chebyshevAffine_coeff_one]

/-- The Chebyshev polynomial of degree `m` after substituting `1 - 2X`. -/
noncomputable def shiftedChebyshev (m : ℕ) : Polynomial ℝ :=
  (T ℝ (m : ℤ)).comp chebyshevAffine

theorem shiftedChebyshev_natDegree (m : ℕ) : (shiftedChebyshev m).natDegree = m := by
  rw [shiftedChebyshev, natDegree_comp, natDegree_T, Int.natAbs_natCast,
    chebyshevAffine_natDegree, mul_one]

theorem shiftedChebyshev_coeff (m : ℕ) :
    (shiftedChebyshev m).coeff m = (2 : ℝ) ^ (m - 1) * (-2 : ℝ) ^ m := by
  have hc := coeff_comp_degree_mul_degree (p := T ℝ (m : ℤ))
    (q := chebyshevAffine) (by rw [chebyshevAffine_natDegree]; norm_num)
  simpa only [shiftedChebyshev, natDegree_T, Int.natAbs_natCast, chebyshevAffine_natDegree,
    mul_one, leadingCoeff_T, chebyshevAffine_leadingCoeff] using hc

theorem shiftedChebyshev_aeval {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Fin n → Matrix ι ι ℝ) (m : ℕ) :
    aeval (booleanLinearMatrix E) (shiftedChebyshev m) =
      aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ)) := by
  rw [shiftedChebyshev, aeval_comp]
  congr 1
  simp only [chebyshevAffine, map_sub, map_one, map_mul, map_ofNat, aeval_X,
    booleanChebyshevArgument, Algebra.smul_def]

theorem chebyshev_matrix_top {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Fin n → Matrix ι ι ℝ) (m : ℕ) :
    booleanMatrixImage (layerCoefficientSum n m)
      (aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ))) =
      ((2 : ℝ) ^ (m - 1) * (-2 : ℝ) ^ m) • distinctProductSum n m E := by
  rw [← shiftedChebyshev_aeval, booleanMatrix_aeval_top E _ (by
    rw [shiftedChebyshev_natDegree]), shiftedChebyshev_coeff]

/-- Lift a normalized scalar coefficient extraction rule to the Chebyshev matrix polynomial. -/
theorem booleanMatrixImage_chebyshev_of_extracts {n m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (E : Fin n → Matrix ι ι ℝ)
    (L : BooleanPolynomial n →ₗ[ℝ] ℝ) (scale : ℝ)
    (hL : ∀ f : BooleanPolynomial n, BooleanDegreeLE f m →
      L f = ((scale / (2 : ℝ) ^ (m - 1)) * (-(n : ℝ) / 2) ^ m / falling n m) *
        layerCoefficientSum n m f) :
    booleanMatrixImage L (aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ))) =
      (scale * (n : ℝ) ^ m / falling n m) • distinctProductSum n m E := by
  apply Matrix.ext
  intro i j
  let F := aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ))
  have hdeg : BooleanDegreeLE (F i j) m := by
    simpa only [F, natDegree_T, Int.natAbs_natCast] using
      booleanMatrix_aeval_degree (booleanChebyshevArgument E) (booleanChebyshevArgument_degree E)
        (T ℝ (m : ℤ)) i j
  have htop := congrArg (fun M : Matrix ι ι ℝ ↦ M i j) (chebyshev_matrix_top E m)
  change layerCoefficientSum n m (F i j) =
    ((2 : ℝ) ^ (m - 1) * (-2 : ℝ) ^ m) * distinctProductSum n m E i j at htop
  change L (F i j) = (scale * (n : ℝ) ^ m / falling n m) * distinctProductSum n m E i j
  rw [hL _ hdeg, htop]
  have hp : (-(n : ℝ) / 2) ^ m * (-2 : ℝ) ^ m = (n : ℝ) ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  have htwo : (2 : ℝ) ^ (m - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hc : (scale / (2 : ℝ) ^ (m - 1)) * (-(n : ℝ) / 2) ^ m *
      ((2 : ℝ) ^ (m - 1) * (-2 : ℝ) ^ m) = scale * (n : ℝ) ^ m := by
    calc
      _ = scale * ((-(n : ℝ) / 2) ^ m * (-2 : ℝ) ^ m) := by field_simp
      _ = _ := by rw [hp]
  linear_combination (distinctProductSum n m E i j / falling n m) * hc

/-- The two actual matrix quadratures differ by the normalized ordered product sum. -/
theorem rootSlice_chebyshev_difference {n m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Fin n → Matrix ι ι ℝ) (hn : 0 < n) (hm : 0 < m) {ξplus ξminus ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (hξplus : ξplus ^ m = 1) (hξminus : ξminus ^ m = -1) :
    booleanMatrixImage (rootSliceLinearMap n m ξplus ζ)
        (aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ))) -
      booleanMatrixImage (rootSliceLinearMap n m ξminus ζ)
        (aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ))) =
      (2 * (n : ℝ) ^ m / falling n m) • distinctProductSum n m E := by
  let L := rootSliceLinearMap n m ξplus ζ - rootSliceLinearMap n m ξminus ζ
  change booleanMatrixImage L (aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ))) = _
  exact booleanMatrixImage_chebyshev_of_extracts E L 2
    (fun f hdegree ↦ rootSliceLinearMap_difference hn hm hζ hξplus hξminus f hdegree)

end NoncommutativeAMGM
