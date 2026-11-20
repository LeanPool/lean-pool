/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.RootCoefficientExtraction
public import LeanPool.NoncommutativeAMGM.Extraction

/-! # Exact normalization of leading Boolean-layer extraction by signed root grids -/

@[expose] public section
namespace NoncommutativeAMGM
open Polynomial
open scoped BigOperators

theorem sliceCoordinatePolynomial_coeff_one (n : ℕ) :
    (sliceCoordinatePolynomial n).coeff 1 = -(n : ℝ) / 2 := by
  norm_num [sliceCoordinatePolynomial, coeff_one]
  ring

theorem sliceCoordinatePolynomial_degree (n : ℕ) (hn : 0 < n) :
    (sliceCoordinatePolynomial n).natDegree = 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (sliceCoordinatePolynomial_natDegree n)
  rw [sliceCoordinatePolynomial_coeff_one]
  exact div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hn.ne')) (by norm_num)

theorem sliceCoordinatePolynomial_leadingCoeff (n : ℕ) (hn : 0 < n) :
    (sliceCoordinatePolynomial n).leadingCoeff = -(n : ℝ) / 2 := by
  rw [← coeff_natDegree, sliceCoordinatePolynomial_degree n hn, sliceCoordinatePolynomial_coeff_one]

theorem falling_sliceCoordinate_natDegree (n r : ℕ) (hn : 0 < n) :
    ((descPochhammer ℝ r).comp (sliceCoordinatePolynomial n)).natDegree = r := by
  rw [natDegree_comp, descPochhammer_natDegree, sliceCoordinatePolynomial_degree n hn, mul_one]

theorem falling_sliceCoordinate_coeff (n r : ℕ) (hn : 0 < n) :
    ((descPochhammer ℝ r).comp (sliceCoordinatePolynomial n)).coeff r = (-(n : ℝ) / 2) ^ r := by
  have hc := coeff_comp_degree_mul_degree (p := descPochhammer ℝ r)
    (q := sliceCoordinatePolynomial n) (by rw [sliceCoordinatePolynomial_degree n hn]; norm_num)
  simpa only [descPochhammer_natDegree, sliceCoordinatePolynomial_degree n hn, mul_one,
    (monic_descPochhammer ℝ r).leadingCoeff, sliceCoordinatePolynomial_leadingCoeff n hn, one_mul]
    using hc

theorem rootSliceFunctional_monomial (n m : ℕ) (ξ ζ : ℂ) (S : Finset (Fin n)) (a : ℝ) :
    rootSliceFunctional n m ξ ζ (booleanMonomial S a) =
      (a / falling n S.card) * rootPolynomialAverage m ξ ζ
        ((descPochhammer ℝ S.card).comp (sliceCoordinatePolynomial n)) := by
  unfold rootSliceFunctional
  simp only [sliceFunctional_monomial, sliceMoment]
  rw [rootPolynomialAverage_apply, ← rootRealAverage_mul]
  congr 1
  funext z
  rw [eval_comp, sliceCoordinatePolynomial_eval, ← falling_eq_descPochhammer]
  ring

/-- Signed root quadratures extract the actual top Boolean layer with its complete scalar factor. -/
theorem rootSliceLinearMap_difference {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {ξplus ξminus ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    (hξplus : ξplus ^ m = 1) (hξminus : ξminus ^ m = -1)
    (f : BooleanPolynomial n) (hf : BooleanDegreeLE f m) :
    rootSliceLinearMap n m ξplus ζ f - rootSliceLinearMap n m ξminus ζ f =
      ((2 / (2 : ℝ) ^ (m - 1)) * (-(n : ℝ) / 2) ^ m / falling n m) *
        layerCoefficientSum n m f := by
  classical
  let D := rootSliceLinearMap n m ξplus ζ - rootSliceLinearMap n m ξminus ζ
  have hmono (S : Finset (Fin n)) (a : ℝ) (hS : S.card ≤ m) :
      D (booleanMonomial S a) =
        ((2 / (2 : ℝ) ^ (m - 1)) * (-(n : ℝ) / 2) ^ m / falling n m) *
          layerCoefficientSum n m (booleanMonomial S a) := by
    change rootSliceFunctional n m ξplus ζ (booleanMonomial S a) -
      rootSliceFunctional n m ξminus ζ (booleanMonomial S a) = _
    rw [rootSliceFunctional_monomial, rootSliceFunctional_monomial, ← mul_sub,
      rootPolynomialAverage_difference hm hζ hξplus hξminus _
        (by rw [falling_sliceCoordinate_natDegree n S.card hn]; exact hS),
      layerCoefficientSum_monomial]
    by_cases he : S.card = m
    · rw [he, falling_sliceCoordinate_coeff n m hn, ite_eq_left rfl]
      ring
    · have hz : ((descPochhammer ℝ S.card).comp (sliceCoordinatePolynomial n)).coeff m = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [falling_sliceCoordinate_natDegree n S.card hn]; omega)
      rw [hz, ite_eq_right he]
      ring
  have he : f = ∑ S ∈ f.coeff.support, booleanMonomial S.toFinset (f.coeff S) :=
    (MonoidAlgebra.sum_coeff_single f).symm
  change D f = _
  conv_lhs => rw [he]
  conv_rhs => rw [he]
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  exact hmono S (f.coeff S) (hf S (Finsupp.mem_support_iff.mp hS))

end NoncommutativeAMGM
