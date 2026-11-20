/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.ChebyshevCoefficient
public import LeanPool.NoncommutativeAMGM.ProductScaling
public import LeanPool.NoncommutativeAMGM.CosineRootNodes
public import LeanPool.NoncommutativeAMGM.ChebyshevQuadrature
public import Mathlib.Tactic.Module

/-! # The quadratic-threshold noncommutative AM-GM bound -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix Polynomial Polynomial.Chebyshev
open scoped BigOperators

theorem rootSliceLinearMap_one (n : ℕ) {m : ℕ} (hm : 0 < m) (ξ ζ : ℂ) :
    rootSliceLinearMap n m ξ ζ 1 = 1 := by
  have hs (s : ℝ) : sliceFunctional n s 1 = 1 := by
    rw [← booleanMonomial_empty, sliceFunctional_monomial]
    simp [sliceMoment]
  change rootSliceFunctional n m ξ ζ 1 = 1
  unfold rootSliceFunctional rootRealAverage
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast hm.ne')

/-- Root-slice quadrature preserves the identity matrix for positive quadrature order. -/
theorem rootSliceLinearMap_matrixImage_one {n m : ℕ} {ι : Type*} [DecidableEq ι]
    (hm : 0 < m) (ξ ζ : ℂ) :
    booleanMatrixImage (rootSliceLinearMap n m ξ ζ)
      (1 : Matrix ι ι (BooleanPolynomial n)) = 1 :=
  booleanMatrixImage_one _ (rootSliceLinearMap_one n hm ξ ζ)

/-- The difference of the even and odd root-slice images recovers twice the product mean. -/
theorem cosineRootSlice_mean_difference {n m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin n → Matrix ι ι ℝ) (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) :
    let E : Fin n → Matrix ι ι ℝ := fun a ↦ (n : ℝ)⁻¹ • A a
    let Q := aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ))
    booleanMatrixImage (rootSliceLinearMap n m 1 (cosineRoot m)) Q -
      booleanMatrixImage (rootSliceLinearMap n m (cosineHalfRoot m) (cosineRoot m)) Q =
        (2 : ℝ) • withoutReplacementMean n m A := by
  intro E Q
  have hdifference : booleanMatrixImage (rootSliceLinearMap n m 1 (cosineRoot m)) Q -
      booleanMatrixImage (rootSliceLinearMap n m (cosineHalfRoot m) (cosineRoot m)) Q =
      (2 * (n : ℝ) ^ m / falling n m) • distinctProductSum n m E :=
    rootSlice_chebyshev_difference E hn hm (cosineRoot_primitive hm)
      (one_pow m) (cosineHalfRoot_pow hm)
  rw [hdifference, mul_div_assoc, ← smul_smul, normalized_distinctProductSum hn hmn A]

/-- Half the difference of two matrices between `-I` and `I` obeys the same bounds. -/
theorem loewner_bounds_of_two_sided_difference {ι : Type*} [DecidableEq ι]
    {P N M : Matrix ι ι ℝ} (hp : (1 - P).PosSemidef ∧ (1 + P).PosSemidef)
    (hnq : (1 - N).PosSemidef ∧ (1 + N).PosSemidef)
    (hdifference : P - N = (2 : ℝ) • M) :
    LoewnerLE (-1) M ∧ LoewnerLE M 1 := by
  have hlow := (hp.2.add hnq.1).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hupp := (hp.1.add hnq.2).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have helo : (1 / 2 : ℝ) • ((1 + P) + (1 - N)) = 1 + M := by
    calc
      _ = 1 + (1 / 2 : ℝ) • (P - N) := by module
      _ = _ := by rw [hdifference, smul_smul]; norm_num
  have heup : (1 / 2 : ℝ) • ((1 - P) + (1 + N)) = 1 - M := by
    calc
      _ = 1 - (1 / 2 : ℝ) • (P - N) := by module
      _ = _ := by rw [hdifference, smul_smul]; norm_num
  rw [helo] at hlow
  rw [heup] at hupp
  constructor
  · simpa only [Matrix.le_iff, sub_neg_eq_add, add_comm] using hlow
  · exact hupp

/-- Reconstruct the mean bounds from the two positive pairs of root-slice matrix images. -/
theorem cosineRootSlice_mean_bounds_of_posSemidef {n m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Fin n → Matrix ι ι ℝ)
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) :
    let Q := aeval (booleanChebyshevArgument (fun a ↦ (n : ℝ)⁻¹ • A a)) (T ℝ (m : ℤ))
    (booleanMatrixImage (rootSliceLinearMap n m 1 (cosineRoot m)) (1 - Q)).PosSemidef ∧
      (booleanMatrixImage (rootSliceLinearMap n m 1 (cosineRoot m)) (1 + Q)).PosSemidef →
    (booleanMatrixImage (rootSliceLinearMap n m (cosineHalfRoot m) (cosineRoot m))
      (1 - Q)).PosSemidef ∧
      (booleanMatrixImage (rootSliceLinearMap n m (cosineHalfRoot m) (cosineRoot m))
        (1 + Q)).PosSemidef →
    LoewnerLE (-1) (withoutReplacementMean n m A) ∧ LoewnerLE (withoutReplacementMean n m A) 1 := by
  intro Q hp hnq
  have hdifference : booleanMatrixImage (rootSliceLinearMap n m 1 (cosineRoot m)) Q -
      booleanMatrixImage (rootSliceLinearMap n m (cosineHalfRoot m) (cosineRoot m)) Q =
      (2 : ℝ) • withoutReplacementMean n m A := cosineRootSlice_mean_difference A hn hm hmn
  simp only [booleanMatrixImage_add, booleanMatrixImage_sub,
    rootSliceLinearMap_matrixImage_one hm] at hp hnq
  exact loewner_bounds_of_two_sided_difference hp hnq hdifference

/-- Theorem 1.2 for arbitrary real PSD input matrices with sum bounded by `nI`. -/
theorem withoutReplacementMean_quadratic_bounds {n m dim : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : 2 * ((m + 1) / 2) ^ 2 ≤ n)
    (A : Fin n → Matrix (Fin dim) (Fin dim) ℝ) (hA : Admissible A) :
    LoewnerLE (-(1 : Matrix (Fin dim) (Fin dim) ℝ)) (withoutReplacementMean n m A) ∧
      LoewnerLE (withoutReplacementMean n m A) 1 := by
  have hn : 0 < n := by omega
  by_cases hm1 : m = 1
  · subst m
    exact mean_one_bounds hn A hA
  have hm2 : 2 ≤ m := by omega
  let E : Fin n → Matrix (Fin dim) (Fin dim) ℝ := fun a ↦ (n : ℝ)⁻¹ • A a
  obtain ⟨hE, hmean⟩ := admissible_normalized hn A hA
  let ζ := cosineRoot m
  have hζ : IsPrimitiveRoot ζ m := cosineRoot_primitive (by omega)
  let ξ := cosineHalfRoot m
  have hξ : ξ ^ m = -1 := cosineHalfRoot_pow (by omega)
  have hp := rootSlice_chebyshev_posSemidef E hE hmean hn hm2 hnd hζ
    (show (1 : ℂ) ^ m = ((1 : ℝ) : ℂ) by simp) (Or.inl rfl)
  have hnq := rootSlice_chebyshev_posSemidef E hE hmean hn hm2 hnd hζ
    (show ξ ^ m = ((-1 : ℝ) : ℂ) by simpa using hξ) (Or.inr rfl)
  exact cosineRootSlice_mean_bounds_of_posSemidef A hn (by omega) hmn hp hnq

/-- The requested quadratic-bound proposition is established without auxiliary hypotheses. -/
theorem quadraticBoundTarget : QuadraticBoundTarget := by
  intro n m dim hm hmn hnd A hA
  exact withoutReplacementMean_quadratic_bounds hm hmn hnd A hA

end NoncommutativeAMGM
