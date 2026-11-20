/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.ChebyshevCoefficient
public import LeanPool.NoncommutativeAMGM.ProductScaling
public import LeanPool.NoncommutativeAMGM.CosineRootNodes

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

theorem booleanMatrixImage_one {n : ℕ} {ι : Type*} [DecidableEq ι]
    (L : BooleanPolynomial n →ₗ[ℝ] ℝ) (hL : L 1 = 1) :
    booleanMatrixImage L (1 : Matrix ι ι (BooleanPolynomial n)) = 1 := by
  apply Matrix.ext
  intro i j
  change L ((1 : Matrix ι ι (BooleanPolynomial n)) i j) = (1 : Matrix ι ι ℝ) i j
  simp only [Matrix.one_apply]
  split_ifs <;> simp [hL]

theorem booleanMatrixImage_add {n : ℕ} {ι κ : Type*}
    (L : BooleanPolynomial n →ₗ[ℝ] ℝ) (A B : Matrix ι κ (BooleanPolynomial n)) :
    booleanMatrixImage L (A + B) = booleanMatrixImage L A + booleanMatrixImage L B := by
  apply Matrix.ext
  intro i j
  exact map_add L (A i j) (B i j)

theorem booleanMatrixImage_sub {n : ℕ} {ι κ : Type*}
    (L : BooleanPolynomial n →ₗ[ℝ] ℝ) (A B : Matrix ι κ (BooleanPolynomial n)) :
    booleanMatrixImage L (A - B) = booleanMatrixImage L A - booleanMatrixImage L B := by
  apply Matrix.ext
  intro i j
  exact map_sub L (A i j) (B i j)

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
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m (by omega)
  let ξ := cosineHalfRoot m
  have hξ : ξ ^ m = -1 := cosineHalfRoot_pow (by omega)
  have hp := rootSlice_chebyshev_posSemidef E hE hmean hn hm2 hnd hζ
    (show (1 : ℂ) ^ m = ((1 : ℝ) : ℂ) by simp) (Or.inl rfl)
  have hnq := rootSlice_chebyshev_posSemidef E hE hmean hn hm2 hnd hζ
    (show ξ ^ m = ((-1 : ℝ) : ℂ) by simpa using hξ) (Or.inr rfl)
  let P := booleanMatrixImage (rootSliceLinearMap n m 1 ζ)
    (aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ)))
  let N := booleanMatrixImage (rootSliceLinearMap n m ξ ζ)
    (aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ)))
  have hdifference : P - N = (2 : ℝ) • withoutReplacementMean n m A := by
    have he := rootSlice_chebyshev_difference E hn (by omega) hζ
      (show (1 : ℂ) ^ m = 1 by simp) hξ
    change P - N = _ at he
    rw [he]
    calc
      _ = (2 : ℝ) • (((n : ℝ) ^ m / falling n m) • distinctProductSum n m E) := by
        rw [smul_smul, mul_div_assoc]
      _ = _ := by rw [normalized_distinctProductSum hn hmn A]
  have hPone := booleanMatrixImage_one (ι := Fin dim) (rootSliceLinearMap n m 1 ζ)
    (rootSliceLinearMap_one n (by omega) 1 ζ)
  have hNone := booleanMatrixImage_one (ι := Fin dim) (rootSliceLinearMap n m ξ ζ)
    (rootSliceLinearMap_one n (by omega) ξ ζ)
  simp only [booleanMatrixImage_add, booleanMatrixImage_sub, hPone, hNone] at hp hnq
  change (1 - P).PosSemidef ∧ (1 + P).PosSemidef at hp
  change (1 - N).PosSemidef ∧ (1 + N).PosSemidef at hnq
  have hlow := (hp.2.add hnq.1).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hupp := (hp.1.add hnq.2).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have helo : (1 / 2 : ℝ) • ((1 + P) + (1 - N)) =
      1 + withoutReplacementMean n m A := by
    calc
      _ = 1 + (1 / 2 : ℝ) • (P - N) := by module
      _ = _ := by rw [hdifference, smul_smul]; norm_num
  have heup : (1 / 2 : ℝ) • ((1 - P) + (1 + N)) =
      1 - withoutReplacementMean n m A := by
    calc
      _ = 1 - (1 / 2 : ℝ) • (P - N) := by module
      _ = _ := by rw [hdifference, smul_smul]; norm_num
  rw [helo] at hlow
  rw [heup] at hupp
  constructor
  · simpa only [LoewnerLE, sub_neg_eq_add, add_comm] using hlow
  · exact hupp

/-- The requested quadratic-bound proposition is established without auxiliary hypotheses. -/
theorem quadraticBoundTarget : QuadraticBoundTarget := by
  intro n m dim hm hmn hnd A hA
  exact withoutReplacementMean_quadratic_bounds hm hmn hnd A hA

end NoncommutativeAMGM
