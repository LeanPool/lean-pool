/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.InterpolationSliceExtraction
public import LeanPool.NoncommutativeAMGM.IntegerSlices
public import LeanPool.NoncommutativeAMGM.RoundedVariation
public import LeanPool.NoncommutativeAMGM.ChebyshevImage
public import LeanPool.NoncommutativeAMGM.ZeroSlice
public import Mathlib.Tactic.Module

/-! # Theorem 1.1 by the paper's original rounded-node proof -/

@[expose] public section

namespace NoncommutativeAMGM
open Matrix Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- Retaining an identity endpoint improves the lower bound for a signed matrix average. -/
theorem signed_matrix_endpoint_lower {J ι : Type*} [Fintype J]
    [DecidableEq ι] (a : J → ℝ) (M : J → Matrix ι ι ℝ) (j₀ : J)
    (hzero : M j₀ = 1) (ha0 : 0 ≤ a j₀)
    (hM : ∀ j, (1 - M j).PosSemidef ∧ (1 + M j).PosSemidef)
    (b : ℝ) (hb : (∑ j, |a j|) - 2 * a j₀ ≤ b) :
    LoewnerLE ((-b) • 1) (∑ j, a j • M j) := by
  classical
  have hterm (j : J) : (a j • M j + |a j| • (1 : Matrix ι ι ℝ)).PosSemidef := by
    by_cases ha : 0 ≤ a j
    · simpa only [smul_add, abs_of_nonneg ha, add_comm] using (hM j).2.smul ha
    · have h := (hM j).1.smul (show 0 ≤ -a j by linarith)
      have he : (-a j) • (1 - M j) = a j • M j + |a j| • (1 : Matrix ι ι ℝ) := by
        rw [abs_of_neg (lt_of_not_ge ha)]
        module
      rwa [he] at h
  have hsum := Matrix.posSemidef_sum (Finset.univ.erase j₀) (fun j _ ↦ hterm j)
  have hMsum := Finset.sum_erase_add Finset.univ (fun j ↦ a j • M j) (Finset.mem_univ j₀)
  have hasum := Finset.sum_erase_add Finset.univ (fun j ↦ |a j|) (Finset.mem_univ j₀)
  have he : (∑ j ∈ Finset.univ.erase j₀, (a j • M j + |a j| • (1 : Matrix ι ι ℝ))) =
      (∑ j, a j • M j) + ((∑ j, |a j|) - 2 * a j₀) • (1 : Matrix ι ι ℝ) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← hMsum, ← hasum, hzero,
      abs_of_nonneg ha0]
    module
  rw [he] at hsum
  have hslack := Matrix.PosSemidef.one (n := ι) (R := ℝ) |>.smul
    (show 0 ≤ b - ((∑ j, |a j|) - 2 * a j₀) by linarith)
  have h := hsum.add hslack
  have he' : ((∑ j, a j • M j) + ((∑ j, |a j|) - 2 * a j₀) • (1 : Matrix ι ι ℝ)) +
      (b - ((∑ j, |a j|) - 2 * a j₀)) • 1 = (∑ j, a j • M j) + b • 1 := by module
  rw [he'] at h
  simpa only [Matrix.le_iff, neg_smul, sub_neg_eq_add] using h

/-- Section 2's rounded-node proof, using the actual integer slices and weights. -/
theorem withoutReplacementMean_rounded_lower {n m dim : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : 4 * m ^ 2 ≤ n)
    (A : Fin n → Matrix (Fin dim) (Fin dim) ℝ) (hA : Admissible A) :
    LoewnerLE ((-(1 - 1 / (2 * (m : ℝ)))) • 1) (withoutReplacementMean n m A) := by
  have hm0 : 0 < m := by omega
  have hn : 0 < n := by omega
  have hnodes : m ^ 2 < n := by nlinarith [sq_pos_of_pos hm0]
  let E : Fin n → Matrix (Fin dim) (Fin dim) ℝ := fun i ↦ (n : ℝ)⁻¹ • A i
  obtain ⟨hE, hmean⟩ := admissible_normalized hn A hA
  let P := aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ))
  let M := fun j : Fin (m + 1) ↦
    booleanMatrixImage (sliceFunctional n (roundedSliceNode n m j : ℝ)) P
  let a := fun j : Fin (m + 1) ↦ roundedWeight n m j
  have hslice (j : ℕ) : (n : ℝ) / 2 * (1 - roundedCosineNode n m j) =
      (roundedSliceNode n m j : ℝ) := by
    dsimp [roundedCosineNode]
    field_simp
    ring
  have hW : (∑ j, a j • M j) = withoutReplacementMean n m A := by
    have he := interpolationSlice_withoutReplacementMean hn hmn A (roundedCosineNode n m)
      (roundedCosineNode_injOn hm0 hnodes)
    rw [← he]
    apply Matrix.ext
    intro i k
    dsimp only [a, M]
    simp only [Matrix.sum_apply, Matrix.smul_apply, booleanMatrixImage,
      interpolationSliceMap, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ roundedWeight n m j •
      sliceFunctional n (roundedSliceNode n m j : ℝ) (P i k)) (m + 1)]
    apply Finset.sum_congr rfl
    intro j _
    rw [hslice]
    rfl
  have hM : ∀ j, (1 - M j).PosSemidef ∧ (1 + M j).PosSemidef := by
    intro j
    have h := chebyshevImage_posSemidef hm E hE hmean
      (sliceFunctional n (roundedSliceNode n m j : ℝ))
      (fun f _ ↦ sliceFunctional_integer_square_nonneg (roundedSliceNode_le n m j) f)
    have hunit : sliceFunctional n (roundedSliceNode n m j : ℝ) 1 = 1 := by
      rw [← booleanMonomial_empty, sliceFunctional_monomial]
      simp [sliceMoment]
    simpa only [booleanMatrixImage_sub, booleanMatrixImage_add,
      booleanMatrixImage_one _ hunit] using h
  have hzero : M ⟨0, by omega⟩ = 1 := by
    dsimp [M]
    rw [roundedSliceNode_zero, Nat.cast_zero]
    exact zero_slice_chebyshev E m
  have ha : 0 ≤ a ⟨0, by omega⟩ := (roundedWeight_zero_pos hm0 hnd).le
  have hb : (∑ j, |a j|) - 2 * a ⟨0, by omega⟩ ≤ 1 - 1 / (2 * (m : ℝ)) := by
    dsimp only [a]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ |roundedWeight n m j|) (m + 1)]
    exact roundedWeight_variation_saving hm0 hnd
  rw [← hW]
  exact signed_matrix_endpoint_lower a M ⟨0, by omega⟩ hzero ha hM _ hb

end NoncommutativeAMGM
