/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.EndpointChebyshev
public import LeanPool.NoncommutativeAMGM.QuadraticBound

/-! # A strict lower bound from the retained endpoint, and Theorem 1.1 -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- Retaining the endpoint gives the stronger lower bound `-1+1/m` at the quadratic threshold. -/
theorem withoutReplacementMean_endpoint_lower {n m dim : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : 2 * ((m + 1) / 2) ^ 2 ≤ n)
    (A : Fin n → Matrix (Fin dim) (Fin dim) ℝ) (hA : Admissible A) :
    LoewnerLE ((-(1 - 1 / (m : ℝ))) • 1) (withoutReplacementMean n m A) := by
  have hn : 0 < n := by omega
  by_cases hm1 : m = 1
  · subst m
    simpa [Matrix.nonneg_iff_posSemidef] using mean_one_posSemidef hn A hA.1
  have hm2 : 2 ≤ m := by omega
  let E : Fin n → Matrix (Fin dim) (Fin dim) ℝ := fun a ↦ (n : ℝ)⁻¹ • A a
  obtain ⟨hE, hmean⟩ := admissible_normalized hn A hA
  let ζ := cosineRoot m
  have hζ : IsPrimitiveRoot ζ m := cosineRoot_primitive (by omega)
  let ξ := cosineHalfRoot m
  have hξ : ξ ^ m = -1 := cosineHalfRoot_pow (by omega)
  have hp := rootSlice_chebyshev_plus_endpoint E hE hmean hn hm2 hnd hζ
  have hnq := (rootSlice_chebyshev_posSemidef E hE hmean hn hm2 hnd hζ
    (show ξ ^ m = ((-1 : ℝ) : ℂ) by simpa using hξ) (Or.inr rfl)).1
  let P := booleanMatrixImage (rootSliceLinearMap n m 1 ζ)
    (aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ)))
  let N := booleanMatrixImage (rootSliceLinearMap n m ξ ζ)
    (aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ)))
  have hdifference : P - N = (2 : ℝ) • withoutReplacementMean n m A :=
    cosineRootSlice_mean_difference A hn (by omega) hmn
  have hmpos : 0 < m := by omega
  simp only [booleanMatrixImage_add, rootSliceLinearMap_matrixImage_one hmpos] at hp
  simp only [booleanMatrixImage_sub, rootSliceLinearMap_matrixImage_one hmpos] at hnq
  change ((1 + P) - (2 / (m : ℝ)) • 1).PosSemidef at hp
  change (1 - N).PosSemidef at hnq
  have hpos := (hp.add hnq).smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have he : (1 / 2 : ℝ) • (((1 + P) - (2 / (m : ℝ)) • 1) + (1 - N)) =
      withoutReplacementMean n m A + (1 - 1 / (m : ℝ)) • 1 := by
    calc
      _ = 1 + (1 / 2 : ℝ) • (P - N) - (1 / (m : ℝ)) • 1 := by module
      _ = _ := by rw [hdifference, smul_smul]; module
  rw [he] at hpos
  simpa only [Matrix.le_iff, neg_smul, sub_neg_eq_add] using hpos

/-- Theorem 1.1 with the paper's stated `4m²` threshold and `1/(2m)` saving. -/
theorem withoutReplacementMean_strengthened_lower {n m dim : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : 4 * m ^ 2 ≤ n)
    (A : Fin n → Matrix (Fin dim) (Fin dim) ℝ) (hA : Admissible A) :
    LoewnerLE ((-(1 - 1 / (2 * (m : ℝ)))) • 1) (withoutReplacementMean n m A) := by
  have hδ : (m + 1) / 2 ≤ m := by omega
  have hquad : 2 * ((m + 1) / 2) ^ 2 ≤ n := by
    have hsq := Nat.mul_self_le_mul_self hδ
    nlinarith
  have hlower := withoutReplacementMean_endpoint_lower hm hmn hquad A hA
  apply loewner_trans _ hlower
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hcoeff : 0 ≤ (1 / (m : ℝ)) - 1 / (2 * (m : ℝ)) := by
    have he : (1 / (m : ℝ)) - 1 / (2 * (m : ℝ)) = 1 / (2 * (m : ℝ)) := by field_simp; ring
    rw [he]
    positivity
  have hpsd := (Matrix.PosSemidef.one (n := Fin dim) (R := ℝ)).smul hcoeff
  have he : 1 - 1 / (2 * (m : ℝ)) - (1 - 1 / (m : ℝ)) =
      1 / (m : ℝ) - 1 / (2 * (m : ℝ)) := by ring
  simpa only [Matrix.le_iff, ← sub_smul, neg_sub_neg, he] using hpsd

/-- The full strengthened-lower-bound proposition, with no unconstructed interfaces. -/
theorem lowerBoundTarget : LowerBoundTarget := by
  intro n m dim hm hmn hnd A hA
  exact withoutReplacementMean_strengthened_lower hm hmn hnd A hA

end NoncommutativeAMGM
