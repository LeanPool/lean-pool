/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.CosineSlicePositivity
public import LeanPool.NoncommutativeAMGM.ChebyshevImage
public import LeanPool.NoncommutativeAMGM.QuadraticBound

/-! # Theorem 3.5: the sine-node threshold for the two-sided matrix bound -/

@[expose] public section
namespace NoncommutativeAMGM
open Matrix Polynomial Polynomial.Chebyshev

/-- Theorem 3.5 with its original sine-node condition, for arbitrary admissible PSD matrices. -/
theorem withoutReplacementMean_sine_bounds {n m dim : ℕ}
    (hm : 1 ≤ m) (hdn : 2 * ((m + 1) / 2) ≤ n)
    (hsin : (((m + 1) / 2 : ℕ) : ℝ) - 1 ≤
      (n : ℝ) * Real.sin (Real.pi / (2 * (m : ℝ))) ^ 2)
    (A : Fin n → Matrix (Fin dim) (Fin dim) ℝ) (hA : Admissible A) :
    LoewnerLE (-(1 : Matrix (Fin dim) (Fin dim) ℝ)) (withoutReplacementMean n m A) ∧
      LoewnerLE (withoutReplacementMean n m A) 1 := by
  have hmpos : 0 < m := by omega
  have hn : 0 < n := by omega
  have hmn : m ≤ n := by omega
  let E : Fin n → Matrix (Fin dim) (Fin dim) ℝ := fun a ↦ (n : ℝ)⁻¹ • A a
  obtain ⟨hE, hmean⟩ := admissible_normalized hn A hA
  have hp := chebyshevImage_posSemidef hm E hE hmean
    (rootSliceLinearMap n m 1 (cosineRoot m))
    (fun f hf ↦ (cosineRootSlice_square_nonneg hmpos hn hdn hsin f hf).1)
  have hnq := chebyshevImage_posSemidef hm E hE hmean
    (rootSliceLinearMap n m (cosineHalfRoot m) (cosineRoot m))
    (fun f hf ↦ (cosineRootSlice_square_nonneg hmpos hn hdn hsin f hf).2)
  let P := booleanMatrixImage (rootSliceLinearMap n m 1 (cosineRoot m))
    (aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ)))
  let N := booleanMatrixImage (rootSliceLinearMap n m (cosineHalfRoot m) (cosineRoot m))
    (aeval (booleanChebyshevArgument E) (T ℝ (m : ℤ)))
  have hdifference : P - N = (2 : ℝ) • withoutReplacementMean n m A := by
    have he := rootSlice_chebyshev_difference E hn hmpos (cosineRoot_primitive hmpos)
      (show (1 : ℂ) ^ m = 1 by simp) (cosineHalfRoot_pow hmpos)
    change P - N = _ at he
    rw [he]
    calc
      _ = (2 : ℝ) • (((n : ℝ) ^ m / falling n m) • distinctProductSum n m E) := by
        rw [smul_smul, mul_div_assoc]
      _ = _ := by rw [normalized_distinctProductSum hn hmn A]
  have hPone := booleanMatrixImage_one (ι := Fin dim) (rootSliceLinearMap n m 1 (cosineRoot m))
    (rootSliceLinearMap_one n hmpos 1 (cosineRoot m))
  have hNone := booleanMatrixImage_one (ι := Fin dim)
    (rootSliceLinearMap n m (cosineHalfRoot m) (cosineRoot m))
    (rootSliceLinearMap_one n hmpos (cosineHalfRoot m) (cosineRoot m))
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

end NoncommutativeAMGM
