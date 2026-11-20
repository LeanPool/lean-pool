/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

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
  exact cosineRootSlice_mean_bounds_of_posSemidef A hn hmpos hmn hp hnq

end NoncommutativeAMGM
