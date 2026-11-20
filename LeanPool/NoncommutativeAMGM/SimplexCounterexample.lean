/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.SimplexEigenvalue
public import LeanPool.NoncommutativeAMGM.MatrixOrder

/-! # An exact seven-matrix counterexample to the unrestricted lower bound -/

@[expose] public section

namespace NoncommutativeAMGM
open Matrix
open scoped BigOperators MatrixOrder

/-- A fully specified instance of the paper's simplex construction. -/
noncomputable def sevenSimplexMatrices : Fin 7 → Matrix (Fin 7) (Fin 7) ℝ :=
  simplexMatrix 7 (simplexAngleAlpha 7 (Real.pi / 6)) (simplexAngleBeta 7 (Real.pi / 6))

/-- The example satisfies the original PSD and mean constraints. -/
theorem sevenSimplexMatrices_admissible : Admissible sevenSimplexMatrices := by
  obtain ⟨hPSD, hsum⟩ := simplexAngle_family (n := 7) (by omega) (Real.pi / 6)
  refine ⟨hPSD, ?_⟩
  change LoewnerLE (∑ i, simplexMatrix 7 _ _ i) _
  rw [hsum]

/-- Its exact axis eigenvalue is `-(49/48)³ < -1`. -/
theorem sevenSimplexMatrices_eigenvector :
    withoutReplacementMean 7 7 sevenSimplexMatrices *ᵥ simplexAxis 7 =
      (-((49 / 48 : ℝ) ^ 3)) • simplexAxis 7 := by
  have h := simplexMean_angle_eigenvector (n := 7) (m := 7) (ℓ := 1)
    (by omega) (by omega) (by omega) (by omega)
  norm_num only [Nat.cast_ofNat, Nat.cast_one, mul_one, one_mul, Nat.reduceSub,
    sub_self, pow_one] at h
  change withoutReplacementMean 7 7 sevenSimplexMatrices *ᵥ simplexAxis 7 = _ at h
  have hp : ((7 / 6 : ℝ) * Real.cos (Real.pi / 6)) ^ 6 = (49 / 48 : ℝ) ^ 3 := by
    calc
      _ = ((7 / 6 : ℝ) ^ 2 * Real.cos (Real.pi / 6) ^ 2) ^ 3 := by norm_num; ring
      _ = _ := by rw [Real.sq_cos_pi_div_six]; norm_num
  simpa only [show (7 : ℝ) - 1 = 6 by norm_num, hp, neg_one_mul] using h

/-- The original unrestricted noncommutative AM-GM lower bound fails in dimension seven. -/
theorem sevenSimplexMatrices_lower_bound_fails :
    ¬ (-(1 : Matrix (Fin 7) (Fin 7) ℝ) ≤
      withoutReplacementMean 7 7 sevenSimplexMatrices) := by
  intro h
  have hPSD : (withoutReplacementMean 7 7 sevenSimplexMatrices + 1).PosSemidef := by
    simpa only [Matrix.le_iff, sub_neg_eq_add] using h
  have hp := hPSD.dotProduct_mulVec_nonneg (simplexAxis 7)
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, sevenSimplexMatrices_eigenvector,
    dotProduct_add, dotProduct_smul, simplexAxis_dot_self (by omega : 0 < 7),
    star_trivial, smul_eq_mul, mul_one] at hp
  norm_num at hp

end NoncommutativeAMGM
