/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Matrix.Mul

/-! # Concrete regular-simplex vectors for the counterexample family -/

@[expose] public section

namespace NoncommutativeAMGM
open scoped BigOperators
open Matrix

/-- The centered standard coordinate vectors, before normalization. -/
noncomputable def simplexCentered (n : ℕ) (i : Fin n) : Fin n → ℝ :=
  fun j ↦ (if i = j then 1 else 0) - (n : ℝ)⁻¹

/-- The unit vector in the all-ones direction. -/
noncomputable def simplexAxis (n : ℕ) : Fin n → ℝ := fun _ ↦ (Real.sqrt n)⁻¹

/-- The concrete regular-simplex vectors of equation (2). -/
noncomputable def simplexVector (n : ℕ) (i : Fin n) : Fin n → ℝ :=
  Real.sqrt ((n : ℝ) / (n - 1 : ℝ)) • simplexCentered n i

theorem simplexCentered_sum_coordinates {n : ℕ} (hn : 0 < n) (i : Fin n) :
    ∑ j, simplexCentered n i j = 0 := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp [simplexCentered, Finset.sum_sub_distrib, hn0]

theorem simplexCentered_sum {n : ℕ} (hn : 0 < n) :
    ∑ i, simplexCentered n i = 0 := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  funext j
  simp [simplexCentered, Finset.sum_apply, Finset.sum_sub_distrib, hn0]

theorem simplexCentered_dot {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    simplexCentered n i ⬝ᵥ simplexCentered n j =
      (if i = j then 1 else 0) - (n : ℝ)⁻¹ := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp only [dotProduct, simplexCentered, sub_mul, mul_sub,
    Finset.sum_sub_distrib]
  simp [ite_mul, mul_ite, hn0]

theorem simplexAxis_dot_self {n : ℕ} (hn : 0 < n) :
    simplexAxis n ⬝ᵥ simplexAxis n = 1 := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  simp only [dotProduct, simplexAxis, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)]

theorem simplexAxis_dot_centered {n : ℕ} (hn : 0 < n) (i : Fin n) :
    simplexAxis n ⬝ᵥ simplexCentered n i = 0 := by
  simp only [dotProduct, simplexAxis, ← Finset.mul_sum]
  rw [simplexCentered_sum_coordinates hn, mul_zero]

theorem simplexVector_sum {n : ℕ} (hn : 0 < n) :
    ∑ i, simplexVector n i = 0 := by
  simp only [simplexVector, ← Finset.smul_sum, simplexCentered_sum hn, smul_zero]

theorem simplexAxis_dot_vector {n : ℕ} (hn : 0 < n) (i : Fin n) :
    simplexAxis n ⬝ᵥ simplexVector n i = 0 := by
  rw [simplexVector, dotProduct_smul, simplexAxis_dot_centered hn, smul_zero]

theorem simplexVector_dot {n : ℕ} (hn : 1 < n) (i j : Fin n) :
    simplexVector n i ⬝ᵥ simplexVector n j =
      if i = j then 1 else -((n : ℝ) - 1)⁻¹ := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hd : (n : ℝ) - 1 ≠ 0 := by linarith
  have hs := Real.sq_sqrt (show 0 ≤ (n : ℝ) / (n - 1 : ℝ) by positivity)
  rw [simplexVector, simplexVector, smul_dotProduct, dotProduct_smul,
    simplexCentered_dot (by omega)]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← pow_two, hs]
  split_ifs <;> field_simp
  all_goals ring

/-- The simplex vectors give the tight frame on the orthogonal complement of the axis. -/
theorem simplexVector_frame {n : ℕ} (hn : 1 < n) :
    ∑ i, vecMulVec (simplexVector n i) (simplexVector n i) =
      ((n : ℝ) / (n - 1 : ℝ)) •
        (1 - vecMulVec (simplexAxis n) (simplexAxis n)) := by
  classical
  have hs := Real.sq_sqrt (show 0 ≤ (n : ℝ) / (n - 1 : ℝ) by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    positivity)
  have hsq : (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ))⁻¹ = (n : ℝ)⁻¹ := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (by positivity)]
  apply Matrix.ext
  intro j k
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  have hsym (i j : Fin n) : simplexCentered n i j = simplexCentered n j i := by
    simp only [simplexCentered, eq_comm]
  simp only [simplexVector, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ i, Real.sqrt ((n : ℝ) / (n - 1 : ℝ)) * simplexCentered n i j *
      (Real.sqrt ((n : ℝ) / (n - 1 : ℝ)) * simplexCentered n i k) =
      ((n : ℝ) / (n - 1 : ℝ)) *
        (simplexCentered n j i * simplexCentered n k i) by
    intro i
    rw [hsym i j, hsym i k]
    calc
      _ = (Real.sqrt ((n : ℝ) / (n - 1 : ℝ))) ^ 2 *
          (simplexCentered n j i * simplexCentered n k i) := by ring
      _ = _ := by rw [hs]]
  rw [← Finset.mul_sum]
  change ((n : ℝ) / (n - 1 : ℝ)) *
      (simplexCentered n j ⬝ᵥ simplexCentered n k) = _
  rw [simplexCentered_dot (by omega)]
  simp only [simplexAxis, Matrix.one_apply, hsq]

end NoncommutativeAMGM
