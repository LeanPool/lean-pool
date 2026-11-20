/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.RoundedWeightSigns
public import LeanPool.NoncommutativeAMGM.ChebyshevRounding
public import LeanPool.NoncommutativeAMGM.RoundedEndpoint
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The final total-variation perturbation bound -/

@[expose] public section

namespace NoncommutativeAMGM
open Polynomial
open scoped BigOperators

/-- The weighted absolute Chebyshev error in the proof of Lemma 2.3. -/
noncomputable def roundedErrorMass (n m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), |roundedWeight n m j| *
    |(Chebyshev.T ℝ (m : ℤ)).eval (roundedCosineNode n m j) -
      (Chebyshev.T ℝ (m : ℤ)).eval (chebyshevNode m j)|

/-- Only interior nodes contribute, and their weighted errors have a summable envelope. -/
theorem roundedErrorMass_le {n m : ℕ} (hm : 0 < m) (hn : 4 * m ^ 2 ≤ n) :
    roundedErrorMass n m ≤
      Real.exp (2 * (m : ℝ) ^ 2 / (n : ℝ) * (Real.pi ^ 2 / 3)) *
        (Real.pi ^ 2 / 12) * ((m : ℝ) ^ 3 / (n : ℝ) ^ 2) := by
  classical
  have hn0 : 0 < n := by nlinarith [sq_pos_of_pos hm]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  let E := Real.exp (2 * (m : ℝ) ^ 2 / (n : ℝ) * (Real.pi ^ 2 / 3))
  let C := (1 / (m : ℝ)) * E * ((m : ℝ) ^ 4 / (4 * (n : ℝ) ^ 2))
  let f := fun j : ℕ ↦ |roundedWeight n m j| *
    |(Chebyshev.T ℝ (m : ℤ)).eval (roundedCosineNode n m j) -
      (Chebyshev.T ℝ (m : ℤ)).eval (chebyshevNode m j)|
  have hend : f 0 = 0 ∧ f m = 0 := by
    have hc : chebyshevNode m m = -1 := by
      rw [chebyshevNode, mul_div_cancel_left₀ _ hm'.ne', Real.cos_pi]
    have hc0 : chebyshevNode m 0 = 1 := by simp [chebyshevNode]
    simp only [f, roundedCosineNode_zero, roundedCosineNode_last hn0 hm, hc, hc0,
      sub_self, abs_zero, mul_zero, and_self]
  have hsum : roundedErrorMass n m = ∑ j ∈ Finset.Ioo 0 m, f j := by
    symm
    apply Finset.sum_subset (by intro j hj; simp only [Finset.mem_Ioo] at hj; simp; omega)
    intro j hj hjout
    have hj' := Finset.mem_range.mp hj
    have ho : ¬(0 < j ∧ j < m) := by simpa only [Finset.mem_Ioo] using hjout
    rcases (show j = 0 ∨ j = m by omega) with h | h
    · subst j
      exact hend.1
    · subst j
      exact hend.2
  have hpoint (j : ℕ) (hj : j ∈ Finset.Ioo 0 m) :
      f j ≤ C * (1 / ((min j (m - j) : ℕ) : ℝ) ^ 2) := by
    obtain ⟨hj0, hjm⟩ := Finset.mem_Ioo.mp hj
    have ha := roundedWeight_abs_le hm hn hjm.le
    have habs : |chebyshevWeight m j| = 1 / (m : ℝ) := by
      rw [chebyshevWeight_abs]
      simp [cosineEndpointFactor, hj0.ne', hjm.ne]
    rw [habs] at ha
    have hb := roundedChebyshev_error hm hn hj0 hjm
    calc
      _ ≤ ((1 / (m : ℝ)) * E) *
          ((m : ℝ) ^ 4 / (4 * (n : ℝ) ^ 2 * ((min j (m - j) : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul ha hb (abs_nonneg _) (by dsimp [E]; positivity)
      _ = _ := by
        dsimp [C]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  rw [hsum]
  calc
    _ ≤ ∑ j ∈ Finset.Ioo 0 m, C * (1 / ((min j (m - j) : ℕ) : ℝ) ^ 2) :=
      Finset.sum_le_sum hpoint
    _ = C * ∑ j ∈ Finset.Ioo 0 m, 1 / ((min j (m - j) : ℕ) : ℝ) ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ C * (Real.pi ^ 2 / 3) := mul_le_mul_of_nonneg_left (inverseSquare_endpoint_sum m)
      (by dsimp [C, E]; positivity)
    _ = _ := by
      dsimp [C, E]
      field_simp
      ring

/-- Substitution of `n ≥ 4m²` into the two factors of the error envelope. -/
theorem roundedErrorMass_le_uniform {n m : ℕ} (hm : 0 < m) (hn : 4 * m ^ 2 ≤ n) :
    roundedErrorMass n m ≤ Real.exp (Real.pi ^ 2 / 6) * Real.pi ^ 2 /
      (192 * (m : ℝ)) := by
  have hn0 : 0 < n := by nlinarith [sq_pos_of_pos hm]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnR : 4 * (m : ℝ) ^ 2 ≤ n := by exact_mod_cast hn
  have hratio : (m : ℝ) ^ 2 / (n : ℝ) ≤ 1 / 4 :=
    (div_le_iff₀ hn').mpr (by linarith)
  have hexponent : 2 * (m : ℝ) ^ 2 / (n : ℝ) * (Real.pi ^ 2 / 3) ≤ Real.pi ^ 2 / 6 := by
    have h := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2 * (Real.pi ^ 2 / 3) by positivity)
    convert h using 1 <;> ring
  have hrate : (m : ℝ) ^ 3 / (n : ℝ) ^ 2 ≤ 1 / (16 * (m : ℝ)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hn') (by positivity)).mpr
    have h := mul_self_le_mul_self (show 0 ≤ 4 * (m : ℝ) ^ 2 by positivity) hnR
    convert h using 1 <;> ring
  apply (roundedErrorMass_le hm hn).trans
  calc
    _ ≤ (Real.exp (Real.pi ^ 2 / 6) * (Real.pi ^ 2 / 12)) *
        (1 / (16 * (m : ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexponent) (by positivity))
        hrate (by positivity) (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- A rational certificate for the final numerical constant in Section 2.3. -/
theorem roundedVariation_constant_lt :
    Real.exp (Real.pi ^ 2 / 6) * Real.pi ^ 2 / 192 < (3 / 10 : ℝ) := by
  have hπ : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have he : Real.exp 1 < (11 / 4 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have he2 : Real.exp 2 < (121 / 16 : ℝ) := by
    have hmul : Real.exp 1 * Real.exp 1 < (121 / 16 : ℝ) := by
      nlinarith [sq_nonneg (Real.exp 1 - 11 / 4), Real.exp_pos 1]
    simpa only [← Real.exp_add, show (1 : ℝ) + 1 = 2 by norm_num] using hmul
  have hprod : Real.exp (Real.pi ^ 2 / 6) * Real.exp (2 - Real.pi ^ 2 / 6) = Real.exp 2 := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hlower : (4 / 3 : ℝ) < Real.exp (2 - Real.pi ^ 2 / 6) := by
    linarith [Real.add_one_le_exp (2 - Real.pi ^ 2 / 6)]
  have hE : Real.exp (Real.pi ^ 2 / 6) < (363 / 64 : ℝ) := by
    have h := mul_lt_mul_of_pos_left hlower (Real.exp_pos (Real.pi ^ 2 / 6))
    rw [hprod] at h
    linarith
  have hmul := mul_lt_mul_of_pos_left hπ (Real.exp_pos (Real.pi ^ 2 / 6))
  nlinarith

/-- The strict variation-error bound with the original constant `3/(10m)`. -/
theorem roundedErrorMass_lt {n m : ℕ} (hm : 0 < m) (hn : 4 * m ^ 2 ≤ n) :
    roundedErrorMass n m < 3 / (10 * (m : ℝ)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h := mul_lt_mul_of_pos_right roundedVariation_constant_lt (by positivity : 0 < (m : ℝ)⁻¹)
  have hbound : Real.exp (Real.pi ^ 2 / 6) * Real.pi ^ 2 / (192 * (m : ℝ)) <
      3 / (10 * (m : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h
  exact (roundedErrorMass_le_uniform hm hn).trans_lt hbound

/-- The rounded interpolation-weight saving at the end of the proof of Lemma 2.3,
using the corrected weights in arXiv:2610.04874v2. -/
theorem roundedWeight_variation_saving {n m : ℕ} (hm : 0 < m) (hn : 4 * m ^ 2 ≤ n) :
    (∑ j ∈ Finset.range (m + 1), |roundedWeight n m j|) - 2 * roundedWeight n m 0 ≤
      1 - 1 / (2 * (m : ℝ)) := by
  have hvar := roundedWeight_variation_le hm hn
  change (∑ j ∈ Finset.range (m + 1), |roundedWeight n m j|) - 1 ≤ roundedErrorMass n m at hvar
  have herr := roundedErrorMass_lt hm hn
  have hend := roundedWeight_zero_gt hm hn
  have he : 3 / (10 * (m : ℝ)) - 2 * (2 / (5 * (m : ℝ))) = -(1 / (2 * (m : ℝ))) := by ring
  linarith

end NoncommutativeAMGM
