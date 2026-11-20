/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.ParityCoefficients

/-!
# Iterating multiplication by `X²-1`

The family of polynomials `Pⱼ` in Section 3.5, with the original Laurent input
absorbed into a single polynomial `R`. Only its degree bound is used here.
-/

@[expose] public section

namespace NoncommutativeAMGM

open Polynomial

/-- Multiplying a bounded-degree polynomial by `(X-1)ʲ` places it in the shifted-power tail. -/
theorem shift_pow_mul_mem_powerTail {M j : ℕ} (q : Polynomial ℝ) (hq : q.degree < M) :
    (X - 1 : Polynomial ℝ) ^ j * q ∈ powerTail (M + j) j := by
  have hmem : q ∈ powerTail M 0 := by
    rw [powerTail_zero_eq_degreeLT, mem_degreeLT]
    exact hq
  clear hq
  induction hmem using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨l, _, hlM, rfl⟩ := hq
    rw [← pow_add]
    exact power_mem_powerTail (by omega) (by omega)
  | zero => simp
  | add p q _ _ hp hq => simpa [mul_add] using (powerTail (M + j) j).add_mem hp hq
  | smul r p _ hp => simpa [mul_smul_comm] using (powerTail (M + j) j).smul_mem r hp

/-- The polynomial family obtained by successive square differences. -/
noncomputable def differenceFamily (R : Polynomial ℝ) (j : ℕ) : Polynomial ℝ :=
  R * (X ^ 2 - 1) ^ j

theorem differenceFamily_step (R : Polynomial ℝ) (j : ℕ) :
    differenceFamily R (j + 1) = differenceFamily R j * (X ^ 2 - 1) := by
  simp [differenceFamily, pow_succ, mul_assoc]

theorem evenCoefficients_differenceFamily (R : Polynomial ℝ) (j : ℕ) :
    evenCoefficients (differenceFamily R j) = evenCoefficients R * (X - 1) ^ j := by
  induction j with
  | zero => simp [differenceFamily]
  | succ j ih => rw [differenceFamily_step, evenCoefficients_mul_step, ih, pow_succ, mul_assoc]

theorem oddCoefficients_differenceFamily (R : Polynomial ℝ) (j : ℕ) :
    oddCoefficients (differenceFamily R j) = oddCoefficients R * (X - 1) ^ j := by
  induction j with
  | zero => simp [differenceFamily]
  | succ j ih => rw [differenceFamily_step, oddCoefficients_mul_step, ih, pow_succ, mul_assoc]

theorem differenceFamily_natDegree_le {R : Polynomial ℝ} {h : ℕ}
    (hR : R.natDegree ≤ 2 * h) (j : ℕ) :
    (differenceFamily R j).natDegree ≤ 2 * (h + j) := by
  have hbase : (X ^ 2 - 1 : Polynomial ℝ).natDegree = 2 := by
    rw [show (X ^ 2 - 1 : Polynomial ℝ) = X ^ 2 - C (1 : ℝ) by simp,
      natDegree_X_pow_sub_C]
  have hmul : (R * (X ^ 2 - 1) ^ j).natDegree ≤
      R.natDegree + ((X ^ 2 - 1 : Polynomial ℝ) ^ j).natDegree := natDegree_mul_le
  rw [natDegree_pow, hbase] at hmul
  exact hmul.trans (by omega)

theorem differenceFamily_degree_lt {R : Polynomial ℝ} {h : ℕ}
    (hR : R.natDegree ≤ 2 * h) (j : ℕ) :
    (differenceFamily R j).degree < (2 * (h + j) + 1 : ℕ) := by
  apply lt_of_le_of_lt degree_le_natDegree
  exact_mod_cast (Nat.lt_succ_of_le (differenceFamily_natDegree_le hR j))

theorem even_differenceFamily_mem_tail {R : Polynomial ℝ} {h : ℕ}
    (hR : R.natDegree ≤ 2 * h) (j : ℕ) :
    evenCoefficients (differenceFamily R j) ∈ powerTail (h + j + 1) j := by
  have hdeg : R.degree < (2 * h + 1 : ℕ) := by
    apply lt_of_le_of_lt degree_le_natDegree
    exact_mod_cast (Nat.lt_succ_of_le hR)
  have hmem := shift_pow_mul_mem_powerTail (j := j) _ (evenCoefficients_degree_lt hdeg)
  rw [show h + 1 + j = h + j + 1 by omega] at hmem
  rw [evenCoefficients_differenceFamily, mul_comm]
  exact hmem

theorem odd_differenceFamily_mem_tail {R : Polynomial ℝ} {h : ℕ}
    (hR : R.natDegree ≤ 2 * h) (j : ℕ) :
    oddCoefficients (differenceFamily R j) ∈ powerTail (h + j) j := by
  have hdeg : R.degree < (2 * h + 1 : ℕ) := by
    apply lt_of_le_of_lt degree_le_natDegree
    exact_mod_cast (Nat.lt_succ_of_le hR)
  have hmem := shift_pow_mul_mem_powerTail (j := j) _ (oddCoefficients_degree_lt hdeg)
  rw [oddCoefficients_differenceFamily, mul_comm]
  exact hmem

theorem interiorCoefficientNormSq_nonneg (L : ℕ) (p : Polynomial ℝ) :
    0 ≤ interiorCoefficientNormSq L p := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> positivity

/-- The parity-combined norm estimate in equation (39), before the `4⁻ʲ` rescaling. -/
theorem differenceFamily_norm_step {R : Polynomial ℝ} {h j : ℕ}
    (hR : R.natDegree ≤ 2 * h) :
    ((j : ℝ) * ((j : ℝ) + 1)) * realCoefficientInner (differenceFamily R j)
        (differenceFamily R j) ≤
      (((h + j + 1 : ℕ) : ℝ) ^ 2 / 4) *
        twoInteriorCoefficientNormSq (h + j + 1) (differenceFamily R (j + 1)) := by
  have hA := coefficient_norm_step_padded (j := j) (L := h + j + 1) (by omega)
    _ (even_differenceFamily_mem_tail hR j)
  have heven : (X - 1 : Polynomial ℝ) * evenCoefficients (differenceFamily R j) =
      evenCoefficients (differenceFamily R (j + 1)) := by
    rw [differenceFamily_step, evenCoefficients_mul_step, mul_comm]
  rw [heven] at hA
  have hB : ((j : ℝ) * ((j : ℝ) + 1)) *
      realCoefficientInner (oddCoefficients (differenceFamily R j))
        (oddCoefficients (differenceFamily R j)) ≤
      (((h + j + 1 : ℕ) : ℝ) ^ 2 / 4) *
        interiorCoefficientNormSq (h + j) (oddCoefficients (differenceFamily R (j + 1))) := by
    by_cases hh : h = 0
    · have hodd : oddCoefficients R = 0 := by
        have hdeg : R.degree < (2 * h + 1 : ℕ) := by
          apply lt_of_le_of_lt degree_le_natDegree
          exact_mod_cast (Nat.lt_succ_of_le hR)
        have hd := oddCoefficients_degree_lt hdeg
        rw [hh] at hd
        ext i
        exact (degree_lt_iff_coeff_zero _ _).mp hd i (by omega)
      simp [oddCoefficients_differenceFamily, hodd, realCoefficientInner,
        interiorCoefficientNormSq]
    · have hb := coefficient_norm_step_padded (j := j) (L := h + j) (by omega)
        _ (odd_differenceFamily_mem_tail hR j)
      have hodd : (X - 1 : Polynomial ℝ) * oddCoefficients (differenceFamily R j) =
          oddCoefficients (differenceFamily R (j + 1)) := by
        rw [differenceFamily_step, oddCoefficients_mul_step, mul_comm]
      rw [hodd] at hb
      apply hb.trans
      apply mul_le_mul_of_nonneg_right _ (interiorCoefficientNormSq_nonneg _ _)
      push_cast
      nlinarith [show (0 : ℝ) ≤ h by positivity, show (0 : ℝ) ≤ j by positivity]
  rw [realCoefficientNorm_parity (differenceFamily_degree_lt hR j),
    twoInteriorCoefficientNormSq_parity _ (by omega), show h + j + 1 - 1 = h + j by omega]
  nlinarith [hA, hB]

end NoncommutativeAMGM
