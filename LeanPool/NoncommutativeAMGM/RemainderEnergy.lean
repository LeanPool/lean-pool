/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.RemainderSafety
public import LeanPool.NoncommutativeAMGM.SymmetricSums

/-!
# The actual remainder energies and the scalar closing argument

This connects the coefficient estimates to the `Hⱼ` quantities. The symmetric-sum
positivity theorem below assumes no inequalities on `H`: they are proved here
for the explicit polynomial remainders.
-/

@[expose] public section

namespace NoncommutativeAMGM

open Polynomial
open scoped BigOperators

/-- The normalized squared coefficient norm of the remainder defining `Hⱼ`. -/
noncomputable def remainderEnergy (R : Polynomial ℝ) (m : ℕ) (η : ℝ) (j : ℕ) : ℝ :=
  let r := differenceFamily R j %ₘ (X ^ m - C η)
  realCoefficientInner r r / (4 : ℝ) ^ j

theorem realCoefficientInner_self_nonneg (p : Polynomial ℝ) : 0 ≤ realCoefficientInner p p := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg _

theorem remainderEnergy_nonneg (R : Polynomial ℝ) (m : ℕ) (η : ℝ) (j : ℕ) :
    0 ≤ remainderEnergy R m η j :=
  div_nonneg (realCoefficientInner_self_nonneg _) (by positivity)

theorem differenceFamily_remainder_self {R : Polynomial ℝ} {h m j : ℕ}
    (hR : R.natDegree ≤ 2 * h) (hjm : 2 * (h + j) < m) (η : ℝ) :
    differenceFamily R j %ₘ (X ^ m - C η) = differenceFamily R j := by
  apply (modByMonic_eq_self_iff (monic_X_pow_sub_C (n := m) η (by omega))).mpr
  rw [degree_X_pow_sub_C (by omega)]
  apply lt_of_le_of_lt degree_le_natDegree
  exact_mod_cast (lt_of_le_of_lt (differenceFamily_natDegree_le hR j) hjm)

/-- Adjacent remainder energies satisfy the one-step estimate required by (40). -/
theorem remainderEnergy_step_mul {R : Polynomial ℝ} {h m j : ℕ} (hm : 2 ≤ m)
    (hR : R.natDegree ≤ 2 * h) (hjm : 2 * (h + j + 1) ≤ m + 1) (η : ℝ) :
    ((j : ℝ) * ((j : ℝ) + 1)) * remainderEnergy R m η j ≤
      (((h + j + 1 : ℕ) : ℝ) ^ 2) * remainderEnergy R m η (j + 1) := by
  have hraw := differenceFamily_norm_step (j := j) hR
  have hrem := twoInterior_le_remainder_norm_of_le hm hjm
    (differenceFamily_natDegree_le hR (j + 1)) η
  have hbound := hraw.trans (mul_le_mul_of_nonneg_left hrem (by positivity))
  have hdiv := div_le_div_of_nonneg_right hbound (show 0 ≤ (4 : ℝ) ^ j by positivity)
  calc
    _ = (((j : ℝ) * ((j : ℝ) + 1)) *
        realCoefficientInner (differenceFamily R j) (differenceFamily R j)) / (4 : ℝ) ^ j := by
      rw [remainderEnergy, differenceFamily_remainder_self hR (by omega) η]
      ring
    _ ≤ _ := hdiv
    _ = _ := by
      simp only [remainderEnergy, pow_succ]
      ring

theorem remainderEnergy_step {R : Polynomial ℝ} {h m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j)
    (hR : R.natDegree ≤ 2 * h) (hjm : 2 * (h + j + 1) ≤ m + 1) (η : ℝ) :
    remainderEnergy R m η j ≤
      (((h + j + 1 : ℕ) : ℝ) ^ 2 / ((j : ℝ) * ((j : ℝ) + 1))) *
        remainderEnergy R m η (j + 1) := by
  rw [div_mul_eq_mul_div]
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  apply (le_div_iff₀ (mul_pos hjR (by positivity))).mpr
  nlinarith [remainderEnergy_step_mul hm hR hjm η]

/-- The scalar closing argument for the actual polynomial family and remainders.
The only hypotheses concern the input degree and the paper's numerical regime. -/
theorem actual_remainder_expansion_nonneg (R : Polynomial ℝ) (n η : ℝ) (m h k : ℕ)
    (hm : 2 ≤ m) (hk : 1 ≤ k) (hR : R.natDegree ≤ 2 * h)
    (hkm : 2 * (h + k) ≤ m + 1) (hn0 : 0 < n) (hn : 2 * ((h + k : ℕ) : ℝ) ^ 2 ≤ n) :
    0 ≤ remainderEnergy R m η k + ∑ i ∈ Finset.range (k - 1),
      (-1 : ℝ) ^ (i + 1) * symmetricBeta n k (i + 1) *
        remainderEnergy R m η (k - (i + 1)) := by
  apply symmetricBeta_expansion_nonneg n ((h + k : ℕ) : ℝ) k hn0 hk
    (by norm_cast; omega) hn
    (remainderEnergy R m η) (remainderEnergy_nonneg R m η)
  · have hc := remainderEnergy_step_mul (j := k - 1) hm hR (by omega) η
    rw [show k - 1 + 1 = k by omega, show h + (k - 1) + 1 = h + k by omega] at hc
    rw [Nat.cast_sub hk, Nat.cast_one] at hc
    nlinarith [hc]
  · intro l hl hlk
    have hc := remainderEnergy_step (j := k - (l + 1)) hm (by omega) hR (by omega) η
    have hidx : k - (l + 1) + 1 = k - l := by omega
    have hjcast : ((k - (l + 1) : ℕ) : ℝ) = (k : ℝ) - l - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      ring
    have hMcast : ((h + (k - (l + 1)) + 1 : ℕ) : ℝ) = ((h + k : ℕ) : ℝ) - l := by
      have heq : h + (k - (l + 1)) + 1 + l = h + k := by omega
      have hReal : ((h + (k - (l + 1)) + 1 : ℕ) : ℝ) + l = ((h + k : ℕ) : ℝ) := by
        exact_mod_cast heq
      linarith
    rw [hidx, hjcast, hMcast] at hc
    convert hc using 1
    ring

end NoncommutativeAMGM
