/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.RemainderEnergy

/-! # The all-length falling-factorial remainder estimate in equation (40) -/

@[expose] public section
namespace NoncommutativeAMGM
open Polynomial
open scoped BigOperators

/-- Product of the adjacent energy ratios when descending from level `k`. -/
noncomputable def cumulativeEnergyFactor (d : ℝ) (k j : ℕ) : ℝ :=
  ∏ l ∈ Finset.range j, (d - l) ^ 2 / (((k : ℝ) - l) * ((k : ℝ) - 1 - l))

theorem cumulativeEnergyFactor_eq_falling (d : ℝ) (k j : ℕ) :
    cumulativeEnergyFactor d k j =
      falling d j ^ 2 / (falling (k : ℝ) j * falling ((k : ℝ) - 1) j) := by
  rw [cumulativeEnergyFactor, Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow]
  rfl

theorem cumulativeEnergyFactor_succ (d : ℝ) (k j : ℕ) :
    cumulativeEnergyFactor d k (j + 1) = cumulativeEnergyFactor d k j *
      ((d - j) ^ 2 / (((k : ℝ) - j) * ((k : ℝ) - 1 - j))) := by
  exact Finset.prod_range_succ _ _

theorem remainderEnergy_iterated_product {R : Polynomial ℝ} {h m k : ℕ}
    (hm : 2 ≤ m) (hk : 1 ≤ k) (hR : R.natDegree ≤ 2 * h)
    (hkm : 2 * (h + k) ≤ m + 1) (η : ℝ) (j : ℕ) (hjk : j ≤ k - 1) :
    remainderEnergy R m η (k - j) ≤
      cumulativeEnergyFactor ((h + k : ℕ) : ℝ) k j * remainderEnergy R m η k := by
  induction j with
  | zero => simp [cumulativeEnergyFactor]
  | succ j ih =>
    have hj : j ≤ k - 1 := by omega
    have hstep := remainderEnergy_step (j := k - (j + 1)) hm (by omega) hR (by omega) η
    have hidx : k - (j + 1) + 1 = k - j := by omega
    have hden : ((k - (j + 1) : ℕ) : ℝ) = (k : ℝ) - 1 - j := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      ring
    have hnum : ((h + (k - (j + 1)) + 1 : ℕ) : ℝ) = ((h + k : ℕ) : ℝ) - j := by
      have he : h + (k - (j + 1)) + 1 + j = h + k := by omega
      have heR : ((h + (k - (j + 1)) + 1 : ℕ) : ℝ) + j = ((h + k : ℕ) : ℝ) := by
        exact_mod_cast he
      linarith
    rw [hidx, hden, hnum] at hstep
    have hkR : (j : ℝ) + 1 < k := by exact_mod_cast (show j + 1 < k by omega)
    have hfac : 0 ≤ (((h + k : ℕ) : ℝ) - j) ^ 2 /
        (((k : ℝ) - 1 - j) * ((k : ℝ) - 1 - j + 1)) := by
      have h1 : 0 < (k : ℝ) - 1 - j := by linarith
      have h2 : 0 < (k : ℝ) - 1 - j + 1 := by linarith
      exact div_nonneg (sq_nonneg _) (mul_nonneg h1.le h2.le)
    have hbound := hstep.trans (mul_le_mul_of_nonneg_left (ih hj) hfac)
    rw [cumulativeEnergyFactor_succ]
    convert hbound using 1; ring

/-- The first estimate in equation (40), for the actual constructed remainder energies. -/
theorem remainderEnergy_iterated {R : Polynomial ℝ} {h m k : ℕ}
    (hm : 2 ≤ m) (hk : 1 ≤ k) (hR : R.natDegree ≤ 2 * h)
    (hkm : 2 * (h + k) ≤ m + 1) (η : ℝ) (j : ℕ) (hjk : j ≤ k - 1) :
    remainderEnergy R m η (k - j) ≤
      (falling ((h + k : ℕ) : ℝ) j ^ 2 /
        (falling (k : ℝ) j * falling ((k : ℝ) - 1) j)) * remainderEnergy R m η k := by
  simpa only [cumulativeEnergyFactor_eq_falling] using
    remainderEnergy_iterated_product hm hk hR hkm η j hjk

end NoncommutativeAMGM
