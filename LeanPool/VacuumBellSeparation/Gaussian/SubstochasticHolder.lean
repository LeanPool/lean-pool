/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTraceHolder

/-!
# Extended Holder with substochastic weights

Nonnegative weights with row and column sums at most one give the same
Holder estimate as a doubly stochastic overlap. The proof uses actual
counting-measure Holder and permits arbitrary index types and infinities.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open scoped ENNReal

variable {ι κ : Type*}

theorem ennreal_substochastic_holder (w : ι → κ → ℝ≥0∞)
    (hwrow : ∀ i, ∑' j, w i j ≤ 1) (hwcol : ∀ j, ∑' i, w i j ≤ 1)
    (a : ι → ℝ≥0∞) (b : κ → ℝ≥0∞) {p q : ℝ} (hpq : p.HolderConjugate q) :
    (∑' i, ∑' j, a i * b j * w i j) ≤
      (∑' i, a i ^ p) ^ (1 / p) * (∑' j, b j ^ q) ^ (1 / q) := by
  let f : ι × κ → ℝ≥0∞ := fun ij => a ij.1 * w ij.1 ij.2 ^ (1 / p)
  let g : ι × κ → ℝ≥0∞ := fun ij => b ij.2 * w ij.1 ij.2 ^ (1 / q)
  have hf (i : ι) (j : κ) : f (i, j) ^ p = a i ^ p * w i j := by
    dsimp only [f]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg, ← ENNReal.rpow_mul,
      one_div_mul_cancel hpq.ne_zero, ENNReal.rpow_one]
  have hg (i : ι) (j : κ) : g (i, j) ^ q = b j ^ q * w i j := by
    dsimp only [g]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.nonneg, ← ENNReal.rpow_mul,
      one_div_mul_cancel hpq.symm.ne_zero, ENNReal.rpow_one]
  have hfg (i : ι) (j : κ) : f (i, j) * g (i, j) = a i * b j * w i j := by
    dsimp only [f, g]
    calc
      _ = (a i * b j) * (w i j ^ (1 / p) * w i j ^ (1 / q)) := by ac_rfl
      _ = _ := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ hpq.one_div_nonneg hpq.symm.one_div_nonneg,
          one_div, one_div, hpq.inv_add_inv_eq_one, ENNReal.rpow_one]
  have hfsum : (∑' ij, f ij ^ p) ≤ ∑' i, a i ^ p := by
    rw [tsum_prod']
    simp only [hf, ENNReal.tsum_mul_left]
    exact tsum_le_tsum fun i => by simpa only [mul_one]
      using _root_.mul_le_mul_right (hwrow i) (a i ^ p)
  have hgsum : (∑' ij, g ij ^ q) ≤ ∑' j, b j ^ q := by
    rw [tsum_prod', tsum_comm]
    simp only [hg, ENNReal.tsum_mul_left]
    exact tsum_le_tsum fun j => by simpa only [mul_one]
      using _root_.mul_le_mul_right (hwcol j) (b j ^ q)
  have h := (ennreal_tsum_holder f g hpq).trans
    (mul_le_mul' (ENNReal.rpow_le_rpow hfsum hpq.one_div_nonneg)
      (ENNReal.rpow_le_rpow hgsum hpq.symm.one_div_nonneg))
  rw [tsum_prod'] at h
  simpa only [hfg] using h

end VacuumBellSeparation.Gaussian
