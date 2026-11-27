/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteProductSeries
import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Literal scalar summation constants in the spatial estimates

The six-index geometric sum and the uniform exponential envelope used
in the forward and reverse spatial arguments.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

theorem hasSum_half_multiIndex (d : ℕ) :
    HasSum (fun k : Fin d → ℕ => (1 / 2 : ℝ) ^ (∑ j, k j)) (2 ^ d : ℝ) := by
  have h := hasSum_fin_product_nonneg d (fun _ n => (1 / 2 : ℝ) ^ n) (fun _ => (2 : ℝ))
    (fun _ _ => by positivity) (fun _ => hasSum_geometric_two)
  simpa only [Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using h

theorem hasSum_six_moment_geometric :
    HasSum (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      (1 / 2 : ℝ) ^ ((∑ j, k.1 j) + ∑ j, k.2 j)) 64 := by
  have h : HasSum (fun k : Fin 3 → ℕ => (1 / 2 : ℝ) ^ (∑ j, k j)) 8 := by
    convert hasSum_half_multiIndex 3 using 1; norm_num
  have hs := h.summable.mul_of_nonneg h.summable (fun _ => by positivity) (fun _ => by positivity)
  have hp := h.mul h hs
  simpa only [← pow_add, show (8 : ℝ) * 8 = 64 by norm_num] using hp

theorem spatial_polynomial_exp_bound {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ 2 * Real.exp (-x / 8) ≤ 256 := by
  have hlin : 1 + x ≤ 16 * Real.exp (x / 16) := by
    nlinarith [Real.add_one_le_exp (x / 16)]
  have hsmall : (1 + x) * Real.exp (-x / 16) ≤ 16 := by
    rw [show -x / 16 = -(x / 16) by ring, Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_iff₀ (Real.exp_pos _)).mpr hlin
  have hnonneg : 0 ≤ (1 + x) * Real.exp (-x / 16) := by positivity
  have hs := pow_le_pow_left₀ hnonneg hsmall 2
  have hexp : Real.exp (-x / 16) ^ 2 = Real.exp (-x / 8) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow, hexp, show (16 : ℝ) ^ 2 = 256 by norm_num] using hs

end VacuumBellSeparation.Gaussian
