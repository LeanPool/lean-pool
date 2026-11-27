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

These are the full six-index geometric sum, the full cubic-geometric
series, and the uniform exponential envelope used in the forward and
reverse spatial arguments. They are scalar estimates only; no weighted
source moment or kernel coefficient bound is assumed or concluded.
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

theorem hasSum_cubic_geometric_fiftyTwo :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ n) 52 := by
  have hn : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have h1 : HasSum (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) 2 := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one hn using 1; norm_num
  have h2 : HasSum (fun n : ℕ => (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ n) 6 := by
    convert hasSum_sq_mul_geometric_of_norm_lt_one hn using 1; norm_num
  have h3 : HasSum (fun n : ℕ => (n : ℝ) ^ 3 * (1 / 2 : ℝ) ^ n) 26 := by
    convert hasSum_pow_mul_geometric_of_norm_lt_one 3 hn using 1
    norm_num [Finset.sum_range_succ, Nat.stirlingSecond]
  convert ((h3.add (h2.mul_left 3)).add (h1.mul_left 3)).add hasSum_geometric_two using 1
  · funext n
    ring
  · norm_num

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
