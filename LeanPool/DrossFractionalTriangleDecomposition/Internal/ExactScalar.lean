/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.CutDensity
import Mathlib.Tactic.Linarith

/-!
# Exact-threshold scalar contradiction

This is the final scalar step for the exact 9/10 cut argument.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

public theorem dross_3_4_to_false_exact (n m k cc wΔ T_A T_B δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10) (hcc : 0 < cc)
    (hccrel : 2 * wΔ = cc * (3 * n * (1 - δ) - 3))
    (hn : 20 ≤ n)
    (hTA1 : (1 - 2 * δ) * n ≤ T_A) (hTA2 : T_A ≤ n)
    (hTB1 : (1 - 2 * δ) * n ≤ T_B)
    (mbound : 2 * m ≤ (1 - δ + 2 * δ ^ 2) * n ^ 2 + 4 + n - 6 * δ * n)
    (ineq3 : cc * (T_A * (T_A - δ * n) / 2 - k) < T_A * wΔ - 1)
    (ineq4 : cc * (T_B * (T_B - δ * n) / 2 - (m - k)) < 1 - T_B * wΔ) :
    False := by
  have hnpos : (0:ℝ) ≤ n := by linarith
  have hδn_le : δ * n ≤ n / 10 := by
    have := mul_le_mul_of_nonneg_right hδ1 hnpos; linarith
  have hn3 : 3 < (1 - 2 * δ) * n := by nlinarith
  have hAleft : 0 ≤ n - T_A := by linarith
  have hAright : 0 ≤ 2 * (1 - δ) * n - 3 - T_A := by nlinarith
  have hAprod : 0 ≤ (n - T_A) * (2 * (1 - δ) * n - 3 - T_A) := mul_nonneg hAleft hAright
  have hBleft : 0 ≤ T_B - (1 - 2 * δ) * n := by linarith
  have hBright : 0 ≤ T_B + (4 - 6 * δ) * n - 3 := by nlinarith
  have hBprod : 0 ≤ (T_B - (1 - 2 * δ) * n) * (T_B + (4 - 6 * δ) * n - 3) :=
    mul_nonneg hBleft hBright
  have hsum : cc * ((2 - 12 * δ + 12 * δ^2) * n^2 + 6 * δ * n - 2 * m) < 0 := by
    nlinarith [ineq3, ineq4, hAprod, hBprod]
  have height : (2 - 12 * δ + 12 * δ^2) * n^2 < 2 * m - 6 * δ * n := by
    nlinarith [mul_pos hcc (show 0 < 2 * m - 6 * δ * n - (2 - 12 * δ + 12 * δ^2) * n^2 by
      nlinarith [hsum])]
  have hnd : (0:ℝ) ≤ n * (1 - δ) - 1.2 := by nlinarith [hδn_le, hn]
  have h10δ : (0:ℝ) ≤ 1 - 10 * δ := by linarith
  have hfac : (0:ℝ) ≤ (1 - 10 * δ) * n * (n * (1 - δ) - 1.2) :=
    mul_nonneg (mul_nonneg h10δ hnpos) hnd
  have hclose : 4 + n - 12 * δ * n ≤ (1 - 11 * δ + 10 * δ^2) * n^2 := by
    nlinarith [hfac, hn]
  nlinarith [height, mbound, hclose]

end LeanPool.DrossFractionalTriangleDecomposition
