/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.Dilog

/-!
# A003: `Li₂((√5-1)/2) = π²/10 - log²((1+√5)/2)`

Let `x = (√5 - 1)/2 = 1/φ`, where `φ = (1 + √5)/2`. Then `x² = 1 - x` and `1 + x = 1/x = φ`.
Three dilogarithm identities at `x` give a linear system for `Li₂(x)`, `Li₂(x²)` and `Li₂(-x)`:
* Euler's reflection formula, with `1 - x = x²`: `Li₂(x) + Li₂(x²) = π²/6 - 2 log² x`;
* the duplication formula: `Li₂(x²) = 2 Li₂(x) + 2 Li₂(-x)`;
* Landen's identity, with `x/(1+x) = x²`: `Li₂(-x) + Li₂(x²) = -½ log² x`.

Solving it gives `Li₂(x) = π²/10 - log² x`, and `log² x = log² φ` because `x = 1/φ`.
-/

open Real

namespace LeanPolyLog.Proofs

/-- A003: `Li₂((√5-1)/2) = π²/10 - log²((1+√5)/2)`. -/
public theorem A003 :
    Lir 2 ((Real.sqrt 5 - 1) / 2) = π ^ 2 / 10 - Real.log ((1 + Real.sqrt 5) / 2) ^ 2 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs2 : 2 < Real.sqrt 5 := by nlinarith [Real.sqrt_nonneg 5]
  have hs3 : Real.sqrt 5 < 3 := by nlinarith [Real.sqrt_nonneg 5]
  set x := (Real.sqrt 5 - 1) / 2 with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  have hx1 : x < 1 := by rw [hx]; linarith
  -- `x² = 1 - x` and `φ = 1 + x = x⁻¹`
  have hsq : 1 - x = x ^ 2 := by rw [hx]; linear_combination -h5 / 4
  have hphi : (1 + Real.sqrt 5) / 2 = x⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [hx]; linear_combination h5 / 4)
  have h1x : 1 + x = x⁻¹ := by rw [← hphi, hx]; ring
  -- the three identities
  have hrefl := Dilog.Lir_two_add_Lir_two_one_sub hx0 hx1
  rw [hsq, Real.log_pow] at hrefl
  have hdup := Dilog.Lir_two_sq (abs_le.2 ⟨by linarith, hx1.le⟩)
  have hlanden := Dilog.Lir_two_neg_add_Lir_two_div hx0.le hx1.le
  rw [h1x, div_inv_eq_mul, ← sq, Real.log_inv] at hlanden
  rw [hphi, Real.log_inv]
  push_cast at hrefl
  linear_combination (3 / 5 : ℝ) * hrefl - (1 / 5 : ℝ) * hdup - (2 / 5 : ℝ) * hlanden

end LeanPolyLog.Proofs
