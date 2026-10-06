/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Lemmas.Series

/-!
# A001: `Li₂(i) = -π²/48 + iG`

Write `Li₂(i) = ∑_{m ≥ 1} iᵐ/m²` and split by the parity of `m`:
* `m = 2k`: the terms are `(-1)ᵏ/(4k²)`, which sum to `-η(2)/4 = -π²/48`;
* `m = 2k + 1`: the terms are `i · (-1)ᵏ/(2k+1)²`, which sum to `i · G`.

Both parts converge absolutely, since `‖iᵐ/m²‖ = 1/m²`.
-/

open Real

namespace LeanPolyLog.Proofs

/-- A001: `Li₂(i) = -π²/48 + iG`. -/
public theorem A001 : Li 2 Complex.I = ((-π ^ 2 / 48 : ℝ) : ℂ) + (G : ℂ) * Complex.I := by
  -- `h m = iᵐ/m²`, whose `m = 0` term is `1/0 = 0`
  set h : ℕ → ℂ := fun m => Complex.I ^ m / (m : ℂ) ^ 2
  have he : HasSum (fun k => h (2 * k)) ((-π ^ 2 / 48 : ℝ) : ℂ) := by
    rw [← hasSum_nat_add_iff' 1]
    convert Complex.hasSum_ofReal.2 (Series.hasSum_eta_two.mul_left (-1 / 4)) using 1
    · funext j
      simp only [h]
      push_cast
      rw [pow_mul, Complex.I_sq]
      field_simp
      ring
    · simp [h]
      ring
  have ho : HasSum (fun k => h (2 * k + 1)) ((G : ℂ) * Complex.I) := by
    convert (Complex.hasSum_ofReal.2 Series.hasSum_catalan).mul_right Complex.I using 1
    funext k
    simp only [h]
    push_cast
    rw [pow_succ, pow_mul, Complex.I_sq]
    ring
  have hall := he.even_add_odd ho
  rw [← hasSum_nat_add_iff' 1] at hall
  simp only [Finset.range_one, Finset.sum_singleton, h, Nat.cast_zero, pow_zero] at hall
  unfold Li
  convert hall.tsum_eq using 1
  · congr 1
    funext n
    push_cast
    ring
  · simp

end LeanPolyLog.Proofs
