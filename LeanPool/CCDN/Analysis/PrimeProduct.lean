/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Combining local divisibility at distinct primes

Local powers of different primes multiply, and their weighted logarithms give a lower
bound on the logarithm of a positive determinant gcd. Estimating these prime sums uniformly
for curve reductions is a separate part of CCDN Proposition 3.2.6.
-/

@[expose] public section

namespace CCDN

private theorem prime_power_product_dvd (P : Finset ℕ) (e : ℕ → ℕ) (D : ℤ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hdiv : ∀ p ∈ P, (p : ℤ) ^ e p ∣ D) :
    (∏ p ∈ P, (p : ℤ) ^ e p) ∣ D := by
  apply Finset.prod_dvd_of_coprime ?_ hdiv
  intro p hp q hq hpq
  have hcop : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)
  exact hcop.pow

/-- If each prime `p` in the finite set `P` has `p ^ e p` dividing the positive integer `D`,
then `∑ p ∈ P, e p * log p ≤ log D`. -/
theorem sum_log_prime_powers_le_log (P : Finset ℕ) (e : ℕ → ℕ) {D : ℤ}
    (hD : 0 < D) (hP : ∀ p ∈ P, Nat.Prime p)
    (hdiv : ∀ p ∈ P, (p : ℤ) ^ e p ∣ D) :
    (∑ p ∈ P, (e p : ℝ) * Real.log p) ≤ Real.log D := by
  have hle := Int.le_of_dvd hD (prime_power_product_dvd P e D hP hdiv)
  have hleR : (∏ p ∈ P, (p : ℝ) ^ e p) ≤ (D : ℝ) := by exact_mod_cast hle
  have hpR : ∀ p ∈ P, 0 < (p : ℝ) := by
    intro p hp
    exact_mod_cast (hP p hp).pos
  have hpos : 0 < ∏ p ∈ P, (p : ℝ) ^ e p := by
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (hpR p hp) _
  have hlog := Real.log_le_log hpos hleR
  rw [Real.log_prod (fun p hp => (pow_pos (hpR p hp) (e p)).ne')] at hlog
  simpa only [Real.log_pow] using hlog

end CCDN
