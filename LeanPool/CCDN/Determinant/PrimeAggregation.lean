/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Analysis.PrimeCutoff
public import LeanPool.CCDN.Plane.FiniteFieldConstants
import LeanPool.CCDN.Analysis.PrimeProduct

/-! Simultaneous prime divisibility with arbitrary main and error coefficients.

`general_determinant_log_lower_cutoff_congruence` multiplies the local prime-power divisors
of an integer `D` at the good primes up to `x`, together with prescribed divisors at a set
`P` of excluded primes, and bounds `log D` from below. `determinant_log_lower_of_local_divisors`
packages this for a local divisor oracle (for each good prime an exponent with the required
lower bound) and absorbs the square-root error above a cutoff `L ≥ d ^ 4`;
`determinant_log_lower_of_local_divisors_degree_four` is the case `L = 27 d ^ 4`. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real

private lemma sum_log_disjoint_prime_powers_le_log (P Q : Finset ℕ)
    (hPQ : Disjoint P Q) (e v : ℕ → ℕ) {D : ℤ} (hD : 0 < D)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (hdivP : ∀ p ∈ P, (p : ℤ) ^ e p ∣ D)
    (hdivQ : ∀ p ∈ Q, (p : ℤ) ^ v p ∣ D) :
    (∑ p ∈ P, (e p : ℝ) * Real.log p) +
      (∑ p ∈ Q, (v p : ℝ) * Real.log p) ≤ Real.log D := by
  classical
  let w : ℕ → ℕ := fun p => if p ∈ P then e p else v p
  have hw (p : ℕ) (hp : p ∈ P ∪ Q) : (p : ℤ) ^ w p ∣ D := by
    by_cases h : p ∈ P
    · simpa only [w, ite_eq_left h] using hdivP p h
    · simpa only [w, ite_eq_right h] using hdivQ p ((mem_union.mp hp).resolve_left h)
  have hh := sum_log_prime_powers_le_log (P ∪ Q) w hD
    (fun p hp => (mem_union.mp hp).elim (hP p) (hQ p)) hw
  rw [sum_union hPQ] at hh
  have h₁ : (∑ p ∈ P, (w p : ℝ) * Real.log p) =
      ∑ p ∈ P, (e p : ℝ) * Real.log p := by
    apply sum_congr rfl
    intro p hp
    simp only [w, ite_eq_left hp]
  have h₂ : (∑ p ∈ Q, (w p : ℝ) * Real.log p) =
      ∑ p ∈ Q, (v p : ℝ) * Real.log p := by
    apply sum_congr rfl
    intro p hp
    have hn : p ∉ P := fun h => (disjoint_left.mp hPQ) h hp
    simp only [w, ite_eq_right hn]
  rwa [h₁, h₂] at hh

/-- Prescribed primes excluded from the global sum contribute their entire
local valuation, in addition to the global lower bound. A lower cutoff costs
`log L`; perturbing `p` by `C √p` costs `O(C / √L)`. -/
theorem general_determinant_log_lower_cutoff_congruence {x L C A E : ℝ}
    (hx : 1 ≤ x) (hL : 1 ≤ L) (hC : 0 ≤ C) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (bad P : Finset ℕ) (hPbad : P ⊆ bad) (hP : ∀ p ∈ P, p.Prime)
    (mass : ℕ → ℝ) (e v : ℕ → ℕ) {D : ℤ} (hD : 0 < D)
    (hmass : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, L < (p : ℝ) → 0 < mass p)
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, L < (p : ℝ) →
      mass p ≤ p + C * Real.sqrt p)
    (he : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, L < (p : ℝ) →
      A / mass p - E ≤ e p)
    (hdiv : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, L < (p : ℝ) →
      (p : ℤ) ^ e p ∣ D)
    (hcong : ∀ p ∈ P, (p : ℤ) ^ v p ∣ D) :
    A * (Real.log x - Real.log L - 2 * mertensError -
      (∑ p ∈ bad, Real.log p / p) - C * (2 * primeBlockMass / Real.sqrt L)) -
      E * ((Real.log 4 + 4) * x) +
      (∑ p ∈ P, (v p : ℝ) * Real.log p) ≤ Real.log D := by
  classical
  let S := (((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad).filter (fun p : ℕ => L < (p : ℝ))
  have hp (p : ℕ) (hp : p ∈ S) : p.Prime :=
    (mem_filter.mp (mem_sdiff.mp (mem_filter.mp hp).1).1).2
  have hSP : Disjoint S P := by
    apply disjoint_left.mpr
    intro p hpS hpP
    exact (mem_sdiff.mp (mem_filter.mp hpS).1).2 (hPbad hpP)
  have hsum := sum_log_disjoint_prime_powers_le_log S P hSP e v hD hp hP
    (fun p hp => hdiv p (mem_filter.mp hp).1 (mem_filter.mp hp).2) hcong
  have hlocal : A * (∑ p ∈ S, Real.log p / mass p) - E * (∑ p ∈ S, Real.log p) ≤
      ∑ p ∈ S, (e p : ℝ) * Real.log p := by
    calc
      _ = ∑ p ∈ S, (A / mass p - E) * Real.log p := by
        rw [mul_sum, mul_sum, ← sum_sub_distrib]
        apply sum_congr rfl
        intro p _
        ring
      _ ≤ _ := sum_le_sum fun p hp => mul_le_mul_of_nonneg_right
        (he p (mem_filter.mp hp).1 (mem_filter.mp hp).2) (Real.log_natCast_nonneg p)
  have hm := weighted_prime_sum_lower_cutoff hx hL hC bad mass hmass hupper
  have htheta : (∑ p ∈ S, Real.log p) ≤ (Real.log 4 + 4) * x := by
    calc
      _ ≤ Chebyshev.theta x := by
        apply sum_le_sum_of_subset_of_nonneg ((filter_subset _ _).trans sdiff_subset)
        intro p _ _
        exact Real.log_natCast_nonneg p
      _ ≤ Chebyshev.psi x := Chebyshev.theta_le_psi x
      _ ≤ _ := Chebyshev.psi_le_const_mul_self (by linarith)
  have hm' := mul_le_mul_of_nonneg_left hm hA
  have ht' := mul_le_mul_of_nonneg_left htheta hE
  linarith

/-- A lower cutoff costs log(L); perturbing p by C sqrt(p) costs O(C/sqrt(L)).
All selected prime-power divisors are multiplied into the integer D. -/
theorem general_determinant_log_lower_cutoff {x L C A E : ℝ}
    (hx : 1 ≤ x) (hL : 1 ≤ L) (hC : 0 ≤ C) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (B : Finset ℕ) (mass : ℕ → ℝ) (e : ℕ → ℕ) {D : ℤ} (hD : 0 < D)
    (hmass : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) → 0 < mass p)
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) →
      mass p ≤ p + C * Real.sqrt p)
    (he : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) →
      A / mass p - E ≤ e p)
    (hdiv : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) →
      (p : ℤ) ^ e p ∣ D) :
    A * (Real.log x - Real.log L - 2 * mertensError -
      (∑ p ∈ B, Real.log p / p) - C * (2 * primeBlockMass / Real.sqrt L)) -
      E * ((Real.log 4 + 4) * x) ≤ Real.log D := by
  have h := general_determinant_log_lower_cutoff_congruence hx hL hC hA hE B ∅
    (empty_subset B) (by simp) mass e e hD hmass hupper he hdiv (by simp)
  rwa [sum_empty, add_zero] at h

/-- Prime aggregation from a local divisor oracle. Every prime `p > L` up to `x` outside
`bad` supplies an exponent `e` with `A / mass p - E ≤ e` and `p ^ e ∣ D`, where
`mass p ≤ p + K d² √p` and `d ^ 4 ≤ L`; every `p ∈ P ⊆ bad` contributes `p ^ v p ∣ D`. -/
theorem determinant_log_lower_of_local_divisors {x L K A E : ℝ} {d : ℕ}
    (hx : 1 ≤ x) (hd : 0 < d) (hdL : (d : ℝ) ^ 4 ≤ L) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hE : 0 ≤ E) (bad P : Finset ℕ) (hPbad : P ⊆ bad) (hP : ∀ p ∈ P, p.Prime) (v : ℕ → ℕ)
    (mass : ℕ → ℝ) {D : ℤ} (hD : 0 < D)
    (hmass : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, L < (p : ℝ) → 0 < mass p)
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, L < (p : ℝ) →
      mass p ≤ p + K * (d : ℝ) ^ 2 * Real.sqrt p)
    (hlocal : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, L < (p : ℝ) →
      ∃ e : ℕ, A / mass p - E ≤ e ∧ (p : ℤ) ^ e ∣ D)
    (hcong : ∀ p ∈ P, (p : ℤ) ^ v p ∣ D) :
    A * (Real.log x - Real.log L - 2 * mertensError - (∑ p ∈ bad, Real.log p / p) -
      2 * K * primeBlockMass) - E * ((Real.log 4 + 4) * x) +
      (∑ p ∈ P, (v p : ℝ) * Real.log p) ≤ Real.log D := by
  classical
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 1 ≤ L := (one_le_pow₀ hd1).trans hdL
  let G := ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad
  let e : ℕ → ℕ := fun p => if h : p ∈ G ∧ L < (p : ℝ) then (hlocal p h.1 h.2).choose else 0
  have hspec (p : ℕ) (hp : p ∈ G) (hcut : L < (p : ℝ)) :
      A / mass p - E ≤ e p ∧ (p : ℤ) ^ e p ∣ D := by
    have h : p ∈ G ∧ L < (p : ℝ) := ⟨hp, hcut⟩
    simp only [e, dite_eq_left h]
    exact (hlocal p hp hcut).choose_spec
  have hh := general_determinant_log_lower_cutoff_congruence hx hL
    (mul_nonneg hK (sq_nonneg (d : ℝ))) hA hE bad P hPbad hP mass e v hD hmass hupper
    (fun p hp hcut => (hspec p hp hcut).1) (fun p hp hcut => (hspec p hp hcut).2) hcong
  have hsqrt : (d : ℝ) ^ 2 ≤ Real.sqrt L :=
    Real.le_sqrt_of_sq_le (by calc ((d : ℝ) ^ 2) ^ 2 = (d : ℝ) ^ 4 := by ring
                                _ ≤ L := hdL)
  have htail : K * (d : ℝ) ^ 2 * (2 * primeBlockMass / Real.sqrt L) ≤
      2 * K * primeBlockMass := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by linarith))).mpr
    have h := mul_le_mul_of_nonneg_left hsqrt
      (mul_nonneg (mul_nonneg zero_le_two hK) primeBlockMass_pos.le)
    linarith
  have hmul := mul_le_mul_of_nonneg_left htail hA
  linarith

/-- The case `L = 27 d ^ 4` of `determinant_log_lower_of_local_divisors`, with local mass
`p + K d² √p`: the cutoff costs `4 log d + log 27`. -/
theorem determinant_log_lower_of_local_divisors_degree_four {x K A E : ℝ} {d : ℕ}
    (hx : 1 ≤ x) (hd : 0 < d) (hK : 0 ≤ K) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (bad P : Finset ℕ) (hPbad : P ⊆ bad) (hP : ∀ p ∈ P, p.Prime) (v : ℕ → ℕ)
    {D : ℤ} (hD : 0 < D)
    (hlocal : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, stepanovThreshold (d : ℝ) < p →
      ∃ e : ℕ, A / (p + K * (d : ℝ) ^ 2 * Real.sqrt p) - E ≤ e ∧ (p : ℤ) ^ e ∣ D)
    (hcong : ∀ p ∈ P, (p : ℤ) ^ v p ∣ D) :
    A * (Real.log x - 4 * Real.log d - Real.log 27 - 2 * mertensError -
      (∑ p ∈ bad, Real.log p / p) - 2 * K * primeBlockMass) -
      E * ((Real.log 4 + 4) * x) + (∑ p ∈ P, (v p : ℝ) * Real.log p) ≤ Real.log D := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h := determinant_log_lower_of_local_divisors hx hd
    (le_mul_of_one_le_left (by positivity) (by norm_num)) hK hA hE bad P hPbad hP v
    (fun p => p + K * (d : ℝ) ^ 2 * Real.sqrt p) hD
    (fun p hp _ => by
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp (mem_sdiff.mp hp).1).2.pos
      positivity)
    (fun _ _ _ => le_rfl) hlocal hcong
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
  push_cast at h
  linarith

end
end CCDN
