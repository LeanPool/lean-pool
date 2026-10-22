/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Analysis.PrimeCutoff
public import LeanPool.CCDN.AuxiliaryPolynomial.DegreeBound
import LeanPool.CCDN.Analysis.PrimeProduct

/-! Analytic control of bad-prime charges from an integer witness.
The construction and coefficient bound for a Noether witness remain separate. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real

/-- Distinct prime divisors of a positive integer have total logarithmic
weight at most the logarithm of that integer. -/
lemma prime_divisor_log_sum_le (P : Finset ℕ) {D : ℤ} (hD : 0 < D)
    (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, (p : ℤ) ∣ D) :
    (∑ p ∈ P, Real.log p) ≤ Real.log D := by
  simpa only [Nat.cast_one, one_mul] using sum_log_prime_powers_le_log P (fun _ => 1)
    hD hP (fun p hp => by simpa only [pow_one] using hdiv p hp)

/-- Above a cutoff T, the reciprocal-weighted charge costs at most log(D)/T. -/
lemma prime_divisor_charge_le (P : Finset ℕ) {D : ℤ} (hD : 0 < D)
    (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, (p : ℤ) ∣ D)
    {T : ℝ} (hT : 0 < T) (hlo : ∀ p ∈ P, T ≤ (p : ℝ)) :
    (∑ p ∈ P, Real.log p / p) ≤ Real.log D / T := by
  calc
    _ ≤ ∑ p ∈ P, Real.log p / T := by
      apply sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_left (by positivity) hT (hlo p hp)
    _ = (∑ p ∈ P, Real.log p) / T := (sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (prime_divisor_log_sum_le P hD hP hdiv) hT.le

/-- Mertens bounds an arbitrary prime interval, with its logarithmic width
and two absolute error terms. -/
private lemma prime_interval_weight_le {L T : ℝ} (hL : 1 ≤ L) (hLT : L ≤ T)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hlo : ∀ p ∈ P, L < (p : ℝ)) (hhi : ∀ p ∈ P, (p : ℝ) ≤ T) :
    (∑ p ∈ P, Real.log p / p) ≤ Real.log T - Real.log L + 2 * mertensError := by
  let U := (Ioc 0 ⌊L⌋₊).filter Nat.Prime
  let V := (Ioc 0 ⌊T⌋₊).filter Nat.Prime
  have hUV : U ⊆ V := by
    intro p hp
    have hp' := (mem_filter.mp hp).2
    exact (prime_mem_upto_iff (by linarith) hp').mpr
      (((prime_mem_upto_iff (by linarith) hp').mp hp).trans hLT)
  have hPV : P ⊆ V \ U := by
    intro p hp
    refine mem_sdiff.mpr ⟨(prime_mem_upto_iff (by linarith) (hP p hp)).mpr (hhi p hp), ?_⟩
    intro hu
    exact (not_le_of_gt (hlo p hp)) ((prime_mem_upto_iff (by linarith) (hP p hp)).mp hu)
  have hsum : (∑ p ∈ P, Real.log p / p) ≤ ∑ p ∈ V \ U, Real.log p / p :=
    sum_le_sum_of_subset_of_nonneg hPV (fun _ _ _ => by positivity)
  have hsplit := sum_sdiff hUV (f := fun p : ℕ => Real.log p / p)
  have hl := (abs_le.mp (Mertens.prime_sum_bounded_error hL)).1
  have ht := (abs_le.mp (Mertens.prime_sum_bounded_error (hL.trans hLT))).2
  change -mertensError ≤ (∑ p ∈ U, Real.log p / p) - Real.log L at hl
  change (∑ p ∈ V, Real.log p / p) - Real.log T ≤ mertensError at ht
  linarith

/-- Split the bad primes at T. The low part costs log(T/L), while the high
part is bounded using the integer witness. -/
private theorem bad_prime_charge_split (P : Finset ℕ) {D : ℤ} (hD : 0 < D)
    (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, (p : ℤ) ∣ D)
    {L T : ℝ} (hL : 1 ≤ L) (hLT : L ≤ T) (hlo : ∀ p ∈ P, L < (p : ℝ)) :
    (∑ p ∈ P, Real.log p / p) ≤
      Real.log T - Real.log L + 2 * mertensError + Real.log D / T := by
  classical
  let U := P.filter (fun p : ℕ => (p : ℝ) ≤ T)
  let V := P.filter (fun p : ℕ => ¬ (p : ℝ) ≤ T)
  have hlow := prime_interval_weight_le hL hLT U
    (fun p hp => hP p (mem_filter.mp hp).1)
    (fun p hp => hlo p (mem_filter.mp hp).1)
    (fun _ hp => (mem_filter.mp hp).2)
  have hhigh := prime_divisor_charge_le V hD
    (fun p hp => hP p (mem_filter.mp hp).1)
    (fun p hp => hdiv p (mem_filter.mp hp).1)
    (by linarith : 0 < T)
    (fun _ hp => (lt_of_not_ge (mem_filter.mp hp).2).le)
  have hsplit := sum_filter_add_sum_filter_not P (fun p : ℕ => (p : ℝ) ≤ T)
    (fun p : ℕ => Real.log p / p)
  change (∑ p ∈ U, Real.log p / p) + (∑ p ∈ V, Real.log p / p) = _ at hsplit
  linarith

/-- A logarithmic-height bound for an integer witness controls the bad-prime
charge at the scale of the cutoff. Constructing such a witness is algebraic. -/
theorem bad_prime_charge_of_height (P : Finset ℕ) {D : ℤ} (hD : 0 < D)
    (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, (p : ℤ) ∣ D)
    {L H : ℝ} (hL : 1 ≤ L) (hH : 1 ≤ H) (hlo : ∀ p ∈ P, L < (p : ℝ))
    (hheight : Real.log D ≤ L * H) :
    (∑ p ∈ P, Real.log p / p) ≤ Real.log H + 2 * mertensError + 1 := by
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < H := by linarith
  have hLT : L ≤ L * H := le_mul_of_one_le_right hL0.le hH
  have h := bad_prime_charge_split P hD hP hdiv hL hLT hlo
  have ht : Real.log D / (L * H) ≤ 1 := (div_le_one (mul_pos hL0 hH0)).mpr hheight
  rw [Real.log_mul hL0.ne' hH0.ne'] at h
  linarith

/-- The exponential bad-prime factor has linear dependence on the scaled
logarithmic height of a nonzero integer witness. -/
theorem bad_prime_factor_of_height (P : Finset ℕ) {D : ℤ} (hD : 0 < D)
    (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, (p : ℤ) ∣ D)
    {L H : ℝ} (hL : 1 ≤ L) (hH : 1 ≤ H) (hlo : ∀ p ∈ P, L < (p : ℝ))
    (hheight : Real.log D ≤ L * H) :
    primeSetFactor P ≤ Real.exp (2 * mertensError + 1) * H := by
  have h := Real.exp_le_exp.mpr (bad_prime_charge_of_height P hD hP hdiv hL hH hlo hheight)
  calc
    _ ≤ Real.exp (Real.log H + 2 * mertensError + 1) := h
    _ = Real.exp (2 * mertensError + 1) * H := by
      rw [add_assoc, Real.exp_add, Real.exp_log (by linarith : 0 < H)]
      ring

end
end CCDN
