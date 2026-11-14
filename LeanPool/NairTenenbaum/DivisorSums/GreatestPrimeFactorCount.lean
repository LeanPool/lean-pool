/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.DivisorSums.DivisorWindowMoments
public import LeanPool.NairTenenbaum.DivisorSums.RoughLogMass
public import Mathlib.Data.Nat.MaxPrimeFac

/-! # Greatest prime factors and divisor hits

This is the finite counting step of Theorem 2. The arithmetic estimate for
how much logarithmic mass survives in the rough cofactors is separate.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Real

theorem prime_le_maxPrimeFac_prod {ι : Type*} (S : Finset ι) (n : ι → ℕ)
    (hn : ∀ i ∈ S, n i ≠ 0) {p : ℕ} {j : ι} (hj : j ∈ S)
    (hp : p.Prime) (hd : p ∣ n j) : p ≤ Nat.maxPrimeFac (∏ j ∈ S, n j) := by
  exact Nat.le_maxPrimeFac (Finset.prod_ne_zero_iff.mpr hn) hp
    (hd.trans (Finset.dvd_prod_of_mem n hj))

theorem rough_logMass_le_maxPrimeFac_prod {ι : Type*} (S H : Finset ι) (hH : H ⊆ S)
    (n b : ι → ℕ) (hn : ∀ i ∈ S, n i ≠ 0) (hb : ∀ i ∈ S, b i ≠ 0)
    (hd : ∀ i ∈ S, b i ∣ n i) {k : ℕ} (hk : 2 ≤ k)
    (hΩ : ∀ i ∈ S, bigOmega (b i) ≤ k - 1)
    (hΩH : ∀ i ∈ H, bigOmega (b i) ≤ k - 2) :
    (∑ i ∈ S, Real.log (b i)) ≤ (((k : ℝ) - 1) * S.card - H.card) *
      Real.log (Nat.maxPrimeFac (∏ i ∈ S, n i)) := by
  have hP : 1 ≤ Nat.maxPrimeFac (∏ i ∈ S, n i) :=
    Nat.one_le_maxPrimeFac_iff.mpr (Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr hn))
  apply rough_logMass_le_saved_factors S H hH b hb hk (by exact_mod_cast hP) _ hΩ hΩH
  intro i hi p hp
  exact_mod_cast prime_le_maxPrimeFac_prod S n hn hi (Nat.prime_of_mem_primeFactors hp)
    ((Nat.dvd_of_mem_primeFactors hp).trans (hd i hi))

theorem rough_logMass_le_divisorHits {ι : Type*} (S : Finset ι) (n a b : ι → ℕ)
    (ha : ∀ i ∈ S, a i ≠ 0) (hb : ∀ i ∈ S, b i ≠ 0)
    (hsplit : ∀ i ∈ S, a i * b i = n i) {k : ℕ} (hk : 2 ≤ k) {A C y : ℝ}
    (hy : 1 ≤ y) (hC : 1 ≤ C) (hA : A < C ^ k) (hA' : 2 * A < C ^ (k - 1))
    (hsize : ∀ i ∈ S, (n i : ℝ) ≤ A * y ^ k)
    (hrough : ∀ i ∈ S, ∀ p ∈ (b i).primeFactors, C * y < (p : ℝ)) :
    (∑ i ∈ S, Real.log (b i)) ≤
      (((k : ℝ) - 1) * S.card - (S.filter (fun i => 0 < dyadicDivisorCount (n i) y)).card) *
        Real.log (Nat.maxPrimeFac (∏ i ∈ S, n i)) := by
  classical
  have hn (i : ι) (hi : i ∈ S) : n i ≠ 0 := by
    rw [← hsplit i hi]; exact mul_ne_zero (ha i hi) (hb i hi)
  have hdiv (i : ι) (hi : i ∈ S) : b i ∣ n i := by rw [← hsplit i hi]; exact dvd_mul_left _ _
  apply rough_logMass_le_maxPrimeFac_prod S _ (filter_subset _ _) n b hn hb hdiv hk
  · intro i hi
    apply rough_cofactor_bigOmega_le (hb i hi) hy hC hA
    · exact (by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (hn i hi)) (hdiv i hi) : (b i : ℝ) ≤ n
          i).trans (hsize i hi)
    · exact fun p hp => (hrough i hi p hp).le
  · intro i hi
    obtain ⟨hi, hwindow⟩ := mem_filter.mp hi
    unfold dyadicDivisorCount at hwindow
    obtain ⟨d, hd⟩ := Finset.card_pos.mp hwindow
    obtain ⟨hdn, hdy, hdy'⟩ := mem_filter.mp hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hdn
    have hddiv : d ∣ a i * b i := by rw [hsplit i hi]; exact Nat.dvd_of_mem_divisors hdn
    have hdz : (d : ℝ) ≤ C * y := hdy'.trans (by nlinarith)
    have hdb := rough_cofactor_mul_divisor_le hdpos (hb i hi) hdz (hrough i hi) hddiv (ha i hi)
    rw [hsplit i hi] at hdb
    exact rough_cofactor_bigOmega_le_of_window_divisor (hb i hi) hk hy hC hA'
      (hsize i hi) hdb hdy (fun p hp => (hrough i hi p hp).le)

end NairTenenbaum
