/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Sieve.OmittedEulerFactors

/-! # Totient corrections on products and restricted prime support -/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real

theorem totientTwist_mul_le (g : ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    totientTwist g (a * b) ≤ totientTwist g a * totientTwist g b := by
  have hφa : (0 : ℝ) < a.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero ha)
  have hφb : (0 : ℝ) < b.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hb)
  have H : (a * b : ℕ) / ((a * b).totient : ℝ) ≤ (a : ℝ) / a.totient * ((b : ℝ) / b.totient) := by
    rw [← mul_div_mul_comm, Nat.cast_mul]
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos hφa hφb)
      (by exact_mod_cast Nat.totient_super_multiplicative a b)
  simpa only [totientTwist, mul_pow] using pow_le_pow_left₀ (by positivity) H g

theorem totientTwist_prod_le {ι : Type*} (g : ℕ) (S : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ S, f i ≠ 0) :
    totientTwist g (∏ i ∈ S, f i) ≤ ∏ i ∈ S, totientTwist g (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hf' : ∀ i ∈ S, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact (totientTwist_mul_le g (hf a (Finset.mem_insert_self a S)) (Finset.prod_ne_zero_iff.mpr
        hf')).trans
      (mul_le_mul_of_nonneg_left (ih hf') (totientTwist_nonneg g (f a)))

theorem totientTwist_mass_le {r : ℕ} (g : ℕ) (m : Tuple r) :
    totientTwist g (mass m) ≤ ∏ i, totientTwist g (m i) :=
  totientTwist_prod_le g Finset.univ (fun i => (m i : ℕ)) (fun i _ => (m i).ne_zero)

theorem totientTwist_le_of_primeFactors_subset (g : ℕ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hsub : m.primeFactors ⊆ n.primeFactors) : totientTwist g m ≤ totientTwist g n := by
  rw [totientTwist_eq_prod g hm, totientTwist_eq_prod g hn]
  apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
  · exact fun p _ => totientTwist_nonneg g p
  · exact fun p hp _ => totientTwist_one_le g (Nat.prime_of_mem_primeFactors hp).ne_zero

end NairTenenbaum
