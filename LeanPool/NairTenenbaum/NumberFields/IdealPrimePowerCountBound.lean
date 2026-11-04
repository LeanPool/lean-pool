/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.PrimeIdealNormBounds

/-! # Polynomial growth of ideal counts at prime powers

An ideal of norm `p^k` is determined by the multiplicities of the prime ideals
above `p`. Each multiplicity is at most `k`, and there are at most `[K:ℚ]`
such prime ideals.
-/

@[expose] public section

namespace NairTenenbaum

open Finset NumberField Ideal UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

theorem rationalPrimeBelow_eq_of_dvd_primePowerNorm {P I : Ideal (𝓞 K)}
    (hP : Prime P) {p k : ℕ} (hp : p.Prime) (hI : absNorm I = p ^ k) (hd : P ∣ I) :
    rationalPrimeBelow P = p := by
  let : P.IsPrime := Ideal.isPrime_of_prime hP
  have H : rationalPrimeBelow P ∣ absNorm P := by
    rw [idealNorm_eq_primeBelow_pow hP]
    exact dvd_pow_self _ (Ideal.inertiaDeg_pos P ℤ).ne'
  have H' : rationalPrimeBelow P ∣ p ^ k := hI ▸ H.trans (map_dvd absNorm hd)
  have hq := rationalPrimeBelow_prime hP
  exact ((Nat.dvd_prime hp).mp (hq.dvd_of_dvd_pow H')).resolve_left hq.ne_one

theorem ideal_factor_count_le_primePowerNorm {I P : Ideal (𝓞 K)} {p k : ℕ}
    (hp : p.Prime) (hI : absNorm I = p ^ k) : (normalizedFactors I).count P ≤ k := by
  classical
  have hI0 : I ≠ ⊥ := by
    intro h
    have H := hI
    rw [h, absNorm_bot] at H
    exact (pow_ne_zero _ hp.ne_zero) H.symm
  by_cases hP : P ∈ normalizedFactors I
  · have hprime := prime_of_normalized_factor P hP
    have hpbelow := rationalPrimeBelow_eq_of_dvd_primePowerNorm hprime hp hI
      (dvd_of_mem_normalizedFactors hP)
    have hpow : P ^ (normalizedFactors I).count P ∣ I := by
      have H := dvd_prod_of_mem (fun R : Ideal (𝓞 K) => R ^ (normalizedFactors I).count R)
        (Multiset.mem_toFinset.mpr hP)
      rwa [← ideal_eq_prod_factor_counts hI0 (normalizedFactors I).toFinset (Subset.refl _)] at H
    have hnorm : absNorm P ^ (normalizedFactors I).count P ≤ p ^ k := by
      apply Nat.le_of_dvd (pow_pos hp.pos _)
      simpa only [map_pow, hI] using map_dvd absNorm hpow
    have hbase : p ≤ absNorm P := hpbelow ▸ rationalPrimeBelow_le_norm hprime
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp
      ((Nat.pow_le_pow_left hbase _).trans hnorm)
  · simp [Multiset.count_eq_zero.mpr hP]

theorem idealNormCount_prime_pow_le {p k : ℕ} (hp : p.Prime) :
    idealNormCount K (p ^ k) ≤ (k + 1) ^ Module.finrank ℚ K := by
  classical
  let T : Finset (Ideal (𝓞 K)) := (finite_setOfPred_absNorm_eq (p ^ k)).toFinset
  have hT (I : Ideal (𝓞 K)) : I ∈ T ↔ absNorm I = p ^ k := by simp [T]
  let S := T.biUnion (fun I => (normalizedFactors I).toFinset)
  have hS (P : Ideal (𝓞 K)) (hP : P ∈ S) : Prime P ∧ rationalPrimeBelow P = p := by
    obtain ⟨I, hIT, hPI⟩ := mem_biUnion.mp hP
    have hPI' := Multiset.mem_toFinset.mp hPI
    have hprime := prime_of_normalized_factor P hPI'
    exact ⟨hprime, rationalPrimeBelow_eq_of_dvd_primePowerNorm hprime hp ((hT I).mp hIT)
      (dvd_of_mem_normalizedFactors hPI')⟩
  have hcard : S.card ≤ Module.finrank ℚ K := by
    have H := primeIdeals_fiber_card_le S (fun P hP => (hS P hP).1) hp
    rwa [filter_eq_self.mpr (fun P hP => (hS P hP).2)] at H
  let f : {I : Ideal (𝓞 K) // absNorm I = p ^ k} → (S → Fin (k + 1)) :=
    fun I P => ⟨(normalizedFactors I.1).count P.1,
      Nat.lt_succ_of_le (ideal_factor_count_le_primePowerNorm hp I.2)⟩
  have hf : Function.Injective f := by
    intro I J hij
    have hnonzero (L : {I : Ideal (𝓞 K) // absNorm I = p ^ k}) : L.1 ≠ ⊥ := by
      intro h
      have H := L.2
      rw [h, absNorm_bot] at H
      exact (pow_ne_zero _ hp.ne_zero) H.symm
    have hsupport (L : {I : Ideal (𝓞 K) // absNorm I = p ^ k}) :
        (normalizedFactors L.1).toFinset ⊆ S := by
      intro P hP
      exact mem_biUnion.mpr ⟨L.1, (hT L.1).mpr L.2, hP⟩
    apply Subtype.ext
    rw [ideal_eq_prod_factor_counts (hnonzero I) S (hsupport I),
      ideal_eq_prod_factor_counts (hnonzero J) S (hsupport J)]
    apply prod_congr rfl
    intro P hP
    have H := congrArg Fin.val (congrFun hij ⟨P, hP⟩)
    exact congrArg (fun e : ℕ => P ^ e) H
  have H := Nat.card_le_card_of_injective f hf
  have H' : idealNormCount K (p ^ k) ≤ (k + 1) ^ S.card := by
    simpa [idealNormCount, Nat.card_fun] using H
  exact H'.trans (Nat.pow_le_pow_right (by omega) hcard)

end NairTenenbaum
