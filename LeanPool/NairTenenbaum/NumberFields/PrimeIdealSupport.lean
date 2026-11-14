/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.IdealPrimePowerCountBound

/-! # The finite set of prime ideals above a rational prime -/

@[expose] public section

namespace NairTenenbaum

open Finset NumberField Ideal UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

/-- The finite set of prime ideals above a specified rational prime. -/
noncomputable def primeIdealSupport (K : Type*) [Field K] [NumberField K] (p : ℕ) :
    Finset (Ideal (𝓞 K)) := (normalizedFactors (Ideal.span {(p : 𝓞 K)})).toFinset

theorem span_prime_natCast_ne_bot {p : ℕ} (hp : p.Prime) :
    (Ideal.span {(p : 𝓞 K)}) ≠ ⊥ := by
  rw [ne_eq, Ideal.span_singleton_eq_bot]
  exact Nat.cast_ne_zero.mpr hp.ne_zero

theorem primeIdealSupport_mem_iff {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} :
    P ∈ primeIdealSupport K p ↔ Prime P ∧ rationalPrimeBelow P = p := by
  rw [primeIdealSupport, Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff (span_prime_natCast_ne_bot hp)]
  constructor
  · rintro ⟨hP, hd⟩
    exact ⟨hP, rationalPrimeBelow_eq_of_dvd_primePowerNorm hP hp
      (Ideal.absNorm_span_natCast p) hd⟩
  · rintro ⟨hP, hbelow⟩
    refine ⟨hP, Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩
    have HE := Int.ideal_span_absNorm_eq_self (P.under ℤ)
    change Ideal.span {((rationalPrimeBelow P : ℕ) : ℤ)} = P.under ℤ at HE
    rw [hbelow] at HE
    have HM : (p : ℤ) ∈ P.under ℤ := by rw [← HE]; exact Ideal.subset_span (Set.mem_singleton _)
    simpa only [map_natCast] using (Ideal.mem_under ℤ P).mp HM

theorem normalizedFactors_subset_primeIdealSupport {I : Ideal (𝓞 K)} {p k : ℕ}
    (hp : p.Prime) (hI : absNorm I = p ^ k) :
    (normalizedFactors I).toFinset ⊆ primeIdealSupport K p := by
  intro P hP
  have HM := Multiset.mem_toFinset.mp hP
  have HP := prime_of_normalized_factor P HM
  exact (primeIdealSupport_mem_iff hp).mpr ⟨HP,
    rationalPrimeBelow_eq_of_dvd_primePowerNorm HP hp hI (dvd_of_mem_normalizedFactors HM)⟩

theorem primeIdealSupport_norm {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : P ∈ primeIdealSupport K p) : absNorm P = p ^ P.inertiaDeg ℤ := by
  obtain ⟨hprime, hbelow⟩ := (primeIdealSupport_mem_iff hp).mp hP
  rw [idealNorm_eq_primeBelow_pow hprime, hbelow]

theorem primeIdealSupport_inertiaDeg_pos {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : P ∈ primeIdealSupport K p) : 0 < P.inertiaDeg ℤ := by
  let : P.IsPrime := Ideal.isPrime_of_prime ((primeIdealSupport_mem_iff hp).mp hP).1
  exact Ideal.inertiaDeg_pos P ℤ

end NairTenenbaum
