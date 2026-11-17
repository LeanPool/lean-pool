/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.PrimeIdealSupport

/-! # Ideals of prime-power norm as weighted multiplicity vectors -/

@[expose] public section

namespace NairTenenbaum

open Finset NumberField Ideal UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

theorem ideal_prime_power_product_count (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, Prime P) (e : Ideal (𝓞 K) → ℕ) (Q : Ideal (𝓞 K)) :
    (normalizedFactors (∏ P ∈ S, P ^ e P)).count Q = if Q ∈ S then e Q else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [prod_empty, normalizedFactors_one, Multiset.count_zero, notMem_empty,
      ite_false]
  | @insert P S hPS ih =>
    have hP : Prime P := hS P (mem_insert_self _ _)
    have hS' : ∀ R ∈ S, Prime R := fun R hR => hS R (mem_insert_of_mem hR)
    rw [prod_insert hPS, normalizedFactors_mul (pow_ne_zero _ hP.ne_zero)
      (prod_ne_zero_iff.mpr (fun R hR => pow_ne_zero _ (hS' R hR).ne_zero)),
      Multiset.count_add, hP.irreducible.normalizedFactors_pow, normalize_eq,
      Multiset.count_replicate, ih hS']
    by_cases hPQ : P = Q
    · subst Q
      simp [hPS]
    · simp [hPQ, Ne.symm hPQ]

/-- The ideal obtained by multiplying prime ideals with specified multiplicities. -/
noncomputable def idealOfMultiplicities (S : Finset (Ideal (𝓞 K))) (e : S → ℕ) : Ideal (𝓞 K) :=
  ∏ P : S, P.1 ^ e P

theorem idealOfMultiplicities_count (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, Prime P) (e : S → ℕ) (P : S) :
    (normalizedFactors (idealOfMultiplicities S e)).count P.1 = e P := by
  classical
  let E : Ideal (𝓞 K) → ℕ := fun Q => if hQ : Q ∈ S then e ⟨Q, hQ⟩ else 0
  have HE : idealOfMultiplicities S e = ∏ Q ∈ S, Q ^ E Q := by
    rw [← prod_coe_sort S (fun Q => Q ^ E Q)]
    apply prod_congr rfl
    intro Q _
    simp [E]
  rw [HE, ideal_prime_power_product_count S hS E P.1, ite_eq_left P.2]
  simp [E, P.2]

theorem idealOfMultiplicities_factor_counts {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (S : Finset (Ideal (𝓞 K))) (hs : (normalizedFactors I).toFinset ⊆ S) :
    idealOfMultiplicities S (fun P => (normalizedFactors I).count P.1) = I := by
  unfold idealOfMultiplicities
  rw [prod_coe_sort S (fun P => P ^ (normalizedFactors I).count P)]
  exact (ideal_eq_prod_factor_counts hI S hs).symm

theorem idealOfMultiplicities_norm {p : ℕ} (hp : p.Prime)
    (e : primeIdealSupport K p → ℕ) :
    absNorm (idealOfMultiplicities (primeIdealSupport K p) e) =
      p ^ (∑ P : primeIdealSupport K p, P.1.inertiaDeg ℤ * e P) := by
  unfold idealOfMultiplicities
  rw [map_prod]
  simp_rw [map_pow]
  calc
    _ = ∏ P : primeIdealSupport K p, p ^ (P.1.inertiaDeg ℤ * e P) := by
      apply prod_congr rfl
      intro P _
      rw [primeIdealSupport_norm hp P.2, ← pow_mul]
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

/-- Prime-power-norm ideals identified with weighted prime-ideal multiplicities. -/
noncomputable def idealNormPrimePowerEquiv {p : ℕ} (hp : p.Prime) (k : ℕ) :
    {I : Ideal (𝓞 K) // absNorm I = p ^ k} ≃
      {e : primeIdealSupport K p → ℕ // ∑ P, P.1.inertiaDeg ℤ * e P = k} where
  toFun I := ⟨fun P => (normalizedFactors I.1).count P.1, by
    apply Nat.pow_right_injective hp.two_le
    change p ^ (∑ P : primeIdealSupport K p, P.1.inertiaDeg ℤ * (normalizedFactors I.1).count P.1)
        = p ^ k
    rw [← idealOfMultiplicities_norm hp (fun P => (normalizedFactors I.1).count P.1),
        idealOfMultiplicities_factor_counts
      (by intro h; have H := I.2; rw [h, absNorm_bot] at H; exact (pow_ne_zero _ hp.ne_zero) H.symm)
      _ (normalizedFactors_subset_primeIdealSupport hp I.2)]
    exact I.2⟩
  invFun e := ⟨idealOfMultiplicities (primeIdealSupport K p) e.1, by
    rw [idealOfMultiplicities_norm hp, e.2]⟩
  left_inv I := by
    apply Subtype.ext
    exact idealOfMultiplicities_factor_counts
      (by intro h; have H := I.2; rw [h, absNorm_bot] at H; exact (pow_ne_zero _ hp.ne_zero) H.symm)
      _ (normalizedFactors_subset_primeIdealSupport hp I.2)
  right_inv e := by
    apply Subtype.ext
    funext P
    exact idealOfMultiplicities_count _
      (fun Q hQ => ((primeIdealSupport_mem_iff hp).mp hQ).1) e.1 P

theorem idealNormCount_prime_pow_eq_card_vectors {p : ℕ} (hp : p.Prime) (k : ℕ) :
    idealNormCount K (p ^ k) =
      Nat.card {e : primeIdealSupport K p → ℕ // ∑ P, P.1.inertiaDeg ℤ * e P = k} :=
  Nat.card_congr (idealNormPrimePowerEquiv hp k)

end NairTenenbaum
