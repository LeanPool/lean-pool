/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.IdealFiniteEulerBound
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Norms and multiplicities of prime ideals over a rational prime -/

@[expose] public section

namespace NairTenenbaum

open Finset NumberField Ideal

variable {K : Type*} [Field K] [NumberField K]

/-- The rational prime below a prime ideal. -/
noncomputable def rationalPrimeBelow (P : Ideal (𝓞 K)) : ℕ := Ideal.absNorm (P.under ℤ)

theorem rationalPrimeBelow_prime {P : Ideal (𝓞 K)} (hP : Prime P) :
    (rationalPrimeBelow P).Prime := by
  let : P.IsPrime := Ideal.isPrime_of_prime hP
  let : NeZero P := ⟨hP.ne_zero⟩
  exact Nat.absNorm_under_prime P

theorem idealNorm_eq_primeBelow_pow {P : Ideal (𝓞 K)} (hP : Prime P) :
    Ideal.absNorm P = rationalPrimeBelow P ^ P.inertiaDeg ℤ := by
  let : P.IsPrime := Ideal.isPrime_of_prime hP
  exact (Ideal.absNorm_pow_inertiaDeg (P.under ℤ) P).symm

theorem rationalPrimeBelow_le_norm {P : Ideal (𝓞 K)} (hP : Prime P) :
    rationalPrimeBelow P ≤ Ideal.absNorm P := by
  let : P.IsPrime := Ideal.isPrime_of_prime hP
  rw [idealNorm_eq_primeBelow_pow hP]
  exact Nat.le_self_pow (Ideal.inertiaDeg_pos P ℤ).ne' _

theorem rationalPrimeBelow_sq_le_norm {P : Ideal (𝓞 K)} (hP : Prime P)
    (hneq : Ideal.absNorm P ≠ rationalPrimeBelow P) :
    rationalPrimeBelow P ^ 2 ≤ Ideal.absNorm P := by
  let : P.IsPrime := Ideal.isPrime_of_prime hP
  have hν : 2 ≤ P.inertiaDeg ℤ := by
    have H := Ideal.inertiaDeg_pos P ℤ
    have H₁ : P.inertiaDeg ℤ ≠ 1 := by
      intro h
      exact hneq (by rw [idealNorm_eq_primeBelow_pow hP, h, pow_one])
    omega
  rw [idealNorm_eq_primeBelow_pow hP]
  exact Nat.pow_le_pow_right (rationalPrimeBelow_prime hP).pos hν

theorem card_primesOver_nat_le_degree {p : ℕ} (hp : p.Prime) :
    Nat.card ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) ≤ Module.finrank ℚ K := by
  let : Fact p.Prime := ⟨hp⟩
  let : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  let : Finite ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver (Ideal.span {(p : ℤ)})).to_subtype
  let := Fintype.ofFinite ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K))
  rw [Nat.card_eq_fintype_card, ← RingOfIntegers.rank K,
    ← Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K),
        Fintype.card_eq_sum_ones]
  apply sum_le_sum
  intro P _
  exact Nat.mul_pos (Ideal.ramificationIdx_pos ℤ P.1) (Ideal.inertiaDeg_pos P.1 ℤ)

theorem primeIdeals_fiber_card_le (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    {p : ℕ} (hp : p.Prime) :
    (S.filter (fun P => rationalPrimeBelow P = p)).card ≤ Module.finrank ℚ K := by
  classical
  let T := S.filter (fun P => rationalPrimeBelow P = p)
  let f : T → (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := fun P => by
    have hP := hS P.1 (mem_filter.mp P.2).1
    let : P.1.IsPrime := Ideal.isPrime_of_prime hP
    refine ⟨P.1, inferInstance, ?_⟩
    have HE : P.1.under ℤ = Ideal.span {(p : ℤ)} := by
      have H := Int.ideal_span_absNorm_eq_self (P.1.under ℤ)
      change Ideal.span {((rationalPrimeBelow P.1 : ℕ) : ℤ)} = _ at H
      rw [(mem_filter.mp P.2).2] at H
      exact H.symm
    rw [← HE]
    infer_instance
  have hf : Function.Injective f := fun P Q h => Subtype.ext (show P.1 = Q.1 from congrArg (fun J
      => J.1) h)
  let : Finite ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver (Ideal.span {(p : ℤ)})).to_subtype
  have H := Nat.card_le_card_of_injective f hf
  have H' : T.card ≤ Nat.card ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) := by simpa using H
  exact H'.trans (card_primesOver_nat_le_degree hp)

end NairTenenbaum
