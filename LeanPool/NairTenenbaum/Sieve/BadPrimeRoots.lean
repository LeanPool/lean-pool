/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.DiscriminantBezout
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Prime.Int

/-! # Root counts at primes dividing the discriminant

Taylor expansion and the discriminant identity bound the clustering of roots.
The resulting count is uniform in the exponent of the modulus.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial

theorem prime_pow_dvd_of_mul_not_dvd {p x y : ℤ} (hp : Prime p) (a b : ℕ)
    (hxy : p ^ (a + b) ∣ x * y) (hy : ¬ p ^ (b + 1) ∣ y) : p ^ a ∣ x := by
  induction b generalizing y with
  | zero =>
      exact hp.pow_dvd_of_dvd_mul_right a (by simpa using hy) (by simpa using hxy)
  | succ b ih =>
      by_cases hpy : p ∣ y
      · obtain ⟨z, rfl⟩ := hpy
        apply ih
        · apply (mul_dvd_mul_iff_left hp.ne_zero).mp
          simpa only [← pow_succ', Nat.add_succ, mul_left_comm] using hxy
        · intro hz
          apply hy
          simpa only [pow_succ', Nat.succ_eq_add_one] using mul_dvd_mul_left p hz
      · exact (pow_dvd_pow p (Nat.le_add_right a (b + 1))).trans
          (hp.pow_dvd_of_dvd_mul_right (a + (b + 1)) hpy hxy)

/-- A root modulo a sufficiently large prime power cannot have its derivative
divisible by a higher power than the discriminant allows. -/
theorem derivative_not_dvd_of_discr {Q : ℤ[X]} (hdeg : 2 ≤ Q.natDegree)
    {p : ℤ} {δ ν : ℕ} (hδν : δ < ν) (hD : ¬ p ^ (δ + 1) ∣ Q.discr)
    {a : ℤ} (ha : p ^ ν ∣ Q.eval a) : ¬ p ^ (δ + 1) ∣ Q.derivative.eval a := by
  intro hder
  exact hD (dvd_discr_of_dvd_eval_and_derivative hdeg
    ((pow_dvd_pow p (by omega : δ + 1 ≤ ν)).trans ha) hder)

/-- Roots that agree modulo `p^(δ+1)` agree modulo `p^(ν-δ)`, provided
`p^(δ+1)` does not divide the discriminant. -/
theorem root_difference_dvd_of_discr {Q : ℤ[X]} (hdeg : 2 ≤ Q.natDegree)
    {p : ℤ} (hp : Prime p) {δ ν : ℕ} (hδν : δ < ν)
    (hD : ¬ p ^ (δ + 1) ∣ Q.discr) {a b : ℤ}
    (ha : p ^ ν ∣ Q.eval a) (hb : p ^ ν ∣ Q.eval b)
    (hab : p ^ (δ + 1) ∣ b - a) : p ^ (ν - δ) ∣ b - a := by
  obtain ⟨c, hc⟩ := Q.binomExpansion a (b - a)
  have hdiff : Q.eval b - Q.eval a =
      (b - a) * (Q.derivative.eval a + c * (b - a)) := by
    rw [add_sub_cancel] at hc
    linarith [hc]
  have hprod : p ^ ((ν - δ) + δ) ∣
      (b - a) * (Q.derivative.eval a + c * (b - a)) := by
    rw [Nat.sub_add_cancel hδν.le, ← hdiff]
    exact dvd_sub hb ha
  apply prime_pow_dvd_of_mul_not_dvd hp (ν - δ) δ hprod
  intro hsum
  have hder : p ^ (δ + 1) ∣ Q.derivative.eval a := by
    have := dvd_sub hsum (dvd_mul_of_dvd_right hab c)
    simpa only [add_sub_cancel_right] using this
  exact derivative_not_dvd_of_discr hdeg hδν hD ha hder

theorem ResidueRoots.modulus_dvd_eval_val {Q : ℤ[X]} {q : ℕ} [NeZero q]
    (a : ResidueRoots Q q) : (q : ℤ) ∣ Q.eval ((a : ZMod q).val : ℤ) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  change (Int.castRingHom (ZMod q)) (Q.eval ((a : ZMod q).val : ℤ)) = 0
  rw [← Polynomial.eval₂_at_apply]
  change Q.eval₂ (Int.castRingHom (ZMod q)) (((a : ZMod q).val : ℤ) : ZMod q) = 0
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  exact a.property

/-- An exponent-independent root bound, with explicit dependence on a power
that does not divide the discriminant. -/
theorem rootCount_prime_pow_le_discr_bound {Q : ℤ[X]} (hdeg : 2 ≤ Q.natDegree)
    {p : ℕ} (hp : p.Prime) (δ ν : ℕ) (hD : ¬ (p : ℤ) ^ (δ + 1) ∣ Q.discr) :
    rootCount Q (p ^ ν) ≤ p ^ (2 * δ + 1) := by
  let : NeZero (p ^ ν) := ⟨pow_ne_zero _ hp.ne_zero⟩
  by_cases hν : ν ≤ 2 * δ + 1
  · exact (rootCount_le Q (pow_ne_zero _ hp.ne_zero)).trans
      (Nat.pow_le_pow_right hp.pos hν)
  have hδν : δ < ν := by omega
  have hpow : p ^ ν = p ^ δ * p ^ (ν - δ) := by
    rw [← pow_add, Nat.add_sub_of_le hδν.le]
  let f : ResidueRoots Q (p ^ ν) → Fin (p ^ (δ + 1)) × Fin (p ^ δ) := fun a =>
    (⟨(a : ZMod (p ^ ν)).val % p ^ (δ + 1), Nat.mod_lt _ (pow_pos hp.pos _)⟩,
     ⟨(a : ZMod (p ^ ν)).val / p ^ (ν - δ),
       (Nat.div_lt_iff_lt_mul (pow_pos hp.pos _)).mpr (by
         rw [← hpow]
         exact ZMod.val_lt _)⟩)
  have hf : Function.Injective f := by
    intro a b hab
    have hlow : (a : ZMod (p ^ ν)).val % p ^ (δ + 1) =
        (b : ZMod (p ^ ν)).val % p ^ (δ + 1) :=
      congrArg (fun x : Fin (p ^ (δ + 1)) × Fin (p ^ δ) => x.1.val) hab
    have hhigh : (a : ZMod (p ^ ν)).val / p ^ (ν - δ) =
        (b : ZMod (p ^ ν)).val / p ^ (ν - δ) :=
      congrArg (fun x : Fin (p ^ (δ + 1)) × Fin (p ^ δ) => x.2.val) hab
    have hdiff := root_difference_dvd_of_discr hdeg (Nat.prime_iff_prime_int.mp hp) hδν hD
      (by simpa only [Nat.cast_pow] using a.modulus_dvd_eval_val)
      (by simpa only [Nat.cast_pow] using b.modulus_dvd_eval_val)
      (by simpa only [Nat.cast_pow] using Nat.modEq_iff_dvd.mp hlow)
    have hmod : (a : ZMod (p ^ ν)).val % p ^ (ν - δ) =
        (b : ZMod (p ^ ν)).val % p ^ (ν - δ) :=
      Nat.modEq_iff_dvd.mpr (by simpa only [Nat.cast_pow] using hdiff)
    apply Subtype.ext
    apply ZMod.val_injective
    have ha := Nat.mod_add_div (a : ZMod (p ^ ν)).val (p ^ (ν - δ))
    have hb := Nat.mod_add_div (b : ZMod (p ^ ν)).val (p ^ (ν - δ))
    rw [hmod, hhigh] at ha
    exact ha.symm.trans hb
  calc
    rootCount Q (p ^ ν) ≤ Nat.card (Fin (p ^ (δ + 1)) × Fin (p ^ δ)) :=
      Nat.card_le_card_of_injective f hf
    _ = p ^ (2 * δ + 1) := by
      rw [Nat.card_prod]
      simp only [Nat.card_fin, ← pow_add]
      congr 1
      omega

theorem rootCount_prime_pow_le_factorization_bound {Q : ℤ[X]}
    (hdeg : 2 ≤ Q.natDegree) (hD : Q.discr ≠ 0) {p : ℕ} (hp : p.Prime) (ν : ℕ) :
    rootCount Q (p ^ ν) ≤ p ^ (2 * Q.discr.natAbs.factorization p + 1) := by
  apply rootCount_prime_pow_le_discr_bound hdeg hp
  simpa only [← Nat.cast_pow, Int.natCast_dvd] using
    Nat.pow_succ_factorization_not_dvd (Int.natAbs_ne_zero.mpr hD) hp

end NairTenenbaum
