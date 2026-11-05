/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Polynomials.PrimitiveResidueRoots
public import LeanPool.NairTenenbaum.Sieve.BadPrimeRoots

/-! # Content after restriction to an arithmetic progression -/

@[expose] public section

namespace NairTenenbaum

open Polynomial

/-- The polynomial obtained by restricting to an arithmetic progression. -/
noncomputable def affineRestriction (Q : ℤ[X]) (M a : ℤ) : ℤ[X] := Q.comp (C M * X + C a)

theorem affineRestriction_eq_taylor_comp (Q : ℤ[X]) (M a : ℤ) :
    affineRestriction Q M a = (taylor a Q).comp (C M * X) := by
  simp only [affineRestriction, taylor_apply, comp_assoc, add_comp, X_comp, C_comp]

theorem affineRestriction_coeff (Q : ℤ[X]) (M a : ℤ) (i : ℕ) :
    (affineRestriction Q M a).coeff i = (taylor a Q).coeff i * M ^ i := by
  rw [affineRestriction_eq_taylor_comp, comp_C_mul_X_coeff]

theorem affineRestriction_coeff_zero (Q : ℤ[X]) (M a : ℤ) :
    (affineRestriction Q M a).coeff 0 = Q.eval a := by
  rw [affineRestriction_coeff, pow_zero, mul_one, taylor_coeff_zero]

theorem affineRestriction_coeff_one (Q : ℤ[X]) (M a : ℤ) :
    (affineRestriction Q M a).coeff 1 = Q.derivative.eval a * M := by
  rw [affineRestriction_coeff, pow_one, taylor_coeff_one]

theorem affineRestriction_content_not_dvd {Q : ℤ[X]} (hdeg : 2 ≤ Q.natDegree)
    {p M a : ℤ} (hp : Prime p) {m : ℕ} (hM : ¬ p ^ (m + 1) ∣ M)
    (hD : ¬ p ^ m ∣ Q.discr) : ¬ p ^ (2 * m) ∣ (affineRestriction Q M a).content := by
  intro hc
  have H (i : ℕ) : p ^ (2 * m) ∣ (affineRestriction Q M a).coeff i :=
    hc.trans (content_dvd_coeff i)
  have H₀ : p ^ m ∣ Q.eval a := by
    apply (pow_dvd_pow p (by omega : m ≤ 2 * m)).trans
    simpa only [affineRestriction_coeff_zero] using H 0
  have H₁ : p ^ m ∣ Q.derivative.eval a := by
    apply prime_pow_dvd_of_mul_not_dvd hp m m _ hM
    simpa only [← two_mul, affineRestriction_coeff_one] using H 1
  exact hD (dvd_discr_of_dvd_eval_and_derivative hdeg H₀ H₁)

theorem affineRestriction_primPart_high_coeff_dvd {Q : ℤ[X]} (hdeg : 2 ≤ Q.natDegree)
    {p : ℕ} (hp : p.Prime) {M a : ℤ} {m : ℕ}
    (hMp : (p : ℤ) ^ m ∣ M) (hM : ¬ (p : ℤ) ^ (m + 1) ∣ M)
    (hD : ¬ (p : ℤ) ^ m ∣ Q.discr) {i : ℕ} (hi : 2 ≤ i) :
    (p : ℤ) ∣ (affineRestriction Q M a).primPart.coeff i := by
  let R := affineRestriction Q M a
  have hc := affineRestriction_content_not_dvd hdeg (Nat.prime_iff_prime_int.mp hp) hM hD (a := a)
  have hc₀ : R.content ≠ 0 := by intro h; exact hc (h ▸ dvd_zero _)
  let e := R.content.natAbs.factorization p
  have he : (p : ℤ) ^ e ∣ R.content := by
    simpa only [← Nat.cast_pow, Int.natCast_dvd] using Nat.ordProj_dvd R.content.natAbs p
  have he' : ¬ (p : ℤ) ^ (e + 1) ∣ R.content := by
    simpa only [← Nat.cast_pow, Int.natCast_dvd] using
      Nat.pow_succ_factorization_not_dvd (Int.natAbs_ne_zero.mpr hc₀) hp
  have he2 : e < 2 * m := by
    by_contra! hh
    exact hc ((pow_dvd_pow (p : ℤ) hh).trans he)
  have Hcoeff : (p : ℤ) ^ (2 * m) ∣ R.coeff i := by
    rw [affineRestriction_coeff]
    apply dvd_mul_of_dvd_right
    apply (show (p : ℤ) ^ (2 * m) ∣ M ^ 2 by
      simpa only [← pow_mul, mul_comm m 2] using pow_dvd_pow_of_dvd hMp 2).trans
    exact pow_dvd_pow M hi
  have Hsplit : R.coeff i = R.primPart.coeff i * R.content := by
    conv_lhs => rw [R.eq_C_content_mul_primPart]
    rw [coeff_C_mul, mul_comm]
  have HH : (p : ℤ) ^ (1 + e) ∣ R.primPart.coeff i * R.content := by
    rw [← Hsplit]
    exact (pow_dvd_pow (p : ℤ) (by omega)).trans Hcoeff
  simpa only [pow_one] using prime_pow_dvd_of_mul_not_dvd (Nat.prime_iff_prime_int.mp hp) 1 e HH he'

end NairTenenbaum
