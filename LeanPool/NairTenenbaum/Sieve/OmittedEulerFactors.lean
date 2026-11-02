/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.TotientTwist
public import Mathlib.Algebra.Order.Star.Real

/-! # Euler factors omitted at primes dividing the conditioning modulus

The omitted factors are bounded by a uniform constant times `(n/φ(n))^g`.
The quotient of the local factors differs from one by `O(g²/p²)` outside
the finitely many primes at most `2g`.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Nat Real Polynomial

theorem one_sub_pow_le_quadratic (g : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    (1 - t) ^ g ≤ 1 - (g : ℝ) * t + (g : ℝ) ^ 2 * t ^ 2 := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [pow_succ]
    have H := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr ht₁)
    push_cast
    nlinarith [mul_nonneg (sq_nonneg (g : ℝ)) (mul_nonneg (sq_nonneg t) ht)]

/-- The correction ratio for the Euler factors omitted from the sieve. -/
noncomputable def omittedEulerRatio (Q : ℤ[X]) (g p : ℕ) : ℝ :=
  (1 - 1 / (p : ℝ)) ^ g / (1 - (rootCount Q p : ℝ) / p)

theorem omittedEulerRatio_nonneg {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q) (g : ℕ)
    {p : ℕ} (hp : p.Prime) : 0 ≤ omittedEulerRatio Q g p := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hb : 0 ≤ 1 - 1 / (p : ℝ) := sub_nonneg.mpr ((div_le_one hp₀).mpr (by
    exact_mod_cast hp.one_le))
  have hden : 0 < 1 - (rootCount Q p : ℝ) / p := sub_pos.mpr ((div_lt_one hp₀).mpr (by
    exact_mod_cast hQ p hp))
  exact div_nonneg (pow_nonneg hb _) hden.le

theorem omittedEulerRatio_le_prime {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q) (g : ℕ)
    {p : ℕ} (hp : p.Prime) : omittedEulerRatio Q g p ≤ p := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hb : 0 ≤ 1 - 1 / (p : ℝ) := sub_nonneg.mpr ((div_le_one hp₀).mpr (by
    exact_mod_cast hp.one_le))
  have hb₁ : 1 - 1 / (p : ℝ) ≤ 1 := sub_le_self _ (by positivity)
  have hnum := pow_le_one₀ hb hb₁ (n := g)
  have hr : (rootCount Q p : ℝ) + 1 ≤ p := by exact_mod_cast hQ p hp
  have hden : 0 < 1 - (rootCount Q p : ℝ) / p := sub_pos.mpr ((div_lt_one hp₀).mpr (by
    exact_mod_cast hQ p hp))
  apply (div_le_iff₀ hden).mpr
  have heq : (p : ℝ) * (1 - (rootCount Q p : ℝ) / p) = p - rootCount Q p := by field_simp
  rw [heq]
  linarith

theorem omittedEulerRatio_le_exp {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {g p : ℕ} (hg : Q.natDegree ≤ g) (hp : p.Prime) (hlarge : 2 * g ≤ p) :
    omittedEulerRatio Q g p ≤ Real.exp (2 * (g : ℝ) ^ 2 / (p : ℝ) ^ 2) := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have ht : 0 ≤ 1 / (p : ℝ) := by positivity
  have ht₁ : 1 / (p : ℝ) ≤ 1 := (div_le_one hp₀).mpr hp₁
  have hr : (rootCount Q p : ℝ) / p ≤ (g : ℝ) / p :=
    div_le_div_of_nonneg_right (by exact_mod_cast (rootCount_le_degree hQ hp).trans hg) hp₀.le
  have hhalf : (g : ℝ) / p ≤ 1 / 2 := (div_le_iff₀ hp₀).mpr (by
    have H : 2 * (g : ℝ) ≤ p := by exact_mod_cast hlarge
    linarith)
  have hden : 0 < 1 - (rootCount Q p : ℝ) / p := by linarith
  have H := one_sub_pow_le_quadratic g ht ht₁
  have H' : (1 - 1 / (p : ℝ)) ^ g ≤ 1 - (g : ℝ) / p + (g : ℝ) ^ 2 / (p : ℝ) ^ 2 := by
    convert H using 1
    ring
  have hratio : omittedEulerRatio Q g p ≤ 1 + 2 * (g : ℝ) ^ 2 / (p : ℝ) ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    have hq : 0 ≤ (g : ℝ) ^ 2 / (p : ℝ) ^ 2 := by positivity
    have Hmul := mul_le_mul_of_nonneg_left (hr.trans hhalf) hq
    rw [mul_div_assoc]
    generalize (g : ℝ) ^ 2 / (p : ℝ) ^ 2 = u at H' hq Hmul ⊢
    nlinarith
  exact hratio.trans (by
    simpa only [add_comm] using Real.add_one_le_exp (2 * (g : ℝ) ^ 2 / (p : ℝ) ^ 2))

/-- A uniform upper bound for the omitted Euler-factor ratio. -/
noncomputable def omittedEulerBound (g : ℕ) : ℝ :=
  (2 * (g : ℝ) + 1) ^ (2 * g + 1) *
    Real.exp (2 * (g : ℝ) ^ 2 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2)

theorem omittedEulerBound_pos (g : ℕ) : 0 < omittedEulerBound g := by
  unfold omittedEulerBound
  positivity

theorem omittedEulerRatio_prod_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {g : ℕ} (hg : Q.natDegree ≤ g) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, omittedEulerRatio Q g p) ≤ omittedEulerBound g := by
  let M : ℝ := 2 * (g : ℝ) + 1
  have hM : 1 ≤ M := by dsimp [M]; linarith [Nat.cast_nonneg (α := ℝ) g]
  have hlocal (p : ℕ) (hp : p ∈ S) : omittedEulerRatio Q g p ≤
      (if p ≤ 2 * g then M else 1) * Real.exp (2 * (g : ℝ) ^ 2 / (p : ℝ) ^ 2) := by
    split_ifs with h
    · have H : omittedEulerRatio Q g p ≤ M :=
        (omittedEulerRatio_le_prime hQ g (hS p hp)).trans (by
          dsimp [M]
          exact_mod_cast h.trans (Nat.le_succ _))
      have he : 1 ≤ Real.exp (2 * (g : ℝ) ^ 2 / (p : ℝ) ^ 2) := Real.one_le_exp_iff.mpr (by
        positivity)
      exact H.trans (by nlinarith)
    · rw [one_mul]
      exact omittedEulerRatio_le_exp hQ hg (hS p hp) (Nat.le_of_lt (Nat.lt_of_not_ge h))
  have hsmall : (∏ p ∈ S, if p ≤ 2 * g then M else 1) ≤ M ^ (2 * g + 1) := by
    have hcard : (S.filter (· ≤ 2 * g)).card ≤ 2 * g + 1 := by
      apply le_trans (Finset.card_le_card (t := Finset.range (2 * g + 1)) ?_) (by simp)
      intro p hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2)
    simpa only [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const] using
        pow_le_pow_right₀ hM hcard
  have hsum : (∑ p ∈ S, 2 * (g : ℝ) ^ 2 / (p : ℝ) ^ 2) ≤
      2 * (g : ℝ) ^ 2 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
    have H := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).sum_le_tsum S (fun _
        _ => by
      positivity)
    have H' := mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ 2 * (g : ℝ) ^ 2)
    simpa only [Finset.mul_sum, mul_one_div] using H'
  calc
    _ ≤ ∏ p ∈ S, (if p ≤ 2 * g then M else 1) * Real.exp (2 * (g : ℝ) ^ 2 / (p : ℝ) ^ 2) :=
      Finset.prod_le_prod₀ (fun p hp => omittedEulerRatio_nonneg hQ g (hS p hp)) hlocal
    _ = (∏ p ∈ S, if p ≤ 2 * g then M else 1) * Real.exp (∑ p ∈ S, 2 * (g : ℝ) ^ 2 / (p : ℝ) ^ 2)
        := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    _ ≤ _ := mul_le_mul hsmall (Real.exp_le_exp.mpr hsum) (Real.exp_nonneg _) (pow_nonneg
        (zero_le_one.trans hM) _)

theorem totientTwist_one_le (g : ℕ) {n : ℕ} (hn : n ≠ 0) : 1 ≤ totientTwist g n := by
  apply one_le_pow₀
  apply (one_le_div (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
  exact_mod_cast Nat.totient_le n

theorem totientTwist_eq_prod (g : ℕ) {n : ℕ} (hn : n ≠ 0) :
    totientTwist g n = ∏ p ∈ n.primeFactors, totientTwist g p := by
  rw [Nat.multiplicative_factorization (totientTwist g) (fun _ _ h => totientTwist_mul g h)
    (totientTwist_one g) hn]
  simp only [Finsupp.prod, Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  obtain ⟨ν, hν⟩ := Nat.exists_eq_succ_of_ne_zero
    (hprime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)).ne'
  rw [hν, totientTwist_prime_pow g hprime, totientTwist_prime g hprime]

theorem omittedEulerRatio_mul_totient (Q : ℤ[X]) (g : ℕ)
    {p : ℕ} (hp : p.Prime) :
    omittedEulerRatio Q g p * totientTwist g p = (1 - (rootCount Q p : ℝ) / p)⁻¹ := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp₁ : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hb : 1 - 1 / (p : ℝ) ≠ 0 := (sub_pos.mpr ((div_lt_one hp₀).mpr hp₁)).ne'
  have heq : (p : ℝ) / (p - 1) = (1 - 1 / (p : ℝ))⁻¹ := by field_simp
  rw [omittedEulerRatio, totientTwist_prime g hp, heq, inv_pow]
  rw [div_mul_eq_mul_div, mul_inv_cancel₀ (pow_ne_zero _ hb), one_div]

/-- The missing Euler factors over any subset of the modulus prime factors
are controlled by the standard totient correction and a degree-only constant. -/
theorem omittedEulerFactors_le {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {g n : ℕ} (hg : Q.natDegree ≤ g) (hn : n ≠ 0)
    (S : Finset ℕ) (hS : S ⊆ n.primeFactors) :
    (∏ p ∈ S, (1 - (rootCount Q p : ℝ) / p)⁻¹) ≤ omittedEulerBound g * totientTwist g n := by
  have hprime : ∀ p ∈ S, p.Prime := fun _ hp => Nat.prime_of_mem_primeFactors (hS hp)
  have htwist : (∏ p ∈ S, totientTwist g p) ≤ totientTwist g n := by
    rw [totientTwist_eq_prod g hn]
    apply Finset.prod_le_prod_of_subset_of_one_le₀ hS
    · intro p _
      exact totientTwist_nonneg g p
    · intro p hp _
      exact totientTwist_one_le g (Nat.prime_of_mem_primeFactors hp).ne_zero
  calc
    _ = (∏ p ∈ S, omittedEulerRatio Q g p) * ∏ p ∈ S, totientTwist g p := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      exact (omittedEulerRatio_mul_totient Q g (hprime p hp)).symm
    _ ≤ _ := mul_le_mul (omittedEulerRatio_prod_le hQ hg S hprime) htwist
      (Finset.prod_nonneg (fun p _ => totientTwist_nonneg g p)) (omittedEulerBound_pos g).le

end NairTenenbaum
