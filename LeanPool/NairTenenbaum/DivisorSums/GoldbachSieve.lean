/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Contributions.RealIntervalBounds
public import LeanPool.NairTenenbaum.Polynomials.ShiftedLinearSystem

/-! # The two-prime sieve for Goldbach representations

Representations with either prime below the sieve cutoff are counted
separately. The remaining representations satisfy the enlarged polynomial
sieve even when the enlarged polynomial has a small fixed prime.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

/-- The primes forming the Goldbach pairs in the specified range. -/
noncomputable def goldbachPrimes (N : ℕ) (x y : ℝ) : Finset ℕ :=
  (shortInterval x y).filter (fun p => p.Prime ∧ (N - p).Prime)

/-- The number of Goldbach primes in the specified range. -/
noncomputable def goldbachCount (N : ℕ) (x y : ℝ) : ℕ :=
  (goldbachPrimes N x y).card

/-- The Goldbach primes remaining after the small-prime cutoff. -/
noncomputable def largeGoldbachPrimes (N : ℕ) (x y z : ℝ) : Finset ℕ :=
  (goldbachPrimes N x y).filter (fun p => z < p ∧ z < (N - p : ℕ))

theorem goldbachPrime_lt {N p : ℕ} {x y : ℝ} (hp : p ∈ goldbachPrimes N x y) : p < N :=
  Nat.sub_pos_iff_lt.mp (mem_filter.mp hp).2.2.pos

theorem goldbachCount_le_large_add (N : ℕ) (x y : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    (goldbachCount N x y : ℝ) ≤ (largeGoldbachPrimes N x y z).card + 2 * (z + 1) := by
  classical
  let s := range (⌊z⌋₊ + 1)
  have hcover : goldbachPrimes N x y ⊆ largeGoldbachPrimes N x y z ∪ s ∪
      s.image (fun q => N - q) := by
    intro p hp
    by_cases hzp : z < p
    · by_cases hzq : z < (N - p : ℕ)
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hp, hzp, hzq⟩))
      · apply mem_union_right
        apply mem_image.mpr
        refine ⟨N - p, ?_, Nat.sub_sub_self (goldbachPrime_lt hp).le⟩
        exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff hz).mpr (le_of_not_gt hzq)))
    · apply mem_union_left
      apply mem_union_right
      exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff hz).mpr (le_of_not_gt hzp)))
  have H : goldbachCount N x y ≤ (largeGoldbachPrimes N x y z).card + 2 * (⌊z⌋₊ + 1) := by
    calc
      _ ≤ (largeGoldbachPrimes N x y z ∪ s ∪ s.image (fun q => N - q)).card := card_le_card hcover
      _ ≤ (largeGoldbachPrimes N x y z).card + s.card + (s.image (fun q => N - q)).card :=
        (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
      _ ≤ (largeGoldbachPrimes N x y z).card + s.card + s.card :=
        Nat.add_le_add_left (card_image_le) _
      _ = _ := by simp [s]; omega
  have H' : (goldbachCount N x y : ℝ) ≤ (largeGoldbachPrimes N x y z).card +
      2 * ((⌊z⌋₊ : ℝ) + 1) := by exact_mod_cast H
  linarith [Nat.floor_le hz]

theorem goldbach_polynomial_natAbs {N p : ℕ} (hp : p ≤ N) :
    ((X + C (-(N : ℤ)) : ℤ[X]).eval (p : ℤ)).natAbs = N - p := by
  rw [eval_add, eval_X, eval_C]
  change Int.natAbs ((p : ℤ) - N) = N - p
  rw [← Int.natAbs_neg, neg_sub, ← Nat.cast_sub hp, Int.natAbs_natCast]

theorem largeGoldbachPrimes_card_le_sifted (N : ℕ) (x y : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    (largeGoldbachPrimes N x y z).card ≤
      conditionalPolynomialSiftedCount ((X + C (-(N : ℤ))) * X)
        (primeArgumentSieveModulus (X + C (-(N : ℤ))) 1 1 z)
        (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i)
        (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ) := by
  classical
  rw [← card_image_of_injective _ (show Function.Injective (fun p : ℕ => (p : ℤ)) from
    fun _ _ h => Int.natCast_inj.mp h)]
  apply card_le_card
  intro t ht
  obtain ⟨p, hp, rfl⟩ := mem_image.mp ht
  obtain ⟨hpg, hzp, hzq⟩ := mem_filter.mp hp
  have hpN := (goldbachPrime_lt hpg).le
  obtain ⟨hpinterval, hpprime, hqprime⟩ := mem_filter.mp hpg
  apply mem_filter.mpr
  constructor
  · apply mem_filter.mpr
    constructor
    · rw [← shortInterval_natCast_image]
      exact mem_image.mpr ⟨p, hpinterval, rfl⟩
    · exact fun i => Fin.elim0 i
  · rw [eval_mul, eval_X, Int.natAbs_mul, Int.natAbs_natCast, goldbach_polynomial_natAbs hpN]
    exact (primeArgumentSieveModulus_coprime_prime _ 1 1 hz hqprime hzq).mul_right
      (primeArgumentSieveModulus_coprime_prime _ 1 1 hz hpprime hzp)

/-- A two-prime upper bound before the cutoff is chosen. The constant is
absolute; all dependence on the represented integer is explicit. -/
theorem exists_goldbach_sieve_bound :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (N : ℕ), N ≠ 0 → ∀ (x y z : ℝ), 0 ≤ x → 2 ≤ y → y ≤ x →
      2 ≤ z → 16 ≤ Real.log z →
      (goldbachCount N x y : ℝ) ≤
        K * (((N : ℝ) / N.totient) * y / (Real.log z) ^ 2 + z ^ (9 : ℝ)) := by
  obtain ⟨K, hK, H⟩ := exists_primeArgument_conditional_sieve_bound 1 (η := 1 / 8) (by norm_num)
  refine ⟨2 * K + 4, by linarith, ?_⟩
  intro N hN x y z hx hy hyx hz hzlog
  let Q : ℤ[X] := X + C (-(N : ℤ))
  obtain ⟨hab, _, hlen, _⟩ := shortInterval_endpoint_bounds hx hy hyx
  have HQ : NoFixedPrimeDivisor Q := noFixedPrimeDivisor_X_add_C _
  have Hzero : Q.eval 0 ≠ 0 := by
    simp only [Q, eval_add, eval_X, eval_C, zero_add, neg_ne_zero]
    exact_mod_cast hN
  have Hsieve := H Q HQ Hzero (by dsimp [Q]; rw [natDegree_X_add_C])
    0 (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i)
    (by intro i; exact Fin.elim0 i) _ _ z hab hz hzlog
  have Hmass : mass (fun i : Fin 0 => (Fin.elim0 i : ℕ+)) = 1 := by simp [mass]
  simp only [Hmass, totientTwist_one, Fin.prod_univ_zero, mul_one,
    Q, eval_add, eval_X, eval_C, zero_add, Int.natAbs_neg, Int.natAbs_natCast,
    sieveProduct_X_add_C, Int.cast_natCast] at Hsieve
  norm_num only [Nat.cast_one] at Hsieve
  have Hcount := (show ((largeGoldbachPrimes N x y z).card : ℝ) ≤ _ from
    Nat.cast_le.mpr (largeGoldbachPrimes_card_le_sifted N x y (by linarith))).trans Hsieve
  have hL : 0 ≤ (⌊x + y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) := by exact_mod_cast sub_nonneg.mpr hab
  have htwist : totientTwist 1 N = (N : ℝ) / N.totient := by simp [totientTwist]
  have hratio : 0 ≤ (N : ℝ) / N.totient := by positivity
  have hlog : 0 < Real.log z := by linarith
  have Hmain : ((⌊x + y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ)) * sieveProduct X z * totientTwist 1 N /
      Real.log z ≤ 2 * (((N : ℝ) / N.totient) * y / (Real.log z) ^ 2) := by
    rw [htwist]
    have Hb := mul_le_mul hlen (sieveProduct_X_le_inv_log (by linarith))
      (sieveProduct_pos noFixedPrimeDivisor_X z).le (by linarith : 0 ≤ 2 * y)
    have Hb' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right Hb hratio) hlog.le
    exact Hb'.trans_eq (by ring)
  have hzpower : z ≤ z ^ (9 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by linarith : 1 ≤ z) (by norm_num : (1 : ℝ) ≤ 9)
  have hmain : 0 ≤ ((N : ℝ) / N.totient) * y / (Real.log z) ^ 2 :=
    div_nonneg (mul_nonneg hratio (by linarith)) (sq_nonneg _)
  simp only [one_mul] at Hcount
  have Hlarge := Hcount.trans (mul_le_mul_of_nonneg_left
    (add_le_add Hmain (le_refl (z ^ (9 : ℝ)))) (by linarith : 0 ≤ K))
  have Hsplit := goldbachCount_le_large_add N x y (by linarith : 0 ≤ z)
  nlinarith

end NairTenenbaum
