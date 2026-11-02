/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.CongruenceCount
public import LeanPool.NairTenenbaum.Arithmetic.PrimePowerThreshold

/-! # Counting values divisible by unusually large powers of small primes -/

@[expose] public section

namespace NairTenenbaum

open Polynomial Finset

/-- The elementary congruence estimate with the error absorbed by the interval
length. -/
theorem polynomialCongruenceCount_le_twice {Q : ℤ[X]} {q : ℕ} (hq : 0 < q)
    {a b : ℤ} (hab : a ≤ b) (hlevel : (q : ℝ) ≤ (b : ℝ) - a) :
    (polynomialCongruenceCount Q q a b : ℝ) ≤
      2 * ((b : ℝ) - a) * rootCount Q q / q := by
  have H := (abs_le.mp (polynomialCongruenceCount_error Q hq a b hab)).2
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast hq
  have hr : (rootCount Q q : ℝ) ≤ ((b : ℝ) - a) * rootCount Q q / q := by
    apply (le_div_iff₀ hq₀).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlevel (Nat.cast_nonneg (rootCount Q q) : (0 : ℝ) ≤ _)]
  calc
    _ ≤ 2 * (((b : ℝ) - a) * rootCount Q q / q) := by linarith
    _ = _ := by ring

/-- A union bound over any finite family of polynomial congruences. -/
theorem polynomialCongruenceUnion_card_le {ι : Type*} (S : Finset ι)
    (Q : ι → ℤ[X]) (q : ι → ℕ) (a b : ℤ) :
    ((Finset.Ioc a b).filter (fun t => ∃ i ∈ S, (q i : ℤ) ∣ (Q i).eval t)).card ≤
      ∑ i ∈ S, polynomialCongruenceCount (Q i) (q i) a b := by
  classical
  have heq : (Finset.Ioc a b).filter (fun t => ∃ i ∈ S, (q i : ℤ) ∣ (Q i).eval t) =
      S.biUnion (fun i => (Finset.Ioc a b).filter (fun t => (q i : ℤ) ∣ (Q i).eval t)) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨ht, i, hi, hd⟩
      exact ⟨i, hi, ht, hd⟩
    · rintro ⟨i, hi, ht, hd⟩
      exact ⟨ht, i, hi, hd⟩
  rw [heq]
  exact Finset.card_biUnion_le

/-- The finite set of primes at most the real cutoff. -/
noncomputable def smallPrimes (z : ℝ) : Finset ℕ :=
  (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime

theorem smallPrimes_le {z : ℝ} (hz : 0 ≤ z) {p : ℕ} (hp : p ∈ smallPrimes z) :
    (p : ℝ) ≤ z := (Nat.le_floor_iff hz).mp
      (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hp).1))

theorem smallPrimes_card_le {z : ℝ} (hz : 1 ≤ z) : ((smallPrimes z).card : ℝ) ≤ 2 * z := by
  have H : (smallPrimes z).card ≤ ⌊z⌋₊ + 1 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
  have H' : ((smallPrimes z).card : ℝ) ≤ ⌊z⌋₊ + 1 := by exact_mod_cast H
  have H'' := Nat.floor_le (zero_le_one.trans hz)
  linarith

/-- Values divisible by a prime power exceeding the threshold for some small prime. -/
noncomputable def primePowerExceptionalSet {r : ℕ} (R : Fin r → ℤ[X])
    (z T : ℝ) (a b : ℤ) : Finset ℤ := by
  classical
  exact (Finset.Ioc a b).filter (fun t => ∃ p ∈ smallPrimes z, ∃ i : Fin r,
    (p ^ firstPowerAbove p T : ℤ) ∣ (R i).eval t)

/-- The large-prime-power exceptional set has density at most a constant
multiple of `z/T`. This does not assume independence of the coordinates. -/
theorem primePowerExceptionalSet_card_le {r : ℕ} (R : Fin r → ℤ[X])
    {z T M : ℝ} (hz : 1 ≤ z) (hT : 1 ≤ T) (hM : 0 ≤ M)
    (hroot : ∀ p ∈ smallPrimes z, ∀ i : Fin r,
      (rootCount (R i) (p ^ firstPowerAbove p T) : ℝ) ≤ M)
    {a b : ℤ} (hab : a ≤ b) (hlevel : z * T ≤ (b : ℝ) - a) :
    ((primePowerExceptionalSet R z T a b).card : ℝ) ≤
      4 * ((b : ℝ) - a) * (r : ℝ) * M * z / T := by
  let S := (smallPrimes z) ×ˢ (Finset.univ : Finset (Fin r))
  have heq : primePowerExceptionalSet R z T a b =
      (Finset.Ioc a b).filter (fun t => ∃ v ∈ S,
        ((v.1 ^ firstPowerAbove v.1 T : ℕ) : ℤ) ∣ (R v.2).eval t) := by
    ext t
    simp only [primePowerExceptionalSet, S, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, and_true, Prod.exists, Nat.cast_pow]
    constructor
    · rintro ⟨ht, p, hp, i, hi⟩
      exact ⟨ht, p, i, hp, hi⟩
    · rintro ⟨ht, p, i, hp, hi⟩
      exact ⟨ht, p, hp, i, hi⟩
  have hL : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  have hb (v : ℕ × Fin r) (hv : v ∈ S) :
      (polynomialCongruenceCount (R v.2) (v.1 ^ firstPowerAbove v.1 T) a b : ℝ) ≤
      2 * ((b : ℝ) - a) * M / T := by
    have hp := (Finset.mem_filter.mp (Finset.mem_product.mp hv).1).2
    have hpz := smallPrimes_le (zero_le_one.trans hz) (Finset.mem_product.mp hv).1
    have hq : 0 < v.1 ^ firstPowerAbove v.1 T := pow_pos hp.pos _
    have hq₀ : (0 : ℝ) < (v.1 ^ firstPowerAbove v.1 T : ℕ) := by exact_mod_cast hq
    have hqt : T < (v.1 : ℝ) ^ firstPowerAbove v.1 T := firstPowerAbove_spec hp.one_lt T
    have hql : ((v.1 ^ firstPowerAbove v.1 T : ℕ) : ℝ) ≤ (b : ℝ) - a := by
      rw [Nat.cast_pow]
      exact (firstPowerAbove_upper hp.one_lt hT).trans
        ((mul_le_mul_of_nonneg_right hpz (zero_le_one.trans hT)).trans hlevel)
    calc
      _ ≤ 2 * ((b : ℝ) - a) * rootCount (R v.2) (v.1 ^ firstPowerAbove v.1 T) /
          (v.1 ^ firstPowerAbove v.1 T : ℕ) := polynomialCongruenceCount_le_twice hq hab hql
      _ ≤ 2 * ((b : ℝ) - a) * M / (v.1 ^ firstPowerAbove v.1 T : ℕ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hroot v.1 (Finset.mem_product.mp hv).1 v.2) (by
            positivity)) hq₀.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by linarith : 0 < T)
        (by exact_mod_cast hqt.le)
  rw [heq]
  calc
    _ ≤ ∑ v ∈ S, (polynomialCongruenceCount (R v.2) (v.1 ^ firstPowerAbove v.1 T) a b : ℝ) := by
      exact_mod_cast polynomialCongruenceUnion_card_le S (fun v => R v.2)
        (fun v => v.1 ^ firstPowerAbove v.1 T) a b
    _ ≤ ∑ _v ∈ S, 2 * ((b : ℝ) - a) * M / T := Finset.sum_le_sum hb
    _ = ((smallPrimes z).card : ℝ) * r * (2 * ((b : ℝ) - a) * M / T) := by
      simp only [Finset.sum_const, nsmul_eq_mul, S, Finset.card_product, Finset.card_univ,
        Fintype.card_fin, Nat.cast_mul]
    _ ≤ (2 * z) * r * (2 * ((b : ℝ) - a) * M / T) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (smallPrimes_card_le hz) (Nat.cast_nonneg _)) (by positivity)
    _ = _ := by ring

end NairTenenbaum
