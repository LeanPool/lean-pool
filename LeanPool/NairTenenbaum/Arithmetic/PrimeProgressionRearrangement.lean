/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.DivisorSumRearrangement

/-! # Averaged prime progressions as divisor windows

This is the finite rearrangement needed in Corollary 9. The condition `a≤x`
excludes the diagonal prime `p=a`, whose zero difference has every modulus
as a divisor. It holds eventually for each fixed integer residue `a`.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- The usual prime count in a residue class, with a real upper endpoint. -/
noncomputable def primeProgressionCount (x : ℝ) (q : ℕ) (a : ℤ) : ℕ :=
  ((Icc 0 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ Int.ModEq (q : ℤ) (p : ℤ) a)).card

theorem primeProgressionCount_mono {x z : ℝ} (hxz : x ≤ z) (q : ℕ) (a : ℤ) :
    primeProgressionCount x q a ≤ primeProgressionCount z q a := by
  apply card_le_card
  intro p hp
  obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hpI).1,
    (mem_Icc.mp hpI).2.trans (Nat.floor_mono hxz)⟩, hpP⟩

theorem primeProgressionCount_sub_eq {x y : ℝ} (hy : 0 ≤ y) (q : ℕ) (a : ℤ) :
    primeProgressionCount (x + y) q a - primeProgressionCount x q a =
      ((shortInterval x y).filter (fun p : ℕ => p.Prime ∧ Int.ModEq (q : ℤ) (p : ℤ) a)).card := by
  have H : ((Icc 0 ⌊x + y⌋₊).filter (fun p : ℕ => p.Prime ∧ Int.ModEq (q : ℤ) (p : ℤ) a)) \
      ((Icc 0 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ Int.ModEq (q : ℤ) (p : ℤ) a)) =
      (shortInterval x y).filter (fun p : ℕ => p.Prime ∧ Int.ModEq (q : ℤ) (p : ℤ) a) := by
    ext p
    simp only [shortInterval, mem_sdiff, mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨⟨_, hb⟩, hP⟩, hn⟩
      refine ⟨⟨?_, hb⟩, hP⟩
      by_contra! h
      exact hn ⟨⟨Nat.zero_le _, h⟩, hP⟩
    · rintro ⟨⟨ha, hb⟩, hP⟩
      exact ⟨⟨⟨Nat.zero_le _, hb⟩, hP⟩, fun H => (not_le_of_gt ha) H.1.2⟩
  unfold primeProgressionCount
  rw [← H, card_sdiff_of_subset]
  intro p hp
  obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hpI).1,
    (mem_Icc.mp hpI).2.trans (Nat.floor_mono (by linarith))⟩, hpP⟩

theorem int_modEq_iff_dvd_natAbs_sub (q : ℕ) (n a : ℤ) :
    Int.ModEq (q : ℤ) n a ↔ q ∣ (n - a).natAbs := by
  rw [Int.modEq_iff_dvd, ← dvd_neg, neg_sub, Int.natCast_dvd]

/-- The dyadic average of the prime-count differences in Corollary 9. -/
noncomputable def dyadicPrimeProgressionSum (K : ℝ) (a : ℤ) (x y : ℝ) : ℝ :=
  ∑ q ∈ shortInterval K K,
    ((primeProgressionCount (x + y) q a : ℝ) - (primeProgressionCount x q a : ℝ))

theorem dyadicPrimeProgressionSum_eq_divisor_sum {K x y : ℝ} (a : ℤ)
    (hK : 0 < K) (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : (a : ℝ) ≤ x) :
    dyadicPrimeProgressionSum K a x y =
      ∑ p ∈ (shortInterval x y).filter Nat.Prime,
        ((((p : ℤ) - a).natAbs.divisors.filter
          (fun q : ℕ => K < q ∧ (q : ℝ) ≤ 2 * K)).card : ℝ) := by
  classical
  have hnonzero (p : ℕ) (hp : p ∈ shortInterval x y) : (p : ℤ) - a ≠ 0 := by
    have hxp : x < (p : ℝ) := (Nat.floor_lt hx).mp (mem_Ioc.mp hp).1
    have H : (a : ℝ) < p := ha.trans_lt hxp
    have H' : a < (p : ℤ) := by exact_mod_cast H
    omega
  unfold dyadicPrimeProgressionSum
  simp_rw [← Nat.cast_sub (primeProgressionCount_mono (show x ≤ x + y by linarith) _ _),
    primeProgressionCount_sub_eq hy]
  have Hswap : (∑ q ∈ shortInterval K K,
      ((shortInterval x y).filter (fun p : ℕ => p.Prime ∧ Int.ModEq (q : ℤ) (p : ℤ) a)).card) =
      ∑ p ∈ (shortInterval x y).filter Nat.Prime,
        ((shortInterval K K).filter (fun q : ℕ => Int.ModEq (q : ℤ) (p : ℤ) a)).card := by
    simp_rw [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    by_cases hprime : p.Prime <;> simp [hprime]
  rw [← Nat.cast_sum, Hswap, Nat.cast_sum]
  apply sum_congr rfl
  intro p hp
  congr 2
  ext q
  have hp₀ : ((p : ℤ) - a).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hnonzero p (mem_filter.mp hp).1)
  simp only [mem_filter, Nat.mem_divisors,
    int_modEq_iff_dvd_natAbs_sub, shortInterval, mem_Ioc]
  rw [Nat.floor_lt hK.le, Nat.le_floor_iff (by linarith : 0 ≤ K + K),
    show K + K = 2 * K by ring]
  constructor
  · rintro ⟨hwindow, hdvd⟩
    exact ⟨⟨hdvd, hp₀⟩, hwindow⟩
  · rintro ⟨⟨hdvd, _⟩, hwindow⟩
    exact ⟨hwindow, hdvd⟩

/-- Uniformity in the dyadic modulus cutoff is preserved in the reduction
to Hooley's function at shifted primes. -/
theorem dyadicPrimeProgressionSum_le_hooley_sum {K x y : ℝ} (a : ℤ)
    (hK : 0 < K) (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : (a : ℝ) ≤ x) :
    dyadicPrimeProgressionSum K a x y ≤
      ∑ p ∈ (shortInterval x y).filter Nat.Prime, (hooleyDelta ((p : ℤ) - a).natAbs : ℝ) := by
  rw [dyadicPrimeProgressionSum_eq_divisor_sum a hK hx hy ha]
  apply sum_le_sum
  intro p _
  exact_mod_cast dyadic_divisors_le_delta (n := ((p : ℤ) - a).natAbs) hK

end NairTenenbaum
