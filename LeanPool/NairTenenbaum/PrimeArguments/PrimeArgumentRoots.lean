/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.CongruenceCount
public import LeanPool.NairTenenbaum.Progressions.AffineRootCounts

/-! # Adjoining the prime argument to the sieve polynomial

The proof of Theorem 3 sieves both `Q(t)` and `t`. Adjoining `X` adds exactly
one root at primes not dividing `Q(0)`. It can introduce fixed prime divisors;
the degree bound confines those new obstructions to small primes.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

theorem residueRootSet_mul_X (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) :
    let : NeZero p := ⟨hp.ne_zero⟩
    residueRootSet (Q * X) p = insert 0 (residueRootSet Q p) := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  ext a
  simp [residueRootSet, Polynomial.eval₂_mul, or_comm]

/-- The additional residue class is new precisely away from `Q(0)`. -/
theorem rootCount_mul_X_prime (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) :
    rootCount (Q * X) p = rootCount Q p +
      if p ∣ (Q.eval 0).natAbs then 0 else 1 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hzero : (0 : ZMod p) ∈ residueRootSet Q p ↔ p ∣ (Q.eval 0).natAbs := by
    simpa only [Int.cast_zero, Int.natCast_dvd] using cast_mem_residueRootSet Q p 0
  rw [← residueRootSet_card, residueRootSet_mul_X Q hp]
  by_cases h : p ∣ (Q.eval 0).natAbs
  · rw [insert_eq_of_mem (hzero.mpr h), residueRootSet_card, ite_eq_left h, add_zero]
  · rw [card_insert_of_notMem (fun H => h (hzero.mp H)), residueRootSet_card, ite_eq_right h]

theorem rootCount_mul_X_prime_le_degree_add_one {Q : ℤ[X]}
    (hQ : NoFixedPrimeDivisor Q) {p : ℕ} (hp : p.Prime) :
    rootCount (Q * X) p ≤ Q.natDegree + 1 := by
  rw [rootCount_mul_X_prime Q hp]
  have := rootCount_le_degree hQ hp
  split_ifs <;> omega

/-- No new fixed divisor occurs above the enlarged degree. -/
theorem rootCount_mul_X_prime_lt {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {p : ℕ} (hp : p.Prime) (hlarge : Q.natDegree + 1 < p) :
    rootCount (Q * X) p < p :=
  (rootCount_mul_X_prime_le_degree_add_one hQ hp).trans_lt hlarge

/-- The obstruction to applying Theorem 1 directly to the enlarged family is
real, even for a linear polynomial with constant term one. -/
theorem adjoining_X_can_introduce_fixed_prime :
    NoFixedPrimeDivisor (X + C 1 : ℤ[X]) ∧
      (X + C 1 : ℤ[X]).eval 0 ≠ 0 ∧
      ¬NoFixedPrimeDivisor ((X + C 1) * X : ℤ[X]) := by
  refine ⟨noFixedPrimeDivisor_X_add_C 1, by simp, ?_⟩
  intro h
  have H := h 2 Nat.prime_two
  rw [rootCount_mul_X_prime _ Nat.prime_two, rootCount_X_add_C] at H
  norm_num at H

/-- Local comparison responsible for the additional prime-sieving factor. -/
theorem sieveFactor_mul_X_le (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) :
    1 - (rootCount (Q * X) p : ℝ) / p ≤
      (1 - (rootCount Q p : ℝ) / p) *
        (if p ∣ (Q.eval 0).natAbs then 1 else 1 - 1 / (p : ℝ)) := by
  rw [rootCount_mul_X_prime Q hp]
  by_cases h : p ∣ (Q.eval 0).natAbs
  · simp [h]
  · simp only [ite_eq_right h, Nat.cast_add, Nat.cast_one]
    have hnonneg : 0 ≤ (rootCount Q p : ℝ) / p / p := by positivity
    calc
      1 - ((rootCount Q p : ℝ) + 1) / p =
          (1 - (rootCount Q p : ℝ) / p) * (1 - 1 / (p : ℝ)) -
            (rootCount Q p : ℝ) / p / p := by ring
      _ ≤ _ := sub_le_self _ hnonneg

/-- The same comparison with an arbitrary set of modulus primes omitted.
This is useful when the modulus contains the small fixed-prime obstructions. -/
theorem progressionSieveProduct_mul_X_le (Q : ℤ[X]) (n : ℕ) (x : ℝ) :
    progressionSieveProduct (Q * X) n x ≤ progressionSieveProduct Q n x *
      progressionSieveProduct X (n * (Q.eval 0).natAbs) x := by
  classical
  let S := (range (⌊x⌋₊ + 1)).filter Nat.Prime
  have hfilter : S.filter (fun p => ¬p ∣ n * (Q.eval 0).natAbs) =
      (S.filter (fun p => ¬p ∣ n)).filter (fun p => ¬p ∣ (Q.eval 0).natAbs) := by
    ext p
    by_cases hp : p ∈ S
    · have hprime := (mem_filter.mp hp).2
      simp only [mem_filter, hp, true_and, hprime.dvd_mul]
      tauto
    · simp [hp]
  unfold progressionSieveProduct
  change (∏ p ∈ S.filter (fun p => ¬p ∣ n), (1 - (rootCount (Q * X) p : ℝ) / p)) ≤ _
  rw [hfilter]
  conv_rhs => rhs; rw [prod_filter]
  rw [← prod_mul_distrib]
  apply prod_le_prod₀
  · intro p hp
    have hprime := (mem_filter.mp (mem_filter.mp hp).1).2
    exact sub_nonneg.mpr ((div_le_one (by exact_mod_cast hprime.pos)).mpr (by
      exact_mod_cast rootCount_le (Q * X) hprime.ne_zero))
  · intro p hp
    simpa only [rootCount_X, Nat.cast_one, ite_not] using
      sieveFactor_mul_X_le Q (mem_filter.mp (mem_filter.mp hp).1).2

end NairTenenbaum
