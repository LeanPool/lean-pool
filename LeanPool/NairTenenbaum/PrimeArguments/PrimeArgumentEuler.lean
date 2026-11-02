/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentRoots
public import LeanPool.NairTenenbaum.Sieve.OmittedEulerFactors
public import Mathlib.NumberTheory.Harmonic.Bounds

/-! # The extra logarithm in the prime-argument Euler product

The elementary harmonic-series argument gives the upper bound needed in
Theorem 3, without the prime number theorem or an asymptotic Mertens theorem.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

theorem reciprocal_prime_powers_hasSum {p : ℕ} (hp : p.Prime) :
    HasSum (fun ν : ℕ => ((p ^ ν : ℕ) : ℝ)⁻¹) (1 - 1 / (p : ℝ))⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  simpa only [Nat.cast_pow, inv_pow, one_div] using
    hasSum_geometric_of_lt_one (inv_nonneg.mpr hp0.le)
      ((inv_lt_one₀ hp0).mpr hp1)

theorem reciprocal_smooth_hasSum (s : Finset ℕ) :
    HasSum (fun n : Nat.factoredNumbers s => ((n : ℕ) : ℝ)⁻¹)
      (∏ p ∈ s.filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹) := by
  have H := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => (n : ℝ)⁻¹) (by simp)
    (fun {_ _} _ => by simp [mul_comm])
    (fun {p} hp => by
      simp only [Real.norm_eq_abs, abs_inv, Nat.abs_cast]
      exact (reciprocal_prime_powers_hasSum hp).summable) s).2
  convert H using 1
  apply prod_congr rfl
  intro p hp
  exact (reciprocal_prime_powers_hasSum (mem_filter.mp hp).2).tsum_eq.symm

/-- Every integer up to `N` is composed of primes up to `N`. The harmonic
sum is consequently bounded by the reciprocal finite Euler product. -/
theorem harmonic_le_reciprocal_prime_product (N : ℕ) :
    (harmonic N : ℝ) ≤
      ∏ p ∈ (range (N + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹ := by
  classical
  let s := range (N + 1)
  have hmem (i : ℕ) (hi : i ∈ range N) : i + 1 ∈ Nat.factoredNumbers s := by
    apply Nat.mem_factoredNumbers_of_primeFactors_subset (Nat.succ_ne_zero i)
    intro p hp
    apply mem_range.mpr
    have H := Nat.le_of_dvd (Nat.succ_pos i) (Nat.dvd_of_mem_primeFactors hp)
    have := mem_range.mp hi
    omega
  let e : {i : ℕ // i ∈ range N} → Nat.factoredNumbers s :=
    fun i => ⟨i.1 + 1, hmem i.1 i.2⟩
  have he : Function.Injective e := by
    intro i j h
    apply Subtype.ext
    have H := congrArg (fun n : Nat.factoredNumbers s => (n : ℕ)) h
    change i.1 + 1 = j.1 + 1 at H
    omega
  have H := reciprocal_smooth_hasSum s
  have hb := H.summable.sum_le_tsum ((range N).attach.image e) (fun _ _ => by positivity)
  rw [H.tsum_eq, sum_image (fun i _ j _ h => he h)] at hb
  change (∑ i ∈ (range N).attach, ((i.1 + 1 : ℕ) : ℝ)⁻¹) ≤ _ at hb
  rw [sum_attach (range N) (fun i : ℕ => ((i + 1 : ℕ) : ℝ)⁻¹)] at hb
  simpa only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using hb

/-- An elementary Mertens upper bound with constant one. -/
theorem sieveProduct_X_le_inv_log {x : ℝ} (hx : 1 < x) :
    sieveProduct (X : ℤ[X]) x ≤ (Real.log x)⁻¹ := by
  have hpos := sieveProduct_pos noFixedPrimeDivisor_X x
  have H := harmonic_le_reciprocal_prime_product ⌊x⌋₊
  have heq : (∏ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime,
      (1 - 1 / (p : ℝ))⁻¹) = (sieveProduct (X : ℤ[X]) x)⁻¹ := by
    simp only [sieveProduct, rootCount_X, Nat.cast_one, prod_inv_distrib]
  rw [heq] at H
  have hlog := (log_le_harmonic_floor x (by linarith)).trans H
  exact (le_inv_comm₀ hpos (Real.log_pos hx)).mpr hlog

/-- Omitting primes dividing `q` costs at most `q / φ(q)`, with no further
constant for this one-root Euler product. -/
theorem progressionSieveProduct_X_le {q : ℕ} (hq : q ≠ 0) (x : ℝ) :
    progressionSieveProduct (X : ℤ[X]) q x ≤
      sieveProduct (X : ℤ[X]) x * ((q : ℝ) / q.totient) := by
  classical
  let S := (range (⌊x⌋₊ + 1)).filter Nat.Prime
  let f := fun p : ℕ => 1 - 1 / (p : ℝ)
  have hf : ∀ p ∈ S, 0 < f p := by
    intro p hp
    have hp' := (mem_filter.mp hp).2
    exact sub_pos.mpr ((div_lt_one (by exact_mod_cast hp'.pos)).mpr
      (by exact_mod_cast hp'.one_lt))
  have hd : (∏ p ∈ S.filter (fun p => p ∣ q), f p) ≠ 0 :=
    (prod_pos (fun p hp => hf p (mem_filter.mp hp).1)).ne'
  have hpartition := prod_filter_mul_prod_filter_not S (fun p => p ∣ q) f
  have heq : (∏ p ∈ S.filter (fun p => ¬p ∣ q), f p) =
      (∏ p ∈ S, f p) * ∏ p ∈ S.filter (fun p => p ∣ q), (f p)⁻¹ := by
    rw [← hpartition, prod_inv_distrib]
    field_simp
  have hsub : S.filter (fun p => p ∣ q) ⊆ q.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr
      ⟨(mem_filter.mp (mem_filter.mp hp).1).2, (mem_filter.mp hp).2, hq⟩
  have hbound : (∏ p ∈ S.filter (fun p => p ∣ q), (f p)⁻¹) ≤ totientTwist 1 q := by
    have heq' : (∏ p ∈ S.filter (fun p => p ∣ q), (f p)⁻¹) =
        ∏ p ∈ S.filter (fun p => p ∣ q), totientTwist 1 p := by
      apply prod_congr rfl
      intro p hp
      rw [totientTwist_prime 1 (Nat.prime_of_mem_primeFactors (hsub hp)), pow_one]
      have hp0 : (p : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (hsub hp)).ne_zero
      dsimp [f]
      field_simp
    rw [heq', totientTwist_eq_prod 1 hq]
    apply prod_le_prod_of_subset_of_one_le₀ hsub
    · intro p _
      exact totientTwist_nonneg 1 p
    · intro p hp _
      exact totientTwist_one_le 1 (Nat.prime_of_mem_primeFactors hp).ne_zero
  simp only [progressionSieveProduct, sieveProduct, rootCount_X, Nat.cast_one]
  change (∏ p ∈ S.filter (fun p => ¬p ∣ q), f p) ≤ _
  rw [heq]
  exact mul_le_mul_of_nonneg_left (by simpa only [totientTwist, pow_one] using hbound)
    (prod_pos hf).le

theorem progressionSieveProduct_X_le_inv_log {q : ℕ} (hq : q ≠ 0)
    {x : ℝ} (hx : 1 < x) :
    progressionSieveProduct (X : ℤ[X]) q x ≤ ((q : ℝ) / q.totient) / Real.log x := by
  calc
    _ ≤ sieveProduct (X : ℤ[X]) x * ((q : ℝ) / q.totient) :=
      progressionSieveProduct_X_le hq x
    _ ≤ (Real.log x)⁻¹ * ((q : ℝ) / q.totient) :=
      mul_le_mul_of_nonneg_right (sieveProduct_X_le_inv_log hx) (by positivity)
    _ = _ := by ring

end NairTenenbaum
