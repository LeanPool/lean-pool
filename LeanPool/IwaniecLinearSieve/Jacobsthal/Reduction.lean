/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.LinearSieve.Estimate
import LeanPool.IwaniecLinearSieve.Jacobsthal.ShiftedSieve
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Reduction of Jacobsthal's problem to the linear sieve ([I78, §3])

`iwaniecBound_of_estimates` derives Iwaniec's bound `m ≪ (r log r)²` for the length `m` of a run
of consecutive integers each divisible by one of `r ≥ 2` given primes, from three analytic inputs
taken as hypotheses:

* `LinearSieveEstimate` (proved as `linearSieveEstimate`): [I71]'s bounds (main term and support
  size) for Rosser's lower-bound sieve at level `y = C₀ z²`, i.e. (5) and (6) of [I78, Lemma 2];
* `R(z) ≫ 1 / log z` (Mertens);
* `p_r ≪ r log r` for the `r`-th prime.

The proof is [I78, §3]: the shifted sieve (`shiftedSieve`) with `X = m`, for which the sifted set
is empty, gives `m ∏_{q ∈ S} (1 - 1/q) · (∑_{D⁻} μ(d)/d) / R(z) ≤ |D⁻|`.
-/

@[expose] public section

open Finset Real

namespace IwaniecLinearSieve

/-- From the linear sieve estimate and `R(z) ≫ 1 / log z`: if `π(z)` primes cover `m`
consecutive integers, then `m ≪ z²`. -/
theorem exists_covering_length_le (hL : LinearSieveEstimate)
    (hR : ∃ c > 0, ∀ z ≥ 2, c / log z ≤ R z) :
    ∃ K z₁ : ℝ, ∀ z ≥ z₁, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → #S = #(primesLT z) →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) → (m : ℝ) ≤ K * z ^ 2 := by
  obtain ⟨C₀, c, K, z₀, hc, hL⟩ := hL
  obtain ⟨c', hc', hR⟩ := hR
  refine ⟨K / (c * c'), max z₀ 2, fun z hz S hS hcard x m hm ↦ ?_⟩
  have hz0 : z₀ ≤ z := (le_max_left _ _).trans hz
  have hz2 : 2 ≤ z := (le_max_right _ _).trans hz
  have hlog : 0 < log z := log_pos (by linarith)
  have hRz := R_pos z
  set M := rosserMain true (C₀ * z ^ 2) z
  obtain ⟨hmain, hcount⟩ := hL z hz0
  have hsieve := shiftedSieve (C₀ * z ^ 2) hS hcard x m
  have hzero : (range m).filter (fun k : ℕ ↦ ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k) = ∅ := by
    rw [filter_eq_empty_iff]
    intro k hk h
    obtain ⟨q, hq, hqk⟩ := hm k (mem_range.1 hk)
    exact h q hq hqk
  rw [hzero, card_empty, Nat.cast_zero] at hsieve
  -- `M ≥ R(z) c / log z`
  have hM : R z * (c / log z) ≤ M := by nlinarith
  have hM0 : 0 ≤ M := (mul_nonneg hRz.le (div_pos hc hlog).le).trans hM
  have hprod := R_le_prod_of_card_eq hS hcard
  have h1 : (m : ℝ) * M ≤ #(rosserSet true (C₀ * z ^ 2) z) := by
    have : (m : ℝ) * M ≤ m * (∏ q ∈ S, (1 - (q : ℝ)⁻¹)) * (M / R z) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ m.cast_nonneg
      calc M = R z * (M / R z) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hprod (div_nonneg hM0 hRz.le)
    linarith
  have hRlog : c' ≤ R z * log z := by
    have := hR z hz2
    rwa [div_le_iff₀ hlog] at this
  -- `m c c' ≤ m c R(z) log z ≤ M m log z · log z ≤ K z²`
  have h2 : (m : ℝ) * (c * c') ≤ K * z ^ 2 := by
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    have e1 : (m : ℝ) * (c * c') ≤ (m : ℝ) * (R z * (c / log z)) * log z ^ 2 := by
      have : (m : ℝ) * (R z * (c / log z)) * log z ^ 2 = m * c * (R z * log z) := by
        field_simp
      rw [this, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hRlog (mul_nonneg hm0 hc.le)
    have e2 : (m : ℝ) * (R z * (c / log z)) * log z ^ 2 ≤ K * z ^ 2 / log z ^ 2 * log z ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact (mul_le_mul_of_nonneg_left hM hm0).trans (h1.trans hcount)
    have e3 : K * z ^ 2 / log z ^ 2 * log z ^ 2 = K * z ^ 2 := by
      field_simp
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hc hc')]
  linarith


/-- The primes below `p_N + 1`, where `p_N = Nat.nth Nat.Prime (N - 1)` is the `N`-th prime, are
the first `N` primes. -/
theorem card_primesLT_nth_prime_add_one (n : ℕ) :
    #(primesLT ((Nat.nth Nat.Prime n : ℝ) + 1)) = n + 1 := by
  rw [primesLT, show (Nat.nth Nat.Prime n : ℝ) + 1 = ((Nat.nth Nat.Prime n + 1 : ℕ) : ℝ) by
    push_cast; ring, Nat.ceil_natCast, Nat.primesBelow_card_eq_primeCounting', Nat.primeCounting',
    Nat.count_succ_eq_succ_count (Nat.prime_nth_prime n),
    Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime]

/-- Any finite set of `r ≤ N` primes extends to a set of exactly `N` primes. -/
theorem exists_superset_card_eq {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {N : ℕ} (hN : #S ≤ N) :
    ∃ S' : Finset ℕ, S ⊆ S' ∧ (∀ p ∈ S', p.Prime) ∧ #S' = N := by
  set U := primesLT ((Nat.nth Nat.Prime N : ℝ) + 1)
  have hU : #U = N + 1 := card_primesLT_nth_prime_add_one N
  have : N - #S ≤ #(U \ S) := (Nat.sub_le_sub_right (by omega) _).trans (le_card_sdiff S U)
  obtain ⟨T, hTU, hT⟩ := exists_subset_card_eq this
  refine ⟨S ∪ T, subset_union_left, fun p hp ↦ ?_, ?_⟩
  · rcases mem_union.1 hp with hp | hp
    · exact hS p hp
    · exact prime_of_mem_primesLT (sdiff_subset (hTU hp))
  · rw [card_union_of_disjoint (disjoint_of_subset_right hTU disjoint_sdiff), hT]
    omega


/-- **Iwaniec's bound for Jacobsthal's function** ([I78, Corollary]), assuming the linear sieve
estimate of [I71], the lower bound `R(z) ≫ 1 / log z`, and the bound `p_r ≪ r log r` for the
`r`-th prime: if `r ≥ 2` primes cover `m` consecutive integers, then `m ≪ (r log r)²`.

Given `S` with `#S = r`, we enlarge `S` to `N = N₀ r` primes (so that `z = p_N + 1 ≥ z₀`) and
apply `exists_covering_length_le` with `z = p_N + 1`, so that `primesLT z` consists of the first
`N` primes. -/
theorem iwaniecBound_of_estimates (hL : LinearSieveEstimate)
    (hR : ∃ c > 0, ∀ z ≥ 2, c / log z ≤ R z)
    (hp : ∃ C, ∀ r ≥ 2, (Nat.nth Nat.Prime (r - 1) : ℝ) ≤ C * r * log r) :
    ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
        (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2 := by
  obtain ⟨K, z₁, hK⟩ := exists_covering_length_le hL hR
  obtain ⟨Cp, hCp⟩ := hp
  set N₀ : ℕ := ⌈z₁⌉₊ + 2
  set B : ℝ := N₀ * (log N₀ / log 2 + 1)
  refine ⟨max K 0 * (|Cp| * B + 1) ^ 2, fun S hS hr x m hm ↦ ?_⟩
  set r := #S
  set N := N₀ * r
  have hrN : r ≤ N := Nat.le_mul_of_pos_left r (by omega)
  have hN2 : 2 ≤ N := hr.trans hrN
  obtain ⟨S', hSS', hS', hcard'⟩ := exists_superset_card_eq hS hrN
  set p := Nat.nth Nat.Prime (N - 1)
  set z : ℝ := p + 1
  have hcardz : #(primesLT z) = N := by
    rw [card_primesLT_nth_prime_add_one]
    omega
  have hz : z₁ ≤ z := by
    have h1 := Nat.add_two_le_nth_prime (N - 1)
    have h2 : N₀ ≤ N := Nat.le_mul_of_pos_right _ (by omega)
    have h3 : z₁ ≤ ⌈z₁⌉₊ := Nat.le_ceil z₁
    have h4 : (⌈z₁⌉₊ : ℝ) + 1 ≤ p := by exact_mod_cast (by omega : ⌈z₁⌉₊ + 1 ≤ p)
    simp only [z]
    linarith
  have hmz := hK z hz S' hS' (hcard'.trans hcardz.symm) x m fun k hk ↦
    let ⟨q, hq, h⟩ := hm k hk
    ⟨q, hSS' hq, h⟩
  -- `z ≤ (|Cp| B + 1) r log r`
  have hlog2 : (0.69 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlogr : log 2 ≤ log r := log_le_log (by norm_num) hr'
  have hrlogr : 1 ≤ (r : ℝ) * log r := by nlinarith
  have hN₀ : (1 : ℝ) ≤ N₀ := by exact_mod_cast (by omega : 1 ≤ N₀)
  have hlogN : log N ≤ (log N₀ / log 2 + 1) * log r := by
    rw [Nat.cast_mul, log_mul (by positivity) (by positivity)]
    have : log N₀ ≤ log N₀ / log 2 * log r := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      exact mul_le_mul_of_nonneg_left hlogr (log_nonneg hN₀)
    linarith
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNlogN0 : 0 ≤ (N : ℝ) * log N := mul_nonneg (by linarith) (log_nonneg (by linarith))
  have hpN : (p : ℝ) ≤ |Cp| * (B * (r * log r)) := by
    have h1 := hCp N hN2
    have h2 : (N : ℝ) * log N ≤ B * (r * log r) := by
      calc (N : ℝ) * log N = N₀ * r * log N := by simp [N]
        _ ≤ N₀ * r * ((log N₀ / log 2 + 1) * log r) :=
          mul_le_mul_of_nonneg_left hlogN (by positivity)
        _ = B * (r * log r) := by ring
    calc (p : ℝ) ≤ Cp * N * log N := h1
      _ = Cp * (N * log N) := by ring
      _ ≤ |Cp| * (N * log N) := mul_le_mul_of_nonneg_right (le_abs_self _) hNlogN0
      _ ≤ |Cp| * (B * (r * log r)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hz' : z ≤ (|Cp| * B + 1) * (r * log r) := by
    simp only [z]
    nlinarith
  have hz0 : 0 ≤ z := by positivity
  calc (m : ℝ) ≤ K * z ^ 2 := hmz
    _ ≤ max K 0 * z ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    _ ≤ max K 0 * ((|Cp| * B + 1) * (r * log r)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hz' 2) (le_max_right _ _)
    _ = _ := by ring

end IwaniecLinearSieve
