/-
Copyright (c) 2026 Yujie Sun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yujie Sun, Claude Opus 5.5 (AI)
-/
module

public import Mathlib.Data.Nat.Prime.Basic

/-!
# Rowland's lemma for the recurrence `a (n + 1) = a n + gcd (n + 1) (a n)`

This file works with an arbitrary sequence `a : ℕ → ℕ` that obeys Rowland's recurrence
`a (n + 1) = a n + Nat.gcd (n + 1) (a n)` from some index `n₀` on, with no assumption on its
initial values.

Call `N ≥ 2` a *checkpoint* of `a` when `a N = 3 * N`. Rowland's Lemma 1
(E. S. Rowland, *A natural prime-generating recurrence*, J. Integer Seq. 11 (2008),
Article 08.2.8) says: if `N` is a checkpoint and `p` is the least prime factor of `2 * N - 1`,
then the next `(p - 1) / 2 - 1` increments of `a` are all `1`, the following increment is `p`,
and `N + (p - 1) / 2` is again a checkpoint.

## Main results

* `RowlandPrimes.eq_of_lt_gap`: between a checkpoint `N` and the next one, `a (N + j) = 3 * N + j`.
* `RowlandPrimes.isCheckpoint_next`: `next N = N + (minFac (2 * N - 1) - 1) / 2` is a checkpoint.
* `RowlandPrimes.increment_at_next`: the increment arriving at `next N` is `minFac (2 * N - 1)`.
* `RowlandPrimes.increment_eq_one_or_minFac`: after a checkpoint every increment is `1` or the
  least prime factor of `2 * M - 1` for the checkpoint `M` it jumps from.
* `RowlandPrimes.increment_eq_one_or_prime`: after a checkpoint every increment `a (n + 1) - a n`
  is `1` or a prime.
* `RowlandPrimes.increment_ne_two`: after a checkpoint no increment equals `2`.
* `RowlandPrimes.exists_prime_increment_ge`: after a checkpoint, prime increments occur
  arbitrarily late.
-/

@[expose] public section

namespace RowlandPrimes

open Nat

/-- The sequence `a` satisfies Rowland's recurrence `a (n + 1) = a n + gcd (n + 1) (a n)` at every
index `n ≥ n₀`. -/
def SatisfiesRecurrence (a : ℕ → ℕ) (n₀ : ℕ) : Prop :=
  ∀ n, n₀ ≤ n → a (n + 1) = a n + Nat.gcd (n + 1) (a n)

/-- `N` is a *checkpoint* of `a` (in Rowland's sense) if `N ≥ 2` and `a N = 3 * N`. -/
def IsCheckpoint (a : ℕ → ℕ) (N : ℕ) : Prop :=
  2 ≤ N ∧ a N = 3 * N

/-- The gap to the next checkpoint: `(p - 1) / 2` where `p` is the least prime factor of
`2 * N - 1`. -/
def gap (N : ℕ) : ℕ :=
  (minFac (2 * N - 1) - 1) / 2

/-- The checkpoint following `N`. -/
def next (N : ℕ) : ℕ :=
  N + gap N

section Arithmetic

variable {N : ℕ}

lemma two_mul_sub_one_odd (hN : 2 ≤ N) : ¬ 2 ∣ 2 * N - 1 := by
  omega

lemma minFac_two_mul_sub_one_prime (hN : 2 ≤ N) : (minFac (2 * N - 1)).Prime :=
  minFac_prime (by omega)

lemma minFac_two_mul_sub_one_ne_two (hN : 2 ≤ N) : minFac (2 * N - 1) ≠ 2 := by
  intro h
  have hd := minFac_dvd (2 * N - 1)
  rw [h] at hd
  exact two_mul_sub_one_odd hN hd

/-- The least prime factor `p` of `2 * N - 1` is odd, so `p = 2 * gap N + 1`. -/
lemma two_mul_gap_add_one (hN : 2 ≤ N) : 2 * gap N + 1 = minFac (2 * N - 1) := by
  have hp := minFac_two_mul_sub_one_prime hN
  have h2 := minFac_two_mul_sub_one_ne_two hN
  have hodd : minFac (2 * N - 1) % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h h2
    · exact h
  unfold gap
  omega

lemma one_le_gap (hN : 2 ≤ N) : 1 ≤ gap N := by
  have hp := (minFac_two_mul_sub_one_prime hN).two_le
  have h := two_mul_gap_add_one hN
  have h2 := minFac_two_mul_sub_one_ne_two hN
  omega

lemma lt_next (hN : 2 ≤ N) : N < next N := by
  have := one_le_gap hN
  unfold next
  omega

/-- If `0 < j < gap N` then `N + j` is coprime to `2 * N - 1`. -/
lemma coprime_of_lt_gap (hN : 2 ≤ N) {j : ℕ} (hj : j < gap N) :
    Nat.gcd (N + j) (2 * N - 1) = 1 := by
  set g := Nat.gcd (N + j) (2 * N - 1) with hg
  have hq : 2 * N - 1 ≠ 0 := by omega
  have hgq : g ∣ 2 * N - 1 := Nat.gcd_dvd_right _ _
  have hgm : g ∣ N + j := Nat.gcd_dvd_left _ _
  -- `g` divides `2 * (N + j) - (2 * N - 1) = 2 * j + 1`.
  have hgs : g ∣ 2 * j + 1 := by
    have h1 : g ∣ 2 * (N + j) := Dvd.dvd.mul_left hgm 2
    have h2 : 2 * (N + j) = (2 * N - 1) + (2 * j + 1) := by omega
    rw [h2] at h1
    exact (Nat.dvd_add_right hgq).mp h1
  by_contra hne
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hgq
    exact hq hgq
  have hg2 : 2 ≤ g := by omega
  have hle : minFac (2 * N - 1) ≤ g := minFac_le_of_dvd hg2 hgq
  have hle' : g ≤ 2 * j + 1 := Nat.le_of_dvd (by omega) hgs
  have hp := two_mul_gap_add_one hN
  omega

/-- At `j = gap N` the gcd of `N + j` and `2 * N - 1` is exactly the least prime factor. -/
lemma gcd_at_gap (hN : 2 ≤ N) :
    Nat.gcd (N + gap N) (2 * N - 1) = minFac (2 * N - 1) := by
  set p := minFac (2 * N - 1) with hpdef
  have hp : p.Prime := minFac_two_mul_sub_one_prime hN
  have hpq : p ∣ 2 * N - 1 := minFac_dvd _
  have hgap := two_mul_gap_add_one hN
  have hsum : 2 * (N + gap N) = (2 * N - 1) + p := by omega
  -- `p ∣ N + gap N`, since `p ∣ 2 * (N + gap N)` and `p` is odd.
  have hpm : p ∣ N + gap N := by
    have h1 : p ∣ 2 * (N + gap N) := by
      rw [hsum]
      exact Nat.dvd_add hpq dvd_rfl
    have hcop : Nat.Coprime p 2 :=
      (Nat.coprime_primes hp Nat.prime_two).mpr (minFac_two_mul_sub_one_ne_two hN)
    exact hcop.dvd_of_dvd_mul_left h1
  -- The gcd divides `2 * (N + gap N) - (2 * N - 1) = p`.
  have hgp : Nat.gcd (N + gap N) (2 * N - 1) ∣ p := by
    have h1 : Nat.gcd (N + gap N) (2 * N - 1) ∣ 2 * (N + gap N) :=
      Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2
    rw [hsum] at h1
    exact (Nat.dvd_add_right (Nat.gcd_dvd_right _ _)).mp h1
  exact Nat.dvd_antisymm hgp (Nat.dvd_gcd hpm hpq)

end Arithmetic

section Recurrence

variable {a : ℕ → ℕ} {n₀ N : ℕ}

/-- If `a n = n + c` with `c ≥ 1`, the next gcd is `gcd (n + 1) (c - 1)`. -/
lemma gcd_succ_of_eq_add {n c : ℕ} (hc : 1 ≤ c) :
    Nat.gcd (n + 1) (n + c) = Nat.gcd (n + 1) (c - 1) := by
  have h : n + c = (c - 1) + (n + 1) := by omega
  rw [h, Nat.gcd_add_self_right]

/-- **Rowland's lemma, first part.** Between a checkpoint `N` and `next N` the sequence grows by
exactly `1` at each step: `a (N + j) = 3 * N + j` for `j < gap N`. -/
theorem eq_of_lt_gap (ha : SatisfiesRecurrence a n₀) (hn₀ : n₀ ≤ N) (hN : IsCheckpoint a N) :
    ∀ j, j < gap N → a (N + j) = 3 * N + j := by
  have hN2 := hN.1
  intro j
  induction j with
  | zero =>
    intro _
    simpa using hN.2
  | succ j ih =>
    intro hj
    have hprev := ih (by omega)
    have hrec := ha (N + j) (by omega)
    have hg : Nat.gcd (N + j + 1) (a (N + j)) = 1 := by
      rw [hprev, show 3 * N + j = (N + j) + (2 * N) by omega,
        gcd_succ_of_eq_add (by omega), show N + j + 1 = N + (j + 1) by omega]
      exact coprime_of_lt_gap hN.1 hj
    rw [show N + (j + 1) = N + j + 1 by omega, hrec, hg, hprev]
    omega

/-- The gcd that drives the step into `next N` equals the least prime factor of `2 * N - 1`. -/
lemma gcd_into_next (ha : SatisfiesRecurrence a n₀) (hn₀ : n₀ ≤ N) (hN : IsCheckpoint a N) :
    Nat.gcd (N + (gap N - 1) + 1) (a (N + (gap N - 1))) = minFac (2 * N - 1) := by
  have h1 := one_le_gap hN.1
  have hN2 := hN.1
  rw [eq_of_lt_gap ha hn₀ hN (gap N - 1) (by omega),
    show 3 * N + (gap N - 1) = (N + (gap N - 1)) + (2 * N) by omega,
    gcd_succ_of_eq_add (by omega), show N + (gap N - 1) + 1 = N + gap N by omega]
  exact gcd_at_gap hN.1

/-- **Rowland's lemma, second part.** The increment arriving at `next N` is the least prime
factor of `2 * N - 1`. -/
theorem increment_at_next (ha : SatisfiesRecurrence a n₀) (hn₀ : n₀ ≤ N)
    (hN : IsCheckpoint a N) :
    a (next N) = a (next N - 1) + minFac (2 * N - 1) := by
  have h1 := one_le_gap hN.1
  have hrec := ha (N + (gap N - 1)) (by omega)
  rw [gcd_into_next ha hn₀ hN, show N + (gap N - 1) + 1 = next N by unfold next; omega,
    show N + (gap N - 1) = next N - 1 by unfold next; omega] at hrec
  exact hrec

/-- **Rowland's lemma, third part.** `next N` is again a checkpoint. -/
theorem isCheckpoint_next (ha : SatisfiesRecurrence a n₀) (hn₀ : n₀ ≤ N)
    (hN : IsCheckpoint a N) : IsCheckpoint a (next N) := by
  have h1 := one_le_gap hN.1
  have hgap := two_mul_gap_add_one hN.1
  have hN2 := hN.1
  refine ⟨by have := lt_next hN.1; omega, ?_⟩
  rw [increment_at_next ha hn₀ hN,
    show next N - 1 = N + (gap N - 1) by unfold next; omega,
    eq_of_lt_gap ha hn₀ hN _ (by omega), ← hgap]
  unfold next
  omega

/-- Below `next N`, the increments after a checkpoint are `1`. -/
lemma increment_eq_one_of_lt (ha : SatisfiesRecurrence a n₀) (hn₀ : n₀ ≤ N)
    (hN : IsCheckpoint a N) {n : ℕ} (hNn : N ≤ n) (hn : n + 1 < next N) :
    a (n + 1) = a n + 1 := by
  have e1 := eq_of_lt_gap ha hn₀ hN (n - N) (by unfold next at hn; omega)
  have e2 := eq_of_lt_gap ha hn₀ hN (n + 1 - N) (by unfold next at hn; omega)
  rw [show N + (n - N) = n by omega] at e1
  rw [show N + (n + 1 - N) = n + 1 by omega] at e2
  omega

/-- Strong-induction form of `increment_eq_one_or_minFac`, indexed by `d = n - N`. -/
theorem increment_eq_one_or_minFac_aux (ha : SatisfiesRecurrence a n₀) :
    ∀ d N n, n - N = d → n₀ ≤ N → IsCheckpoint a N → N ≤ n →
      a (n + 1) = a n + 1 ∨
        ∃ M, n₀ ≤ M ∧ IsCheckpoint a M ∧ n + 1 = next M ∧
          a (n + 1) = a n + minFac (2 * M - 1) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro N n hd hn₀ hN hNn
    rcases lt_trichotomy (n + 1) (next N) with hlt | heq | hgt
    · exact Or.inl (increment_eq_one_of_lt ha hn₀ hN hNn hlt)
    · refine Or.inr ⟨N, hn₀, hN, heq, ?_⟩
      have := increment_at_next ha hn₀ hN
      rw [← heq] at this
      simpa using this
    · have hlt := lt_next hN.1
      exact ih (n - next N) (by omega) (next N) n rfl (by omega)
        (isCheckpoint_next ha hn₀ hN) (by omega)

/-- **Rowland's theorem, general form.** After a checkpoint `N` (with the recurrence valid from
`n₀ ≤ N` on), every increment `a (n + 1) - a n` with `n ≥ N` is either `1`, or equals the least
prime factor of `2 * M - 1` for a checkpoint `M` with `n + 1 = next M`. -/
theorem increment_eq_one_or_minFac (ha : SatisfiesRecurrence a n₀) (hn₀ : n₀ ≤ N)
    (hN : IsCheckpoint a N) {n : ℕ} (hNn : N ≤ n) :
    a (n + 1) = a n + 1 ∨
      ∃ M, n₀ ≤ M ∧ IsCheckpoint a M ∧ n + 1 = next M ∧
        a (n + 1) = a n + minFac (2 * M - 1) :=
  increment_eq_one_or_minFac_aux ha (n - N) N n rfl hn₀ hN hNn

/-- After a checkpoint, every increment of `a` is `1` or a prime. -/
theorem increment_eq_one_or_prime (ha : SatisfiesRecurrence a n₀) (hn₀ : n₀ ≤ N)
    (hN : IsCheckpoint a N) {n : ℕ} (hNn : N ≤ n) :
    a (n + 1) - a n = 1 ∨ (a (n + 1) - a n).Prime := by
  rcases increment_eq_one_or_minFac ha hn₀ hN hNn with h | ⟨M, -, hM, -, h⟩
  · left
    omega
  · right
    rw [h, Nat.add_sub_cancel_left]
    exact minFac_two_mul_sub_one_prime hM.1

/-- After a checkpoint, no increment of `a` equals `2`: the prime increments are odd. -/
theorem increment_ne_two (ha : SatisfiesRecurrence a n₀) (hn₀ : n₀ ≤ N)
    (hN : IsCheckpoint a N) {n : ℕ} (hNn : N ≤ n) :
    a (n + 1) - a n ≠ 2 := by
  rcases increment_eq_one_or_minFac ha hn₀ hN hNn with h | ⟨M, -, hM, -, h⟩
  · omega
  · rw [h, Nat.add_sub_cancel_left]
    exact minFac_two_mul_sub_one_ne_two hM.1

/-- The iterates of `next` starting from a checkpoint are checkpoints. -/
lemma isCheckpoint_iterate_next (ha : SatisfiesRecurrence a n₀) (hn₀ : n₀ ≤ N)
    (hN : IsCheckpoint a N) :
    ∀ k, n₀ ≤ next^[k] N ∧ IsCheckpoint a (next^[k] N) := by
  intro k
  induction k with
  | zero => exact ⟨hn₀, hN⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := lt_next ih.2.1
    exact ⟨by omega, isCheckpoint_next ha ih.1 ih.2⟩

lemma le_iterate_next (hN : 2 ≤ N) : ∀ k, N + k ≤ next^[k] N := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h2 : 2 ≤ next^[k] N := by omega
    have := lt_next h2
    omega

/-- After a checkpoint, prime increments occur arbitrarily late: for every `m` there is `n ≥ m`
with `a (n + 1) - a n` prime. -/
theorem exists_prime_increment_ge (ha : SatisfiesRecurrence a n₀) (hn₀ : n₀ ≤ N)
    (hN : IsCheckpoint a N) (m : ℕ) :
    ∃ n, m ≤ n ∧ (a (n + 1) - a n).Prime := by
  obtain ⟨hM₀, hMc⟩ := isCheckpoint_iterate_next ha hn₀ hN m
  have hle := le_iterate_next hN.1 m
  generalize next^[m] N = M at hM₀ hMc hle
  have hlt := lt_next hMc.1
  refine ⟨next M - 1, by omega, ?_⟩
  rw [show next M - 1 + 1 = next M by omega, increment_at_next ha hM₀ hMc,
    Nat.add_sub_cancel_left]
  exact minFac_two_mul_sub_one_prime hMc.1

/-- Closed form between consecutive checkpoints: if `N ≤ n < next N` then `a n = n + 2 * N`. -/
theorem eq_add_two_mul_of_le_of_lt (ha : SatisfiesRecurrence a n₀) (hn₀ : n₀ ≤ N)
    (hN : IsCheckpoint a N) {n : ℕ} (hNn : N ≤ n) (hn : n < next N) :
    a n = n + 2 * N := by
  have := eq_of_lt_gap ha hn₀ hN (n - N) (by unfold next at hn; omega)
  rw [show N + (n - N) = n by omega] at this
  omega

end Recurrence

end RowlandPrimes
