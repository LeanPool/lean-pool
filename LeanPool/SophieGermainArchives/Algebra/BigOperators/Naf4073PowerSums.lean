/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.SophieGermainArchives.NumberTheory.Naf4073Triangular
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

/-!
# NAF 4073: sums of odd powers as polynomials in `T_n`

Adapted from `Germain/Algebra/BigOperators/Naf4073PowerSums.lean` of
https://github.com/Commutator-IO/GermainArchivesProofs
at commit `8aa15af` (Apache-2.0, same author); the same proofs are under CC0 in
https://github.com/Commutator-IO/germain-project.

Summing the differences `T_m² − T_{m−1}² = m³` from `1` to `n` gives Lagrange's formula
`1³ + ⋯ + n³ = T_n²`. The same telescoping at exponent `k` gives a triangular linear system for
the sums of odd powers (Faulhaber's method, as reconstructed by Knuth, 1993).

## Main results

* `S p n = 0^p + 1^p + ⋯ + n^p`.
* `T_pow_eq_sum`: `2^(k−1) T_n^k = ∑_{m ≤ k, k − m odd} C(k, m) S_{k+m}`.
* `S_one`, `S_three`, `S_five`, `S_seven`, `S_nine`: the first rows, solved.
* `T_pow_eq_sum_even`: the even system, telescoping `(2n+1) T_n^k`:
  `2^(k−1) (2n+1) T_n^k = ∑_{m ≤ k} C(k, m) (S_{k+m} if k − m is even, 2 S_{k+m+1} if odd)`.
* `S_two`, `S_four`, `S_six`, `S_eight`, `S_ten`: its first rows, solved.
* `S_even_eq_S_two_mul` (proposition 10): `S_{2k} = S₂ · R_k(S₁)` for every `k ≥ 1`, by strong
  induction on the even system (`S_even_isEvenForm`).
-/

@[expose] public section

namespace LeanPool.SophieGermainArchives.Naf4073

open Finset

/-- `S p n = 0^p + 1^p + ⋯ + n^p`. -/
def S (p n : ℕ) : ℕ := ∑ i ∈ range (n + 1), i ^ p

/-- `(x+1)^k − (x−1)^k = 2 ∑_{m ≤ k, k − m odd} C(k, m) x^m`. -/
lemma sum_odd_binom (x : ℚ) (k : ℕ) :
    (x + 1) ^ k - (x - 1) ^ k
      = 2 * ∑ m ∈ (range (k + 1)).filter (fun m => Odd (k - m)), (k.choose m : ℚ) * x ^ m := by
  rw [sub_eq_add_neg x 1, add_pow, add_pow, ← sum_sub_distrib, sum_filter, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rcases Nat.even_or_odd (k - m) with h | h
  · rw [ite_eq_right (Nat.not_odd_iff_even.mpr h), h.neg_one_pow]
    ring
  · rw [ite_eq_left h, h.neg_one_pow]
    ring

/-- The triangular system: `2^(k−1) T_n^k = ∑_{m ≤ k, k − m odd} C(k, m) S_{k+m}`, for `k ≥ 1`. -/
theorem T_pow_eq_sum (k n : ℕ) (hk : 1 ≤ k) :
    (2 : ℚ) ^ (k - 1) * (T n : ℚ) ^ k
      = ∑ m ∈ (range (k + 1)).filter (fun m => Odd (k - m)),
          (k.choose m : ℚ) * (S (k + m) n : ℚ) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction n with
  | zero => norm_num [T, S]
  | succ n ih =>
    have hS (p : ℕ) : (S p (n + 1) : ℚ) = S p n + ((n : ℚ) + 1) ^ p := by
      simp [S, sum_range_succ _ (n + 1)]
    simp_rw [hS, mul_add, sum_add_distrib, ← ih]
    have hb := sum_odd_binom ((n : ℚ) + 1) (k + 1)
    have hsum : ∑ m ∈ (range (k + 1 + 1)).filter (fun m => Odd (k + 1 - m)),
        (((k + 1).choose m : ℚ) * ((n : ℚ) + 1) ^ (k + 1 + m))
        = ((n : ℚ) + 1) ^ (k + 1) * ∑ m ∈ (range (k + 1 + 1)).filter (fun m => Odd (k + 1 - m)),
          ((k + 1).choose m : ℚ) * ((n : ℚ) + 1) ^ m := by
      rw [mul_sum]
      exact sum_congr rfl fun m _ => by ring
    rw [hsum]
    rw [show (n : ℚ) + 1 + 1 = n + 2 by ring, add_sub_cancel_right] at hb
    have hT : (T n : ℚ) ^ (k + 1) + (((n : ℚ) + 1) / 2) ^ (k + 1)
        * (((n : ℚ) + 2) ^ (k + 1) - (n : ℚ) ^ (k + 1)) = (T (n + 1) : ℚ) ^ (k + 1) := by
      rw [← T_pow_sub]; ring
    rw [← hT, hb, div_pow]
    field_simp
    ring

/-- The first rows of the system, solved: `S₁ = T`, `S₃ = T²`, `3 S₅ = T²(4T − 1)`,
`3 S₇ = T²(6T² − 4T + 1)`. -/
theorem S_one (n : ℕ) : S 1 n = T n := by
  have h := T_pow_eq_sum 1 n le_rfl
  norm_num [show (range 2).filter (fun m => Odd (1 - m)) = {0} by decide] at h
  exact_mod_cast h.symm

theorem S_three (n : ℕ) : S 3 n = T n ^ 2 := by
  have h := T_pow_eq_sum 2 n (by norm_num)
  norm_num [show (range 3).filter (fun m => Odd (2 - m)) = {1} by decide] at h
  exact_mod_cast (by linarith : (S 3 n : ℚ) = T n ^ 2)

theorem S_five (n : ℕ) : 3 * (S 5 n : ℚ) = (T n : ℚ) ^ 2 * (4 * T n - 1) := by
  have h3 := T_pow_eq_sum 3 n (by norm_num)
  norm_num [show (range 4).filter (fun m => Odd (3 - m)) = {0, 2} by decide] at h3
  have h2 : (S 3 n : ℚ) = (T n : ℚ) ^ 2 := by exact_mod_cast S_three n
  linarith

theorem S_seven (n : ℕ) :
    3 * (S 7 n : ℚ) = (T n : ℚ) ^ 2 * (6 * (T n : ℚ) ^ 2 - 4 * T n + 1) := by
  have h4 := T_pow_eq_sum 4 n (by norm_num)
  norm_num [show (range 5).filter (fun m => Odd (4 - m)) = {1, 3} by decide] at h4
  have h5 := S_five n
  linarith

/-! ## Sums of even powers -/

/-- `(2x+1)(x+1)^k − (2x−1)(x−1)^k = ∑_{m ≤ k} C(k, m) c_m`, where `c_m` is `2 x^m` if `k − m`
is even and `4 x^(m+1)` if it is odd. -/
lemma sum_even_binom (x : ℚ) (k : ℕ) :
    (2 * x + 1) * (x + 1) ^ k - (2 * x - 1) * (x - 1) ^ k
      = ∑ m ∈ range (k + 1),
          (k.choose m : ℚ) * (if Even (k - m) then 2 * x ^ m else 4 * x ^ (m + 1)) := by
  rw [sub_eq_add_neg x 1, add_pow, add_pow, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun m _ => ?_
  rcases Nat.even_or_odd (k - m) with h | h
  · rw [ite_eq_left h, h.neg_one_pow]; ring
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr h), h.neg_one_pow]; ring

/-- The even system: `2^(k−1) (2n+1) T_n^k = ∑_{m ≤ k} C(k, m) (S_{k+m} if k − m is even,
`2 S_{k+m+1}` if odd)`, for `k ≥ 1`; the leading term is `(2k+1) S_{2k}`. -/
theorem T_pow_eq_sum_even (k n : ℕ) (hk : 1 ≤ k) :
    (2 : ℚ) ^ (k - 1) * (2 * n + 1) * (T n : ℚ) ^ k
      = ∑ m ∈ range (k + 1), (k.choose m : ℚ)
          * (if Even (k - m) then (S (k + m) n : ℚ) else 2 * (S (k + m + 1) n : ℚ)) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction n with
  | zero => norm_num [T, S]
  | succ n ih =>
    have hS (p : ℕ) : (S p (n + 1) : ℚ) = S p n + ((n : ℚ) + 1) ^ p := by
      simp [S, sum_range_succ _ (n + 1)]
    have hsplit : ∀ m ∈ range (k + 1 + 1), ((k + 1).choose m : ℚ)
        * (if Even (k + 1 - m) then (S (k + 1 + m) (n + 1) : ℚ)
            else 2 * (S (k + 1 + m + 1) (n + 1) : ℚ))
        = ((k + 1).choose m : ℚ) * (if Even (k + 1 - m) then (S (k + 1 + m) n : ℚ)
            else 2 * (S (k + 1 + m + 1) n : ℚ))
          + ((n : ℚ) + 1) ^ (k + 1) / 2 * (((k + 1).choose m : ℚ)
            * (if Even (k + 1 - m) then 2 * ((n : ℚ) + 1) ^ m
              else 4 * ((n : ℚ) + 1) ^ (m + 1))) := fun m _ => by
      rw [hS, hS]; split_ifs <;> ring
    rw [sum_congr rfl hsplit, sum_add_distrib, ← ih, ← mul_sum, ← sum_even_binom, T_succ_cast,
      T_cast']
    push_cast
    rw [mul_pow, mul_pow, div_pow]
    field_simp
    ring

/-- The first rows of the even system, solved: `3 S₂ = (2n+1) T` and
`15 S₄ = (2n+1) T (6T − 1)`. -/
theorem S_two (n : ℕ) : 3 * (S 2 n : ℚ) = (2 * n + 1) * T n := by
  have h := T_pow_eq_sum_even 1 n le_rfl
  norm_num [sum_range_succ] at h
  linear_combination (-1 : ℚ) * h

theorem S_four (n : ℕ) :
    15 * (S 4 n : ℚ) = (2 * n + 1) * T n * (6 * T n - 1) := by
  have h := T_pow_eq_sum_even 2 n (by norm_num)
  norm_num [sum_range_succ, Nat.choose] at h
  linear_combination (-3 : ℚ) * h - S_two n

theorem S_nine (n : ℕ) :
    5 * (S 9 n : ℚ) = (T n : ℚ) ^ 2 * (16 * (T n : ℚ) ^ 3 - 20 * (T n : ℚ) ^ 2 + 12 * T n - 3) := by
  have h := T_pow_eq_sum 5 n (by norm_num)
  norm_num [show (range 6).filter (fun m => Odd (5 - m)) = {0, 2, 4} by decide,
    Nat.choose] at h
  linear_combination (-1 : ℚ) * h - (1 / 3 : ℚ) * S_five n - (10 / 3 : ℚ) * S_seven n

theorem S_six (n : ℕ) :
    21 * (S 6 n : ℚ) = (2 * n + 1) * T n * (12 * (T n : ℚ) ^ 2 - 6 * T n + 1) := by
  have h := T_pow_eq_sum_even 3 n (by norm_num)
  norm_num [sum_range_succ, Nat.choose] at h
  linear_combination (-3 : ℚ) * h - S_four n

theorem S_eight (n : ℕ) :
    45 * (S 8 n : ℚ)
      = (2 * n + 1) * T n * (40 * (T n : ℚ) ^ 3 - 40 * (T n : ℚ) ^ 2 + 18 * T n - 3) := by
  have h := T_pow_eq_sum_even 4 n (by norm_num)
  norm_num [sum_range_succ, Nat.choose] at h
  linear_combination (-5 : ℚ) * h - (1 / 3 : ℚ) * S_four n - (10 / 3 : ℚ) * S_six n

theorem S_ten (n : ℕ) :
    33 * (S 10 n : ℚ)
      = (2 * n + 1) * T n
          * (48 * (T n : ℚ) ^ 4 - 80 * (T n : ℚ) ^ 3 + 68 * (T n : ℚ) ^ 2 - 30 * T n + 5) := by
  have h := T_pow_eq_sum_even 5 n (by norm_num)
  norm_num [sum_range_succ, Nat.choose] at h
  linear_combination (-3 : ℚ) * h - 2 * S_eight n - S_six n

/-! ## Every even sum is `S₂` times a polynomial in `T` -/

/-- A function of `n` of the form `(2n+1) T_n Q(T_n)`, `Q` a polynomial with rational
coefficients. -/
def IsEvenForm (g : ℕ → ℚ) : Prop :=
  ∃ Q : Polynomial ℚ, ∀ n, g n = (2 * n + 1) * T n * Q.eval (T n : ℚ)

lemma IsEvenForm.add {f g : ℕ → ℚ} (hf : IsEvenForm f) (hg : IsEvenForm g) :
    IsEvenForm (f + g) := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P + Q, fun n => by simp [hP, hQ]; ring⟩

lemma IsEvenForm.zero : IsEvenForm 0 := ⟨0, fun n => by simp⟩

lemma IsEvenForm.const_mul {g : ℕ → ℚ} (c : ℚ) (hg : IsEvenForm g) :
    IsEvenForm (fun n => c * g n) := by
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨Polynomial.C c * Q, fun n => by simp [hQ]; ring⟩

lemma IsEvenForm.sub {f g : ℕ → ℚ} (hf : IsEvenForm f) (hg : IsEvenForm g) :
    IsEvenForm (fun n => f n - g n) := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P - Q, fun n => by simp [hP, hQ]; ring⟩

lemma IsEvenForm.sum {ι : Type*} (s : Finset ι) (g : ι → ℕ → ℚ)
    (hg : ∀ i ∈ s, IsEvenForm (g i)) : IsEvenForm (fun n => ∑ i ∈ s, g i n) := by
  have : IsEvenForm (∑ i ∈ s, g i) :=
    Finset.sum_induction _ IsEvenForm (fun _ _ => IsEvenForm.add) IsEvenForm.zero hg
  rwa [show (fun n => ∑ i ∈ s, g i n) = ∑ i ∈ s, g i from
    funext fun n => (Finset.sum_apply n s g).symm]

/-- `S_{2k} = (2n+1) T Q_k(T)` for every `k ≥ 1`: strong induction on the even system, whose
terms are all even sums (`k + m` is even when `k − m` is, `k + m + 1` when it is not), the two
top terms making `(2k+1) S_{2k}`. -/
theorem S_even_isEvenForm (k : ℕ) (hk : 1 ≤ k) : IsEvenForm (fun n => (S (2 * k) n : ℚ)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  -- the row of the even system, its two top terms split off
  set f : ℕ → ℕ → ℚ := fun m n => ((k + 1).choose m : ℚ)
      * (if Even (k + 1 - m) then (S (k + 1 + m) n : ℚ) else 2 * (S (k + 1 + m + 1) n : ℚ))
    with hf
  have hrow : ∀ n, (2 : ℚ) ^ k * (2 * n + 1) * (T n : ℚ) ^ (k + 1)
      = ∑ m ∈ range k, f m n + (2 * k + 3) * (S (2 * (k + 1)) n : ℚ) := fun n => by
    have h := T_pow_eq_sum_even (k + 1) n (by omega)
    rw [Nat.add_sub_cancel] at h
    rw [h, sum_range_succ, sum_range_succ]
    simp only [hf, Nat.sub_self, show k + 1 - k = 1 by omega, Nat.choose_self,
      Nat.choose_succ_self_right]
    rw [ite_eq_left (show Even 0 from ⟨0, rfl⟩), ite_eq_right Nat.not_even_one,
      show k + 1 + (k + 1) = 2 * (k + 1) by ring, show k + 1 + k + 1 = 2 * (k + 1) by ring]
    push_cast; ring
  -- every lower term is an even sum of index `2j`, `1 ≤ j ≤ k`
  have hlow : ∀ m ∈ range k, IsEvenForm (f m) := fun m hm => by
    have hm := mem_range.1 hm
    simp only [hf]
    by_cases he : Even (k + 1 - m)
    · obtain ⟨j, hj⟩ : ∃ j, k + 1 + m = 2 * j := by
        obtain ⟨r, hr⟩ := he; exact ⟨m + r, by omega⟩
      have := (ih j (by omega) (by omega)).const_mul ((k + 1).choose m : ℚ)
      simpa [he, hj] using this
    · obtain ⟨j, hj⟩ : ∃ j, k + 1 + m + 1 = 2 * j := by
        rcases Nat.not_even_iff_odd.1 he with ⟨r, hr⟩; exact ⟨m + r + 1, by omega⟩
      have := ((ih j (by omega) (by omega)).const_mul 2).const_mul ((k + 1).choose m : ℚ)
      simpa [he, hj, mul_assoc] using this
  -- the left side is `(2n+1) T (2^k T^k)`
  have hlhs : IsEvenForm (fun n => (2 : ℚ) ^ k * (2 * n + 1) * (T n : ℚ) ^ (k + 1)) :=
    ⟨Polynomial.C ((2 : ℚ) ^ k) * Polynomial.X ^ k, fun n => by simp; ring⟩
  have key := (hlhs.sub (IsEvenForm.sum (range k) f hlow)).const_mul (1 / (2 * k + 3))
  refine (show (fun n => (S (2 * (k + 1)) n : ℚ)) = _ from funext fun n => ?_) ▸ key
  rw [hrow n]
  have : (2 * (k : ℚ) + 3) ≠ 0 := by positivity
  field_simp
  ring

/-- **Proposition 10.** For every `k ≥ 1` there is a polynomial `R_k` with rational coefficients
such that `S_{2k} = S₂ · R_k(S₁)`. -/
theorem S_even_eq_S_two_mul (k : ℕ) (hk : 1 ≤ k) :
    ∃ R : Polynomial ℚ, ∀ n, (S (2 * k) n : ℚ) = S 2 n * R.eval (T n : ℚ) := by
  obtain ⟨Q, hQ⟩ := S_even_isEvenForm k hk
  refine ⟨Polynomial.C 3 * Q, fun n => ?_⟩
  have h := hQ n
  simp only at h
  rw [h, Polynomial.eval_mul, Polynomial.eval_C]
  linear_combination (-(Q.eval (T n : ℚ))) * S_two n

end LeanPool.SophieGermainArchives.Naf4073
