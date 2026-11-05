/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.Rosser
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Bool

/-!
# Depth stabilisation of Rosser's sieve ([I71, pp. 23, 26])

A failing tuple `p₁ > ⋯ > p_l` of depth `l ≥ 3` passed the test at index `l - 2`, so
`p₁ ⋯ p_{l-1} < p₁ ⋯ p_{l-2} p_{l-2}² < y`; an element `d = p₁ ⋯ p_l` of `rosserSet lower y z`
satisfies `d < y` as soon as `l ≥ 2` (or `l ≥ 1` for the upper sieve). Hence if every product of
`r` distinct primes below `z` is at least `y` (`LeProdPrimesLT r y z`), the recursion stops at
depth `r`:

* `fail_add_eq`: `2 ≤ r → LeProdPrimesLT r y z → fail lower (r + j) y z = fail lower r y z`;
* `card_filter_rosserSet_add_eq`:
  `1 ≤ r → LeProdPrimesLT (r + 1) y z → #{d ∈ D | ω(d) ≤ r + j} = #{d ∈ D | ω(d) ≤ r}`.

Products of `r` distinct primes are at least `(r + 1)!` (`factorial_card_add_one_le_prod`), and
`(r + 1)! ≥ y` once `r + 2 > 2 log y / log log y` and `y` is large (`exists_le_factorial`), which
gives [I71]'s "if `m + 1 > 2 log y / log log y` then `Q_{m+1, y} = Q_{m-1, y}`"
(`exists_fail_add_eq`, `exists_card_filter_rosserSet_add_eq`).
-/

@[expose] public section

open Finset Real

namespace IwaniecLinearSieve

/-- `y` is at most every product of `r` distinct primes below `z` (vacuous if there are fewer
than `r` such primes). -/
def LeProdPrimesLT (r : ℕ) (y z : ℝ) : Prop :=
  ∀ T ⊆ primesLT z, #T = r → y ≤ ∏ p ∈ T, (p : ℝ)

variable {lower : Bool} {r : ℕ} {y z : ℝ} {p d : ℕ}

theorem one_le_prod_primes {T : Finset ℕ} {z : ℝ} (hT : T ⊆ primesLT z) :
    1 ≤ ∏ p ∈ T, (p : ℝ) :=
  one_le_prod₀ fun p hp ↦ by exact_mod_cast (prime_of_mem_primesLT (hT hp)).one_lt.le

/-- One level down the recursion. -/
theorem LeProdPrimesLT.div (h : LeProdPrimesLT (r + 1) y z) (hp : p ∈ primesLT z) :
    LeProdPrimesLT r (y / p) p := by
  intro T hT hcard
  have hpT : p ∉ T := fun h ↦ notMem_primesLT_self (hT h)
  have hpos : (0 : ℝ) < p := by exact_mod_cast (prime_of_mem_primesLT hp).pos
  have := h (insert p T) (insert_subset hp (hT.trans (primesLT_natCast_subset hp)))
    (by rw [card_insert_of_notMem hpT, hcard])
  rw [prod_insert hpT] at this
  rwa [div_le_iff₀' hpos]

theorem LeProdPrimesLT.succ (h : LeProdPrimesLT r y z) : LeProdPrimesLT (r + 1) y z := by
  intro T hT hcard
  obtain ⟨a, ha⟩ := card_pos.1 (by omega : 0 < #T)
  rw [← mul_prod_erase T _ ha]
  have h1 := h (T.erase a) ((erase_subset a T).trans hT) (by rw [card_erase_of_mem ha, hcard]; rfl)
  have h2 : (1 : ℝ) ≤ a := by exact_mod_cast (prime_of_mem_primesLT (hT ha)).one_lt.le
  have h3 := one_le_prod_primes ((erase_subset a T).trans hT)
  nlinarith

theorem LeProdPrimesLT.mono {s : ℕ} (h : LeProdPrimesLT r y z) (hrs : r ≤ s) :
    LeProdPrimesLT s y z := by
  induction s, hrs using Nat.le_induction with
  | base => exact h
  | succ s _ ih => exact ih.succ

/-- A product of `#T` distinct integers `≥ 2` is at least `(#T + 1)!`. -/
theorem factorial_card_add_one_le_prod (T : Finset ℕ) (hT : ∀ n ∈ T, 2 ≤ n) :
    (#T + 1).factorial ≤ ∏ n ∈ T, n := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a T hlt ih =>
    have haT : a ∉ T := fun h ↦ lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem haT, prod_insert haT, Nat.factorial_succ]
    have hsub : T ⊆ Ico 2 a := fun n hn ↦ mem_Ico.2 ⟨hT n (mem_insert_of_mem hn), hlt n hn⟩
    have hcard : #T + 2 ≤ a := by
      have := card_le_card hsub
      have h2 := hT a (mem_insert_self a T)
      simp only [Nat.card_Ico] at this
      omega
    exact Nat.mul_le_mul (by omega) (ih fun n hn ↦ hT n (mem_insert_of_mem hn))

theorem leProdPrimesLT_of_le_factorial (h : y ≤ (r + 1).factorial) : LeProdPrimesLT r y z := by
  intro T hT hcard
  refine h.trans ?_
  rw [← hcard]
  have h := (Nat.cast_le (α := ℝ)).2 (factorial_card_add_one_le_prod T fun n hn ↦
    (prime_of_mem_primesLT (hT hn)).two_le)
  push_cast at h
  exact h

/-! ### Stabilisation of `fail` -/
theorem fail_succ_congr {a b : ℕ}
    (h : ∀ p ∈ rosserPrimes lower y z, fail (!lower) a (y / p) p = fail (!lower) b (y / p) p) :
    fail lower (a + 1) y z = fail lower (b + 1) y z := by
  cases lower <;> simp only [Bool.not_false, Bool.not_true] at h
  · rw [fail_false_succ, fail_false_succ]
    congr 1
    exact sum_congr rfl fun p hp ↦ by rw [h p hp]
  · rw [fail_true_succ, fail_true_succ]
    exact sum_congr rfl fun p hp ↦ by rw [h p (by simpa using hp)]

/-- If every product of `r ≥ 2` distinct primes below `z` is at least `y`, the deficits do not
change beyond depth `r`. -/
theorem fail_add_eq (hr : 2 ≤ r) (h : LeProdPrimesLT r y z) (j : ℕ) :
    fail lower (r + j) y z = fail lower r y z := by
  induction r, hr using Nat.le_induction generalizing lower y z with
  | base =>
    rw [show 2 + j = (1 + j) + 1 by omega]
    refine fail_succ_congr fun p hp ↦ ?_
    have hpz := rosserPrimes_subset hp
    have hpos : (0 : ℝ) < p := by exact_mod_cast (prime_of_mem_primesLT hpz).pos
    -- `y / p ≤ q` for every prime `q < p`
    have h1 : ∀ q ∈ primesLT p, y / p ≤ q := fun q hq ↦ by
      have := (h.div hpz) {q} (singleton_subset_iff.2 hq) (card_singleton (α := ℕ) q)
      simpa using this
    rw [Nat.add_comm 1 j]
    cases lower
    · -- the upper sieve: `p³ < y`, so there is no prime `q < p` at all
      rw [mem_rosserPrimes] at hp
      have hp3 : (p : ℝ) ^ 3 < y := hp.2.resolve_left (by simp)
      simp only [Bool.not_false, fail_true_succ]
      refine sum_congr rfl fun q hq ↦ absurd (h1 q hq) ?_
      have hqp := lt_of_mem_primesLT hq
      have hq0 : (0 : ℝ) ≤ q := q.cast_nonneg
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_primesLT hpz).one_lt.le
      rw [not_le, lt_div_iff₀' hpos]
      have h2 : (p : ℝ) * q < p * p := mul_lt_mul_of_pos_left hqp hpos
      have h3 : (p : ℝ) ^ 2 ≤ p ^ 3 := pow_le_pow_right₀ hp1 (by norm_num)
      nlinarith
    · -- the lower sieve: the next prime `q` would need `q³ < y / p ≤ q`
      simp only [Bool.not_true, fail_false_succ]
      congr 1
      refine sum_congr rfl fun q hq ↦ absurd (h1 q (rosserPrimes_subset hq)) ?_
      rw [mem_rosserPrimes] at hq
      have hq3 : (q : ℝ) ^ 3 < y / p := hq.2.resolve_left (by simp)
      have hq1 : (1 : ℝ) ≤ q := by
        exact_mod_cast (prime_of_mem_primesLT hq.1).one_lt.le
      rw [not_le]
      have h2 : (q : ℝ) ≤ q ^ 3 := le_self_pow₀ hq1 (by norm_num)
      linarith
  | succ r hr ih =>
    rw [show r + 1 + j = (r + j) + 1 by omega]
    exact fail_succ_congr fun p hp ↦ ih (h.div (rosserPrimes_subset hp))

theorem fail_add_eq_of_le_factorial (hr : 2 ≤ r) (h : y ≤ (r + 1).factorial) (j : ℕ) :
    fail lower (r + j) y z = fail lower r y z :=
  fail_add_eq hr (leProdPrimesLT_of_le_factorial h) j

/-! ### Stabilisation of the depth-truncated counts -/

/-- Elements of `rosserSet lower y z` with at least two prime factors (at least one for the
upper sieve) are smaller than `y`. -/
theorem lt_of_mem_rosserSet (hd : d ∈ rosserSet lower y z)
    (hω : (if lower then 2 else 1) ≤ #d.primeFactors) : (d : ℝ) < y := by
  induction z using primesLT_induction generalizing lower y d with
  | h z ih =>
    rcases mem_rosserSet.1 hd with rfl | ⟨p, hp, e, he, rfl⟩
    · cases lower <;> simp at hω
    have hpz := rosserPrimes_subset hp
    have hpp := prime_of_mem_primesLT hpz
    have hpos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    rw [card_primeFactors_mul_of_mem_rosserSet hpp he] at hω
    have key : (if (!lower) then 2 else 1) ≤ #e.primeFactors → ((p * e : ℕ) : ℝ) < y := by
      intro h
      have := ih p hpz he h
      push_cast
      rwa [lt_div_iff₀' hpos] at this
    cases lower
    · rw [mem_rosserPrimes] at hp
      have hp3 : (p : ℝ) ^ 3 < y := hp.2.resolve_left (by simp)
      by_cases h2 : 2 ≤ #e.primeFactors
      · exact key (by simpa using h2)
      -- `e` has at most one prime factor, each below `p`
      have he' : e ≤ p ^ #e.primeFactors := by
        conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree (squarefree_of_mem_rosserSet he)]
        exact prod_le_pow_card _ _ _ fun q hq ↦
          (Nat.cast_lt.1 (lt_of_mem_primesLT (primeFactors_subset_of_mem_rosserSet he hq))).le
      have hpe : p * e ≤ p ^ 3 := by
        calc p * e ≤ p * p ^ #e.primeFactors := Nat.mul_le_mul_left p he'
          _ = p ^ (#e.primeFactors + 1) := by ring
          _ ≤ p ^ 3 := Nat.pow_le_pow_right hpp.pos (by omega)
      exact lt_of_le_of_lt (by exact_mod_cast hpe) hp3
    · exact key (by simp at hω ⊢; omega)

/-- If every product of `r + 1 ≥ 2` distinct primes below `z` is at least `y`, no element of
`rosserSet lower y z` has more than `r` prime factors. -/
theorem card_primeFactors_le_of_mem_rosserSet (hr : 1 ≤ r) (h : LeProdPrimesLT (r + 1) y z)
    (hd : d ∈ rosserSet lower y z) : #d.primeFactors ≤ r := by
  by_contra hlt
  obtain ⟨T, hT, hcard⟩ := exists_subset_card_eq (s := d.primeFactors) (n := r + 1) (by omega)
  have hdy := lt_of_mem_rosserSet hd (by split_ifs <;> omega)
  have hyT := h T (hT.trans (primeFactors_subset_of_mem_rosserSet hd)) hcard
  have hTd : ∏ p ∈ T, p ≤ d := by
    refine Nat.le_of_dvd (pos_of_mem_rosserSet hd) ?_
    conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree (squarefree_of_mem_rosserSet hd)]
    exact prod_dvd_prod_of_subset _ _ _ hT
  have : (∏ p ∈ T, (p : ℝ)) ≤ d := by
    have h' := (Nat.cast_le (α := ℝ)).2 hTd
    push_cast at h'
    exact h'
  linarith

theorem card_filter_rosserSet_add_eq (hr : 1 ≤ r) (h : LeProdPrimesLT (r + 1) y z) (j : ℕ) :
    #((rosserSet lower y z).filter fun d ↦ #d.primeFactors ≤ r + j) =
      #((rosserSet lower y z).filter fun d ↦ #d.primeFactors ≤ r) := by
  congr 1
  refine filter_congr fun d hd ↦ ⟨fun _ ↦ card_primeFactors_le_of_mem_rosserSet hr h hd,
    fun h ↦ h.trans (Nat.le_add_right r j)⟩

/-! ### The numerical form -/

/-- `n (log n - 1) ≤ log n!`. -/
theorem mul_log_sub_one_le_log_factorial (n : ℕ) :
    (n : ℝ) * (log n - 1) ≤ log n.factorial := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := pow_div_factorial_le_exp _ hn'.le n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [div_le_iff₀ hf] at h
  have := log_le_log (by positivity) h
  rw [log_pow, log_mul (exp_pos _).ne' hf.ne', log_exp] at this
  linarith

/-- `log x ≤ 2 √x`. -/
theorem log_le_two_mul_sqrt {x : ℝ} (hx : 0 ≤ x) : log x ≤ 2 * √x := by
  have := log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← sqrt_eq_rpow] at this
  linarith

/-- [I71, p. 23]: if `r + 2 > 2 log y / log log y` and `y` is large then `y ≤ (r + 1)!`, so every
product of `r` distinct primes is at least `y`; moreover `r ≥ 2`. -/
theorem exists_le_factorial : ∃ y₀ : ℝ, ∀ y ≥ y₀, ∀ r : ℕ,
    2 * log y / log (log y) < r + 2 → 2 ≤ r ∧ y ≤ (r + 1).factorial := by
  refine ⟨exp (exp 49), fun y hy r hr ↦ ?_⟩
  have hy0 : 0 < y := (exp_pos _).trans_le hy
  set L := log y with hL
  set ℓ := log L with hℓ
  have hL49 : exp 49 ≤ L := by rw [hL, le_log_iff_exp_le hy0]; exact hy
  have hL0 : 0 < L := (exp_pos _).trans_le hL49
  have hℓ49 : 49 ≤ ℓ := by rw [hℓ, le_log_iff_exp_le hL0]; exact hL49
  have hℓ0 : 0 < ℓ := by linarith
  -- `ℓ ≤ L / 4`
  have hsqrtL : 64 ≤ L := by
    have := quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 49)
    linarith
  have hℓL : 4 * ℓ ≤ L := by
    have h1 := log_le_two_mul_sqrt hL0.le
    have h2 : 8 ≤ √L := by
      rw [show (8 : ℝ) = √64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
      exact sqrt_le_sqrt hsqrtL
    have h3 : √L * √L = L := mul_self_sqrt hL0.le
    nlinarith
  have hratio : 4 ≤ L / ℓ := by rw [le_div_iff₀ hℓ0]; linarith
  have h2Lℓ : 2 * L / ℓ = 2 * (L / ℓ) := by ring
  refine ⟨by exact_mod_cast (by linarith : (2 : ℝ) ≤ r), ?_⟩
  -- `log ℓ ≤ (ℓ - 3) / 3`
  have hlogℓ : 3 * log ℓ + 3 ≤ ℓ := by
    have h1 := log_le_two_mul_sqrt hℓ0.le
    have h2 : 7 ≤ √ℓ := by
      rw [show (7 : ℝ) = √49 by rw [show (49 : ℝ) = 7 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
      exact sqrt_le_sqrt hℓ49
    have h3 : √ℓ * √ℓ = ℓ := mul_self_sqrt hℓ0.le
    nlinarith
  set m := 3 * L / (2 * ℓ) with hm
  have hm0 : 0 < m := by positivity
  set n : ℕ := r + 1 with hn
  have hn_cast : (n : ℝ) = r + 1 := by rw [hn]; push_cast; ring
  have hmn : m ≤ n := by
    rw [hn_cast, hm]
    have : 3 * L / (2 * ℓ) = 3 / 2 * (L / ℓ) := by field_simp
    rw [this]
    linarith
  have hlogm : ℓ - log ℓ ≤ log m := by
    rw [hm, log_div (by positivity) (by positivity), log_mul (by norm_num) hL0.ne',
      log_mul (by norm_num) hℓ0.ne', ← hℓ]
    have : log 2 ≤ log 3 := log_le_log (by norm_num) (by norm_num)
    linarith
  have hkey : L ≤ m * (log m - 1) := by
    have h1 : 2 * ℓ / 3 ≤ log m - 1 := by linarith
    calc L = m * (2 * ℓ / 3) := by rw [hm]; field_simp
      _ ≤ m * (log m - 1) := by gcongr
  have hmono : m * (log m - 1) ≤ n * (log n - 1) := by
    have h1 : log m ≤ log n := log_le_log hm0 hmn
    have h2 : 0 ≤ log m - 1 := by
      by_contra h
      have : m * (log m - 1) < 0 := mul_neg_of_pos_of_neg hm0 (not_le.1 h)
      linarith
    nlinarith
  have hfact := mul_log_sub_one_le_log_factorial n
  have : L ≤ log n.factorial := by linarith
  rw [hL, ← exp_le_exp, exp_log hy0, exp_log (by exact_mod_cast n.factorial_pos)] at this
  exact this

/-- [I71, p. 23]: for `y ≥ y₀` and `r + 2 > 2 log y / log log y`, the deficits do not change
beyond depth `r`. -/
theorem exists_fail_add_eq : ∃ y₀ : ℝ, ∀ y ≥ y₀, ∀ (lower : Bool) (r : ℕ) (z : ℝ),
    2 * log y / log (log y) < r + 2 → ∀ j, fail lower (r + j) y z = fail lower r y z := by
  obtain ⟨y₀, hy₀⟩ := exists_le_factorial
  refine ⟨y₀, fun y hy lower r z hr j ↦ ?_⟩
  obtain ⟨h2, hf⟩ := hy₀ y hy r hr
  exact fail_add_eq_of_le_factorial h2 hf j

/-- [I71, p. 26]: for `y ≥ y₀` and `r + 2 > 2 log y / log log y`, no element of
`rosserSet lower y z` has more than `r - 1` prime factors; in particular the depth-truncated
counts do not change beyond depth `r`. -/
theorem exists_card_filter_rosserSet_add_eq : ∃ y₀ : ℝ, ∀ y ≥ y₀, ∀ (lower : Bool) (r : ℕ)
    (z : ℝ), 2 * log y / log (log y) < r + 2 → ∀ j,
      #((rosserSet lower y z).filter fun d ↦ #d.primeFactors ≤ r - 1 + j) =
        #((rosserSet lower y z).filter fun d ↦ #d.primeFactors ≤ r - 1) := by
  obtain ⟨y₀, hy₀⟩ := exists_le_factorial
  refine ⟨y₀, fun y hy lower r z hr j ↦ ?_⟩
  obtain ⟨h2, hf⟩ := hy₀ y hy r hr
  have h := leProdPrimesLT_of_le_factorial (z := z) hf
  rw [show r = r - 1 + 1 by omega] at h
  exact card_filter_rosserSet_add_eq (by omega) h j

end IwaniecLinearSieve
