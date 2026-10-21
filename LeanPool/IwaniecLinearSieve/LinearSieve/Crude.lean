/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.PrimeSums.Product
public import LeanPool.IwaniecLinearSieve.Rosser
import LeanPool.IwaniecLinearSieve.LinearSieve.Depth
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Polynomial.Basic

/-!
# The crude bound for deep terms ([I71, pp. 24, 27])

A failing tuple `p₁ > ⋯ > p_l` (all `< z`) of depth `l` satisfies `p₁ ⋯ p_l p_l² ≥ y`, so
`z^{l+2} > y`; it contributes `R(p_l)/(p₁ ⋯ p_l) ≤ 1/(p₁ ⋯ p_l)`, and the sum of
`1/(p₁ ⋯ p_l)` over `z > p₁ > ⋯ > p_l` is at most `(∑_{p<z} 1/p)^l / l!`. Hence
(`fail_le_sum_SLT_pow`)
    fail lower r y z ≤ ∑_{1 ≤ l ≤ r, y < z^{l+2}} SLT(z)^l / l!,

which is [I71]'s `Q_{m+1,y}(ξ-1) < ∑_{k > ξ-3} (∑_{p<y} 1/p)^k / k!` (with `z = y^{1/(ξ-1)}`).
With the tail estimate `sum_pow_div_factorial_le` (`∑_{l > u} X^l / l! ≤ 2 (e X / u)^u` for
`2 e X ≤ u`) and `SLT_le_loglog` (`SLT z ≤ log log z + C`) this gives `fail_le_tail`:
    z^{u+2} ≤ y, SLT z ≤ X, 2 e X ≤ u → fail lower r y z ≤ 2 (e X / u)^u
                                        = 2 exp (-(u log u) + u log X + u).

For the counts ([I71, p. 27]): elements with `l ≥ 2` prime factors (`l ≥ 1` for the upper sieve)
are `< y`, and `∑_{d ∈ D, ω(d) = l} 1/d ≤ SLT(z)^l / l!`, so
`#{d ∈ D | ω(d) ≥ k} ≤ y ∑_{k ≤ l ≤ π(z)} SLT(z)^l / l!` (`card_filter_le_mul_sum`); also
`#{d ∈ D | ω(d) = l} ≤ π(z)^l / l!` (`card_filter_eq_le_pow_div`).
-/

@[expose] public section

open Finset Real

namespace IwaniecLinearSieve

/-! ### Discrete integration -/

/-- `a^{n+1} + (n+1) a^n b ≤ (a + b)^{n+1}` for `a, b ≥ 0`. -/
theorem pow_succ_add_mul_le_add_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    a ^ (n + 1) + (n + 1) * a ^ n * b ≤ (a + b) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 0 ≤ a ^ n := pow_nonneg ha n
    have h2 : 0 ≤ (n + 1 : ℝ) * a ^ n * b * b := by positivity
    calc a ^ (n + 1 + 1) + ((n + 1 : ℕ) + 1 : ℝ) * a ^ (n + 1) * b
        ≤ (a + b) * (a ^ (n + 1) + (n + 1) * a ^ n * b) := by
          push_cast
          rw [pow_succ a (n + 1), pow_succ a n]
          nlinarith [mul_nonneg h1 hb]
      _ ≤ (a + b) * (a + b) ^ (n + 1) := by gcongr
      _ = (a + b) ^ (n + 1 + 1) := by ring

/-- Discrete form of `∫ F(t)^n dF(t) ≤ F^{n+1}/(n+1)`: for weights `w ≥ 0` on a finite set
of naturals, `∑_{p ∈ s} (∑_{q ∈ s, q < p} w q)^n w p ≤ (∑_{q ∈ s} w q)^{n+1} / (n+1)`. -/
theorem sum_pow_sum_lt_mul_le (s : Finset ℕ) {w : ℕ → ℝ} (hw : ∀ p ∈ s, 0 ≤ w p) (n : ℕ) :
    ∑ p ∈ s, (∑ q ∈ s.filter (· < p), w q) ^ n * w p ≤ (∑ q ∈ s, w q) ^ (n + 1) / (n + 1) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h ↦ lt_irrefl a (hlt a h)
    have hw' : ∀ p ∈ s, 0 ≤ w p := fun p hp ↦ hw p (mem_insert_of_mem hp)
    have hwa : 0 ≤ w a := hw a (mem_insert_self a s)
    have hfa : (insert a s).filter (· < a) = s := by
      ext q
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hq, hqa⟩
        · exact absurd hqa (lt_irrefl _)
        · exact hq
      · intro hq
        exact ⟨Or.inr hq, hlt q hq⟩
    have hfp : ∀ p ∈ s, (insert a s).filter (· < p) = s.filter (· < p) := by
      intro p hp
      rw [filter_insert, ite_eq_right (not_lt.2 (hlt p hp).le)]
    have hsum : ∑ p ∈ s, (∑ q ∈ (insert a s).filter (· < p), w q) ^ n * w p =
        ∑ p ∈ s, (∑ q ∈ s.filter (· < p), w q) ^ n * w p :=
      sum_congr rfl fun p hp ↦ by rw [hfp p hp]
    rw [sum_insert has, sum_insert has, hfa, hsum]
    have hS : 0 ≤ ∑ q ∈ s, w q := sum_nonneg hw'
    have := pow_succ_add_mul_le_add_pow hS hwa n
    have hn : (0 : ℝ) < n + 1 := by positivity
    calc (∑ q ∈ s, w q) ^ n * w a + ∑ p ∈ s, (∑ q ∈ s.filter (· < p), w q) ^ n * w p
        ≤ (∑ q ∈ s, w q) ^ n * w a + (∑ q ∈ s, w q) ^ (n + 1) / (n + 1) := by
          gcongr
          exact ih hw'
      _ ≤ (w a + ∑ q ∈ s, w q) ^ (n + 1) / (n + 1) := by
          rw [add_comm (w a), le_div_iff₀ hn, add_mul, div_mul_cancel₀ _ hn.ne']
          nlinarith

/-- `∑_{p < z} SLT(p)^n / p ≤ SLT(z)^{n+1} / (n+1)`. -/
theorem sum_SLT_pow_div_le (n : ℕ) (z : ℝ) :
    ∑ p ∈ primesLT z, SLT p ^ n / p ≤ SLT z ^ (n + 1) / (n + 1) := by
  have h := sum_pow_sum_lt_mul_le (primesLT z) (w := fun p ↦ (p : ℝ)⁻¹)
    (fun p _ ↦ by positivity) n
  refine le_of_eq_of_le (sum_congr rfl fun p hp ↦ ?_) h
  rw [filter_lt_primesLT hp, SLT, div_eq_mul_inv]

/-- `∑_{p < z} (SLT(p)^n / n!) / p ≤ SLT(z)^{n+1} / (n+1)!`. -/
theorem sum_SLT_pow_div_factorial_div_le (n : ℕ) (z : ℝ) :
    ∑ p ∈ primesLT z, SLT p ^ n / n.factorial / p ≤
      SLT z ^ (n + 1) / (n + 1).factorial := by
  have h := sum_SLT_pow_div_le n z
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  calc ∑ p ∈ primesLT z, SLT p ^ n / n.factorial / p
      = (∑ p ∈ primesLT z, SLT p ^ n / p) / n.factorial := by
        rw [sum_div]
        exact sum_congr rfl fun p _ ↦ by ring
    _ ≤ SLT z ^ (n + 1) / (n + 1) / n.factorial := by gcongr
    _ = SLT z ^ (n + 1) / (n + 1).factorial := by
        rw [Nat.factorial_succ]
        push_cast
        rw [div_div, mul_comm]

theorem SLT_nonneg (z : ℝ) : 0 ≤ SLT z := sum_nonneg fun p _ ↦ by positivity

theorem R_le_one (z : ℝ) : R z ≤ 1 :=
  prod_le_one₀ (fun p hp ↦ sub_nonneg.2 <| inv_le_one_of_one_le₀ <| by
    exact_mod_cast (mem_primesLT.1 hp).1.one_lt.le) fun p _ ↦ one_sub_inv_le_one p

/-! ### The crude bound for `fail` -/

/-- The crude bound in "shifted" form: depth `l + 1` contributes only if `y < z^{l+3}`. -/
theorem fail_le_sum_ite (lower : Bool) (r : ℕ) (y z : ℝ) :
    fail lower r y z ≤ ∑ l ∈ range r,
      if y < z ^ (l + 3) then SLT z ^ (l + 1) / (l + 1).factorial else 0 := by
  induction r generalizing lower y z with
  | zero => simp
  | succ r ih =>
    -- the contribution of depth `≥ 2`
    have hA : ∑ p ∈ rosserPrimes lower y z, fail (!lower) r (y / p) p / p ≤
        ∑ l ∈ range r, if y < z ^ (l + 1 + 3) then
          SLT z ^ (l + 1 + 1) / (l + 1 + 1).factorial else 0 := by
      calc ∑ p ∈ rosserPrimes lower y z, fail (!lower) r (y / p) p / p
          ≤ ∑ p ∈ primesLT z, fail (!lower) r (y / p) p / p :=
            sum_le_sum_of_subset_of_nonneg rosserPrimes_subset fun p _ _ ↦
              div_nonneg (fail_nonneg _ _ _ _) p.cast_nonneg
        _ ≤ ∑ p ∈ primesLT z, (∑ l ∈ range r, if y / p < (p : ℝ) ^ (l + 3) then
              SLT p ^ (l + 1) / (l + 1).factorial else 0) / p := by
            gcongr with p
            exact ih _ _ _
        _ = ∑ l ∈ range r, ∑ p ∈ primesLT z, (if y / p < (p : ℝ) ^ (l + 3) then
              SLT p ^ (l + 1) / (l + 1).factorial else 0) / p := by
            simp_rw [sum_div]
            exact sum_comm
        _ ≤ _ := by
            refine sum_le_sum fun l _ ↦ ?_
            split_ifs with hyz
            · calc ∑ p ∈ primesLT z, (if y / p < (p : ℝ) ^ (l + 3) then
                    SLT p ^ (l + 1) / (l + 1).factorial else 0) / p
                  ≤ ∑ p ∈ primesLT z, SLT p ^ (l + 1) / (l + 1).factorial / p := by
                    gcongr with p
                    split_ifs
                    · exact le_rfl
                    · have := SLT_nonneg p
                      positivity
                _ ≤ _ := sum_SLT_pow_div_factorial_div_le (l + 1) z
            · refine (sum_eq_zero fun p hp ↦ ?_).le
              rw [ite_eq_right, zero_div]
              intro h
              have hpos : (0 : ℝ) < p := by exact_mod_cast (prime_of_mem_primesLT hp).pos
              rw [div_lt_iff₀ hpos, ← pow_succ] at h
              exact hyz (h.trans (pow_lt_pow_left₀ (lt_of_mem_primesLT hp) hpos.le
                (by omega)))
    -- the contribution of depth `1`
    have hE : ∑ p ∈ (primesLT z).filter (fun p : ℕ ↦ ¬ (p : ℝ) ^ 3 < y), R p / p ≤
        if y < z ^ (0 + 3) then SLT z ^ (0 + 1) / (0 + 1).factorial else 0 := by
      split_ifs with hyz
      · simp only [zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one, SLT]
        calc ∑ p ∈ (primesLT z).filter (fun p : ℕ ↦ ¬ (p : ℝ) ^ 3 < y), R p / p
            ≤ ∑ p ∈ (primesLT z).filter (fun p : ℕ ↦ ¬ (p : ℝ) ^ 3 < y), (p : ℝ)⁻¹ := by
              gcongr with p
              rw [div_eq_mul_inv]
              exact mul_le_of_le_one_left (by positivity) (R_le_one p)
          _ ≤ ∑ p ∈ primesLT z, (p : ℝ)⁻¹ :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ ↦ by positivity
      · refine (sum_eq_zero fun p hp ↦ ?_).le
        rw [mem_filter] at hp
        exact absurd ((not_lt.1 hp.2).trans_lt (pow_lt_pow_left₀ (lt_of_mem_primesLT hp.1)
          p.cast_nonneg (by norm_num))) hyz
    rw [sum_range_succ']
    cases lower
    · rw [fail_false_succ]
      exact add_le_add hA hE
    · rw [fail_true_succ, ← rosserPrimes_true, ← add_zero (∑ p ∈ _, _ / _)]
      refine add_le_add hA ?_
      have := SLT_nonneg z
      split_ifs <;> positivity

/-- [I71, p. 24]: the deficits are bounded by the sum of `SLT(z)^l / l!` over the depths
`1 ≤ l ≤ r` for which `y < z^{l+2}`. -/
theorem fail_le_sum_SLT_pow (lower : Bool) (r : ℕ) (y z : ℝ) :
    fail lower r y z ≤ ∑ l ∈ Icc 1 r with y < z ^ (l + 2), SLT z ^ l / l.factorial := by
  refine (fail_le_sum_ite lower r y z).trans_eq ?_
  rw [sum_filter]
  refine sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [mem_range, mem_Icc] at hl ⊢
    omega
  · intro l hl
    simp only [mem_range, mem_Icc] at hl ⊢
    omega
  · intro l _
    simp
  · intro l hl
    simp only [mem_Icc] at hl
    omega
  · intro l _
    simp only [show l + 3 = l + 1 + 2 by ring]

/-! ### Tail estimates -/

/-- `X^k / k! ≤ (e X / k)^k`. -/
theorem pow_div_factorial_le_pow {X : ℝ} (hX : 0 ≤ X) (k : ℕ) :
    X ^ k / k.factorial ≤ (exp 1 * X / k) ^ k := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h := pow_div_factorial_le_exp _ hk'.le k
  rw [div_le_iff₀ hf] at h
  rw [div_pow, mul_pow, ← exp_nat_mul, mul_one, div_le_div_iff₀ hf (by positivity)]
  calc X ^ k * k ^ k ≤ X ^ k * (exp k * k.factorial) := by gcongr
    _ = exp k * X ^ k * k.factorial := by ring

/-- [I71, p. 24]: the tail `∑_{l > u} X^l / l!` (over any finite set of `l > u`) is at most
`2 (e X / u)^u` when `2 e X ≤ u`. -/
theorem sum_pow_div_factorial_le {X u : ℝ} (hX : 0 ≤ X) (hu : 0 < u) (h : 2 * exp 1 * X ≤ u)
    (s : Finset ℕ) (hs : ∀ l ∈ s, u < l) :
    ∑ l ∈ s, X ^ l / l.factorial ≤ 2 * (exp 1 * X / u) ^ u := by
  set k := ⌊u⌋₊ + 1 with hk
  have huk : u < k := by rw [hk]; push_cast; exact Nat.lt_floor_add_one u
  have hks : ∀ l ∈ s, k ≤ l := fun l hl ↦ by
    rw [hk, Nat.add_one_le_iff, Nat.floor_lt hu.le]
    exact hs l hl
  have he : 1 ≤ exp 1 := one_le_exp zero_le_one
  have h2X : 2 * X ≤ k + 1 := by nlinarith
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  -- each term is at most `X^k/k! · 2^{-(l-k)}`
  have hterm : ∀ j : ℕ, X ^ (k + j) / (k + j).factorial ≤
      X ^ k / k.factorial * (1 / 2) ^ j := by
    intro j
    have h1 : ((k.factorial * (k + 1) ^ j : ℕ) : ℝ) ≤ (k + j).factorial := by
      exact_mod_cast Nat.factorial_mul_pow_le_factorial
    push_cast at h1
    have hpos : (0 : ℝ) < k.factorial * (k + 1) ^ j := by positivity
    calc X ^ (k + j) / (k + j).factorial ≤ X ^ (k + j) / (k.factorial * (k + 1) ^ j) := by
          gcongr
      _ = X ^ k / k.factorial * (X / (k + 1)) ^ j := by
          rw [pow_add, div_pow]
          field_simp
      _ ≤ X ^ k / k.factorial * (1 / 2) ^ j := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ j)
            (by positivity)
          rw [div_le_iff₀ (by positivity)]
          linarith
  set N := s.sup id + 1
  have hsub : s ⊆ Ico k N := fun l hl ↦
    mem_Ico.2 ⟨hks l hl, Nat.lt_succ_of_le (le_sup (f := id) hl)⟩
  calc ∑ l ∈ s, X ^ l / l.factorial
      ≤ ∑ l ∈ s, X ^ k / k.factorial * (1 / 2) ^ (l - k) := by
        refine sum_le_sum fun l hl ↦ ?_
        have := hterm (l - k)
        rwa [Nat.add_sub_cancel' (hks l hl)] at this
    _ ≤ ∑ l ∈ Ico k N, X ^ k / k.factorial * (1 / 2) ^ (l - k) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
    _ = X ^ k / k.factorial * ∑ j ∈ range (N - k), (1 / 2 : ℝ) ^ j := by
        rw [← mul_sum, sum_Ico_eq_sum_range]
        simp
    _ ≤ X ^ k / k.factorial * 2 := by
        gcongr
        exact sum_geometric_two_le _
    _ ≤ (exp 1 * X / k) ^ k * 2 := by gcongr; exact pow_div_factorial_le_pow hX k
    _ ≤ (exp 1 * X / u) ^ (k : ℝ) * 2 := by
        rw [rpow_natCast]
        gcongr
    _ ≤ (exp 1 * X / u) ^ u * 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
        refine rpow_le_rpow_of_exponent_ge' (by positivity) ?_ hu.le huk.le
        rw [div_le_one hu]
        nlinarith [exp_pos 1]
    _ = 2 * (exp 1 * X / u) ^ u := mul_comm _ _

/-- `(e X / u)^u = exp (-(u log u) + u log X + u)`. -/
theorem exp_one_mul_div_rpow {X u : ℝ} (hX : 0 < X) (hu : 0 < u) :
    (exp 1 * X / u) ^ u = exp (-(u * log u) + u * log X + u) := by
  rw [rpow_def_of_pos (by positivity), log_div (by positivity) hu.ne',
    log_mul (exp_pos 1).ne' hX.ne', log_exp]
  ring_nf

/-- The crude bound in the form used in [I71, p. 24]: if `z^{u+2} ≤ y` (i.e. `s ≥ u + 2` for
`z = y^{1/s}`), `SLT z ≤ X` and `2 e X ≤ u`, then `fail lower r y z ≤ 2 (e X / u)^u`. -/
theorem fail_le_tail {lower : Bool} {r : ℕ} {y z X u : ℝ} (hz : 1 < z) (hu : 0 < u)
    (hyz : z ^ (u + 2) ≤ y) (hX : SLT z ≤ X) (h : 2 * exp 1 * X ≤ u) :
    fail lower r y z ≤ 2 * (exp 1 * X / u) ^ u := by
  refine (fail_le_sum_SLT_pow lower r y z).trans ((sum_le_sum fun l _ ↦ ?_).trans
    (sum_pow_div_factorial_le ((SLT_nonneg z).trans hX) hu h _ fun l hl ↦ ?_))
  · gcongr
    exact SLT_nonneg z
  · have hl := (mem_filter.1 hl).2
    rw [← rpow_natCast] at hl
    have := (rpow_lt_rpow_left_iff hz).1 (hyz.trans_lt hl)
    push_cast at this
    linarith

/-- `fail_le_tail` with `z = y^{1/s}`: for `y > 1`, `s > 2`, `SLT (y^{1/s}) ≤ X` and
`2 e X ≤ s - 2`, `fail lower r y y^{1/s} ≤ 2 (e X / (s - 2))^{s - 2}`. -/
theorem fail_rpow_le_tail {lower : Bool} {r : ℕ} {y s X : ℝ} (hy : 1 < y) (hs : 2 < s)
    (hX : SLT (y ^ s⁻¹) ≤ X) (h : 2 * exp 1 * X ≤ s - 2) :
    fail lower r y (y ^ s⁻¹) ≤ 2 * (exp 1 * X / (s - 2)) ^ (s - 2) := by
  have hs0 : 0 < s := by linarith
  refine fail_le_tail (one_lt_rpow hy (inv_pos.2 hs0)) (by linarith) ?_ hX h
  rw [sub_add_cancel, ← rpow_mul (by linarith), inv_mul_cancel₀ hs0.ne', rpow_one]

/-- `SLT z ≤ log log z + C` for `z ≥ 2`. -/
theorem SLT_le_loglog : ∃ C : ℝ, ∀ z ≥ 2, SLT z ≤ log (log z) + C := by
  obtain ⟨c₅, C, hC⟩ := S_asymp
  refine ⟨c₅ + |C|, fun z hz ↦ ?_⟩
  have h1 := (S_sub_SLT (by linarith : (0 : ℝ) < z)).1
  have h2 := (abs_le.1 (hC z hz)).2
  have h3 : C * pntE z ≤ |C| := by
    calc
      C * pntE z ≤ |C| * pntE z :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pntE_nonneg z)
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left (pntE_le_one z) (abs_nonneg C)
      _ = |C| := mul_one _
  linarith

/-! ### Counts -/

/-- `∑_{d ∈ D, ω(d) = l} 1/d ≤ SLT(z)^l / l!`. -/
theorem sum_inv_filter_card_primeFactors_eq_le (lower : Bool) (y z : ℝ) (l : ℕ) :
    ∑ d ∈ (rosserSet lower y z).filter (fun d ↦ #d.primeFactors = l), (d : ℝ)⁻¹ ≤
      SLT z ^ l / l.factorial := by
  induction l generalizing lower y z with
  | zero =>
    rw [sum_filter, sum_rosserSet]
    simp only [Nat.primeFactors_one, card_empty, ite_true, Nat.cast_one, inv_one, pow_zero,
      Nat.factorial_zero, div_one]
    refine (add_eq_left.2 (sum_eq_zero fun p hp ↦ sum_eq_zero fun e he ↦ ?_)).le
    rw [card_primeFactors_mul_of_mem_rosserSet
      (prime_of_mem_primesLT (rosserPrimes_subset hp)) he, ite_eq_right (Nat.succ_ne_zero _)]
  | succ l ih =>
    rw [sum_filter, sum_rosserSet]
    simp only [Nat.primeFactors_one, card_empty, Nat.cast_one, inv_one]
    rw [ite_eq_right (Nat.succ_ne_zero l).symm, zero_add]
    calc ∑ p ∈ rosserPrimes lower y z, ∑ e ∈ rosserSet (!lower) (y / p) p,
          (if #(p * e).primeFactors = l + 1 then ((p * e : ℕ) : ℝ)⁻¹ else 0)
        = ∑ p ∈ rosserPrimes lower y z, (∑ e ∈ (rosserSet (!lower) (y / p) p).filter
            (fun e ↦ #e.primeFactors = l), (e : ℝ)⁻¹) / p := by
          refine sum_congr rfl fun p hp ↦ ?_
          rw [sum_filter, sum_div]
          refine sum_congr rfl fun e he ↦ ?_
          rw [card_primeFactors_mul_of_mem_rosserSet
            (prime_of_mem_primesLT (rosserPrimes_subset hp)) he]
          simp only [add_left_inj]
          split_ifs
          · push_cast
            rw [mul_inv, div_eq_mul_inv, mul_comm]
          · simp
      _ ≤ ∑ p ∈ rosserPrimes lower y z, SLT p ^ l / l.factorial / p := by
          gcongr with p
          exact ih _ _ _
      _ ≤ ∑ p ∈ primesLT z, SLT p ^ l / l.factorial / p :=
          sum_le_sum_of_subset_of_nonneg rosserPrimes_subset fun p _ _ ↦ by
            have := SLT_nonneg p
            positivity
      _ ≤ _ := sum_SLT_pow_div_factorial_div_le l z

/-- [I71, p. 27]: the number of elements of `rosserSet lower y z` with at least `k` prime
factors, for `k ≥ 2` (`k ≥ 1` for the upper sieve), is at most
`y ∑_{k ≤ l ≤ π(z)} SLT(z)^l / l!`. -/
theorem card_filter_le_mul_sum {lower : Bool} {y z : ℝ} {k : ℕ} (hy : 0 ≤ y)
    (hk : (if lower then 2 else 1) ≤ k) :
    (#((rosserSet lower y z).filter fun d ↦ k ≤ #d.primeFactors) : ℝ) ≤
      y * ∑ l ∈ Icc k #(primesLT z), SLT z ^ l / l.factorial := by
  set D := (rosserSet lower y z).filter fun d ↦ k ≤ #d.primeFactors
  calc (#D : ℝ) = ∑ d ∈ D, (1 : ℝ) := by simp
    _ ≤ ∑ d ∈ D, y * (d : ℝ)⁻¹ := by
        refine sum_le_sum fun d hd ↦ ?_
        obtain ⟨hd, hkd⟩ := mem_filter.1 hd
        have hdy := lt_of_mem_rosserSet hd (hk.trans hkd)
        have hd0 : (0 : ℝ) < d := by exact_mod_cast pos_of_mem_rosserSet hd
        rw [← div_eq_mul_inv, le_div_iff₀ hd0, one_mul]
        exact hdy.le
    _ = y * ∑ l ∈ Icc k #(primesLT z), ∑ d ∈ D.filter (fun d ↦ #d.primeFactors = l),
          (d : ℝ)⁻¹ := by
        rw [← mul_sum, sum_fiberwise_of_maps_to]
        intro d hd
        obtain ⟨hd, hkd⟩ := mem_filter.1 hd
        exact mem_Icc.2 ⟨hkd, card_le_card (primeFactors_subset_of_mem_rosserSet hd)⟩
    _ ≤ y * ∑ l ∈ Icc k #(primesLT z), SLT z ^ l / l.factorial := by
        gcongr with l
        refine le_trans ?_ (sum_inv_filter_card_primeFactors_eq_le lower y z l)
        refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ by positivity
        exact filter_subset_filter _ (filter_subset _ _)

/-- [I71, p. 27]: `#{d ∈ D | ω(d) ≥ k} ≤ 2 y (e X / u)^u` for `u < k`, `SLT z ≤ X` and
`2 e X ≤ u`, where `k ≥ 2` (`k ≥ 1` for the upper sieve). -/
theorem card_filter_le_tail {lower : Bool} {y z X u : ℝ} {k : ℕ} (hy : 0 ≤ y)
    (hk : (if lower then 2 else 1) ≤ k) (hu : 0 < u) (huk : u < k) (hX : SLT z ≤ X)
    (h : 2 * exp 1 * X ≤ u) :
    (#((rosserSet lower y z).filter fun d ↦ k ≤ #d.primeFactors) : ℝ) ≤
      2 * y * (exp 1 * X / u) ^ u := by
  refine (card_filter_le_mul_sum hy hk).trans ?_
  rw [mul_assoc, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ((sum_le_sum fun l _ ↦ ?_).trans
    (sum_pow_div_factorial_le ((SLT_nonneg z).trans hX) hu h _ fun l hl ↦ ?_)) hy
  · gcongr
    exact SLT_nonneg z
  · exact huk.trans_le (by exact_mod_cast (mem_Icc.1 hl).1)

/-- The number of elements of `rosserSet lower y z` with exactly `l` prime factors is at most
`π(z)^l / l!`. -/
theorem card_filter_eq_le_pow_div (lower : Bool) (y z : ℝ) (l : ℕ) :
    (#((rosserSet lower y z).filter fun d ↦ #d.primeFactors = l) : ℝ) ≤
      (#(primesLT z) : ℝ) ^ l / l.factorial := by
  refine le_trans ?_ (Nat.choose_le_pow_div l _)
  have : #((rosserSet lower y z).filter fun d ↦ #d.primeFactors = l) ≤
      #((primesLT z).powersetCard l) := by
    refine card_le_card_of_injOn (fun d ↦ d.primeFactors) (fun d hd ↦ ?_) fun d hd e he h ↦ ?_
    · obtain ⟨hd, hl⟩ := mem_filter.1 hd
      exact mem_powersetCard.2 ⟨primeFactors_subset_of_mem_rosserSet hd, hl⟩
    · have hd' := squarefree_of_mem_rosserSet (mem_filter.1 hd).1
      have he' := squarefree_of_mem_rosserSet (mem_filter.1 he).1
      rw [← Nat.prod_primeFactors_of_squarefree hd', ← Nat.prod_primeFactors_of_squarefree he']
      exact congrArg (fun T ↦ ∏ p ∈ T, p) h
  rw [card_powersetCard] at this
  exact_mod_cast this

end IwaniecLinearSieve
