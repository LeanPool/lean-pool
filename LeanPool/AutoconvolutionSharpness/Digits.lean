/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Heights and mass of the maximal - height blocks

The arguments follow Crmarić, Kovač, and Rupčić, §2. The collision estimate is proved
by the falling - factorial recurrence, so no probability space is needed.

Mathlib supplies the multinomial formula and the relation between falling factorials and binomial
coefficients. See the individual proofs for the declarations used.
-/

@[expose] public section

namespace Autoconvolutions.Digits

/-- A bound independent of the multiplicities, including repeated choices. -/
theorem multinomial_le_fact {ι : Type*} (I : Finset ι) (a : ι → ℕ) :
    Nat.multinomial I a ≤ (∑ i ∈ I, a i).factorial := by
  exact Nat.div_le_self _ _

/-- If every occupied digit was chosen only once, the bound is attained. -/
theorem multinomial_of_distinct {ι : Type*} (I : Finset ι) (a : ι → ℕ)
    (ha : ∀ i ∈ I, a i ≤ 1) :
    Nat.multinomial I a = (∑ i ∈ I, a i).factorial := by
  have hp : (∏ i ∈ I, (a i).factorial) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (ha i hi) with h | h <;> simp [h]
  simp [Nat.multinomial, hp]

/-- Proportion of ordered strings with no repeated letter. -/
noncomputable def distinctFraction (r k : ℕ) : ℝ :=
  (r.descFactorial k : ℝ) / (r : ℝ) ^ k

theorem distinctFraction_nonneg (r k : ℕ) : 0 ≤ distinctFraction r k := by
  unfold distinctFraction
  positivity

theorem distinctFraction_le_one {r : ℕ} (hr : 0 < r) (k : ℕ) :
    distinctFraction r k ≤ 1 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  apply (div_le_iff₀ (pow_pos hr' k)).2
  simpa only [one_mul, Nat.cast_pow] using
    (show (r.descFactorial k : ℝ) ≤ (r ^ k : ℕ) by exact_mod_cast Nat.descFactorial_le_pow r k)

/-- Extending a distinct string of length k has exactly r - k available choices.
The equality also holds when k exceeds the alphabet size. -/
theorem distinctFraction_recurrence {r : ℕ} (hr : 0 < r) (k : ℕ) :
    (r : ℝ) * distinctFraction r k =
      (r : ℝ) * distinctFraction r (k + 1) + (k : ℝ) * distinctFraction r k := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hrec : (r.descFactorial k : ℝ) * r =
      (r.descFactorial (k + 1) : ℝ) + k * (r.descFactorial k : ℝ) := by
    exact_mod_cast Nat.descFactorial_mul_self r k
  unfold distinctFraction
  calc
    _ = ((r.descFactorial (k + 1) : ℝ) + k * (r.descFactorial k : ℝ)) / (r : ℝ) ^ k := by
      rw [← hrec]
      ring
    _ = _ := by
      rw [pow_succ]
      field_simp [hr']

/-- Twice the alphabet size times the collision probability is at most k².
The sharp intermediate bound k(k - 1) is unnecessary for the final constant. -/
theorem collision_bound {r : ℕ} (hr : 0 < r) (k : ℕ) :
    2 * (r : ℝ) * (1 - distinctFraction r k) ≤ (k : ℝ) ^ 2 := by
  induction k with
  | zero => simp [distinctFraction]
  | succ k ih =>
    have hdrop := distinctFraction_recurrence hr k
    have hk : (0 : ℝ) ≤ k := by positivity
    have hstep := mul_nonneg hk (sub_nonneg.mpr (distinctFraction_le_one hr k))
    push_cast
    nlinarith only [ih, hdrop, hstep]

/-- The paper's good - block estimate, with the numbers of draws named u,v.
At level s use u=2n - s, v=2n + s. -/
theorem good_fraction {r b n u v : ℕ} (hn : 0 < n) (hb : 8 * n ^ 3 ≤ b)
    (hbr : b ≤ r) (huv : u + v = 4 * n) :
    1 - 1 / (n : ℝ) ≤ distinctFraction r u * distinctFraction b v := by
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hr0 : 0 < r := lt_of_lt_of_le hb0 hbr
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb' : 8 * (n : ℝ) ^ 3 ≤ b := by exact_mod_cast hb
  have hbr' : (b : ℝ) ≤ r := by exact_mod_cast hbr
  have huv' : (u : ℝ) + v = 4 * n := by exact_mod_cast huv
  have hu := sub_nonneg.mpr (distinctFraction_le_one hr0 u)
  have hv := sub_nonneg.mpr (distinctFraction_le_one hb0 v)
  have hpv := distinctFraction_nonneg b v
  have hboth : 0 ≤ 1 - distinctFraction r u * distinctFraction b v := by
    nlinarith only [hv, mul_nonneg hu hpv]
  have hcost : 2 * (b : ℝ) * (1 - distinctFraction r u * distinctFraction b v)
      ≤ (4 * (n : ℝ)) ^ 2 := by
    rw [← huv']
    nlinarith only [collision_bound hr0 u, collision_bound hb0 v,
      mul_nonneg (sub_nonneg.mpr hbr') hu,
      mul_nonneg (show (0 : ℝ) ≤ b by positivity) (mul_nonneg hu hv),
      mul_nonneg (show (0 : ℝ) ≤ u by positivity) (show (0 : ℝ) ≤ v by positivity)]
  have hnorm : (n : ℝ) * (1 - distinctFraction r u * distinctFraction b v) ≤ 1 := by
    by_contra! hx
    have hpos := mul_pos (show (0 : ℝ) < 16 * (n : ℝ) ^ 2 by positivity) (sub_pos.mpr hx)
    nlinarith only [hcost, mul_nonneg (sub_nonneg.mpr hb') hboth, hpos]
  have hdiv : 1 - distinctFraction r u * distinctFraction b v ≤ 1 / (n : ℝ) :=
    (le_div_iff₀ hn').2 (by simpa only [mul_comm (n : ℝ)] using hnorm)
  linarith

/-- Algebraic form of equation (mass), including its factorial and binomial
factors. Neither side involves floating - point arithmetic. -/
theorem good_mass {r b n u v : ℕ} (hn : 0 < n) (hb : 8 * n ^ 3 ≤ b)
    (hbr : b ≤ r) (huv : u + v = 4 * n) :
    (1 - 1 / (n : ℝ)) * ((r : ℝ) ^ u * (b : ℝ) ^ v) ≤
      (r.choose u : ℝ) * (b.choose v : ℝ) * (u.factorial : ℝ) * (v.factorial : ℝ) := by
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hr0 : 0 < r := lt_of_lt_of_le hb0 hbr
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb0
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr0
  have hg := good_fraction hn hb hbr huv
  unfold distinctFraction at hg
  rw [div_mul_div_comm] at hg
  have h := (le_div_iff₀ (mul_pos (pow_pos hrp u) (pow_pos hbp v))).mp hg
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at h
  push_cast at h
  nlinarith only [h]

end Autoconvolutions.Digits
