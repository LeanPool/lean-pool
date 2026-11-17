/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The cumulant envelope of BKL Section 6

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 6, (94)–(106): the envelope
`b_m = K^{m-1} ((m-1)!)²` of the induction (95) proving Theorem 4.1, the binomial identity (105)
`C(m-1, a-1) √(b_a b_{m-a+1}) = √b_m` and the recurrence `b_m = K (m-1)² b_{m-1}`. These are the
deterministic arithmetic of the induction; they prove nothing about cumulants by themselves.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.KLS.BKL

/-- The cumulant envelope `b_m = K^{m-1} ((m-1)!)²` of BKL (94). -/
def envelope (K : ℝ) (m : ℕ) : ℝ := K ^ (m - 1) * ((m - 1).factorial : ℝ) ^ 2

theorem envelope_nonneg {K : ℝ} (hK : 0 ≤ K) (m : ℕ) : 0 ≤ envelope K m := by
  unfold envelope
  positivity

/-- **BKL (105)**: `C(m-1, a-1) √(b_a b_{m-a+1}) = √b_m` for `1 ≤ a ≤ m` (the source uses
`2 ≤ a ≤ m - 2`). -/
theorem choose_mul_sqrt_envelope {K : ℝ} (hK : 0 ≤ K) {m a : ℕ} (ha : 1 ≤ a) (ham : a ≤ m) :
    ((m - 1).choose (a - 1) : ℝ) * Real.sqrt (envelope K a * envelope K (m - a + 1)) =
      Real.sqrt (envelope K m) := by
    have hsub : m - a + 1 - 1 = m - a := by
      omega
    have hpow : (a - 1) + (m - a) = m - 1 := by
      omega
    have hfac : ((m - 1).choose (a - 1) : ℝ) *
        ((a - 1).factorial : ℝ) * ((m - a).factorial : ℝ) =
        ((m - 1).factorial : ℝ) := by
      have hchoose := Nat.choose_mul_factorial_mul_factorial
        (n := m - 1) (k := a - 1) (by omega)
      have hsubfac : (m - 1) - (a - 1) = m - a := by
        omega
      rw [hsubfac] at hchoose
      exact_mod_cast hchoose
    have hprod :
        envelope K a * envelope K (m - a + 1) =
          K ^ (m - 1) *
            (((a - 1).factorial : ℝ) * ((m - a).factorial : ℝ)) ^ 2 := by
      simp only [envelope, hsub]
      calc
        K ^ (a - 1) * ((a - 1).factorial : ℝ) ^ 2 *
            (K ^ (m - a) * ((m - a).factorial : ℝ) ^ 2) =
            (K ^ (a - 1) * K ^ (m - a)) *
              (((a - 1).factorial : ℝ) ^ 2 *
                ((m - a).factorial : ℝ) ^ 2) := by ring
        _ = K ^ ((a - 1) + (m - a)) *
              (((a - 1).factorial : ℝ) ^ 2 *
                ((m - a).factorial : ℝ) ^ 2) := by
              rw [pow_add]
        _ = K ^ (m - 1) *
              (((a - 1).factorial : ℝ) * ((m - a).factorial : ℝ)) ^ 2 := by
              rw [hpow]
              ring
    have hsqrtprod :
        Real.sqrt (envelope K a * envelope K (m - a + 1)) =
          Real.sqrt (K ^ (m - 1)) *
            (((a - 1).factorial : ℝ) * ((m - a).factorial : ℝ)) := by
      rw [hprod, Real.sqrt_mul (pow_nonneg hK _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg]
      positivity
    have hsqrtm :
        Real.sqrt (envelope K m) =
          Real.sqrt (K ^ (m - 1)) * ((m - 1).factorial : ℝ) := by
      rw [envelope, Real.sqrt_mul (pow_nonneg hK _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg]
      positivity
    rw [hsqrtprod, hsqrtm]
    calc
      ((m - 1).choose (a - 1) : ℝ) *
          (Real.sqrt (K ^ (m - 1)) *
            (((a - 1).factorial : ℝ) * ((m - a).factorial : ℝ))) =
          Real.sqrt (K ^ (m - 1)) *
            (((m - 1).choose (a - 1) : ℝ) *
              ((a - 1).factorial : ℝ) * ((m - a).factorial : ℝ)) := by
                ring
      _ = Real.sqrt (K ^ (m - 1)) * ((m - 1).factorial : ℝ) := by
        rw [hfac]

/--
**The envelope recurrence** used to close the induction: `b_m = K (m-1)² b_{m-1}` for `m ≥ 2`. -/
theorem envelope_succ (K : ℝ) {m : ℕ} (hm : 2 ≤ m) :
    envelope K m = K * ((m - 1 : ℕ) : ℝ) ^ 2 * envelope K (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  simp only [envelope, show k + 2 - 1 = k + 1 by omega, Nat.factorial_succ, pow_succ]
  push_cast
  ring


/-- **BKL (106)**: the `m - 3` summands `2 ≤ a ≤ m - 2` of (104) each equal `√b_m`, so their sum is
`(m - 3) √b_m` (empty for `m = 3`). -/
theorem sum_choose_mul_sqrt_envelope {K : ℝ} (hK : 0 ≤ K) {m : ℕ} (hm : 3 ≤ m) :
    ∑ a ∈ Finset.Icc 2 (m - 2),
        ((m - 1).choose (a - 1) : ℝ) * Real.sqrt (envelope K a * envelope K (m - a + 1)) =
      ((m - 3 : ℕ) : ℝ) * Real.sqrt (envelope K m) := by
    have hsum :
        ∑ a ∈ Finset.Icc 2 (m - 2),
            ((m - 1).choose (a - 1) : ℝ) *
              Real.sqrt (envelope K a * envelope K (m - a + 1)) =
          ∑ _a ∈ Finset.Icc 2 (m - 2), Real.sqrt (envelope K m) := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := Finset.mem_Icc.mp ha
      exact choose_mul_sqrt_envelope hK (by omega) (by omega)
    have hcard : (Finset.Icc 2 (m - 2)).card = m - 3 := by
      rw [Nat.card_Icc]
      omega
    calc
      ∑ a ∈ Finset.Icc 2 (m - 2),
          ((m - 1).choose (a - 1) : ℝ) *
            Real.sqrt (envelope K a * envelope K (m - a + 1)) =
          ∑ _a ∈ Finset.Icc 2 (m - 2), Real.sqrt (envelope K m) := hsum
      _ = (Finset.Icc 2 (m - 2)).card • Real.sqrt (envelope K m) := by
        rw [Finset.sum_const]
      _ = ((m - 3 : ℕ) : ℝ) * Real.sqrt (envelope K m) := by
        rw [hcard]
        simp [nsmul_eq_mul]

/-- **Scalar absorption in the final estimate** (BKL p. 27, after (106)): for `m ≥ 3`,
`2 C m² b_{m-1} + 4 (m-3) √(b_{m-1} b_m) ≤ b_m` once `K ≥ 9C` and `K ≥ 64`. Stated for `C ≥ 0`
(the source takes `C ≥ 1`, `K ≥ max{5, 9C, 64}`). This is the arithmetic step only; it does not
close the induction (95) by itself. -/
theorem absorption_le_envelope {K C : ℝ} (hC : 0 ≤ C) (hK9 : 9 * C ≤ K) (hK64 : 64 ≤ K)
    {m : ℕ} (hm : 3 ≤ m) :
    2 * C * (m : ℝ) ^ 2 * envelope K (m - 1) +
        4 * ((m - 3 : ℕ) : ℝ) * Real.sqrt (envelope K (m - 1) * envelope K m) ≤
      envelope K m := by
    have hKnon : 0 ≤ K := by
      linarith
    have hm2 : 2 ≤ m := by
      omega
    have hm1 : 1 ≤ m := by
      omega
    have hm3 : 3 ≤ m := hm
    have hb : 0 ≤ envelope K (m - 1) := by
      exact envelope_nonneg (K := K) hKnon (m - 1)
    have hrec := envelope_succ K hm2
    have hcast1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm1]
      norm_num
    have hcast3 : ((m - 3 : ℕ) : ℝ) = (m : ℝ) - 3 := by
      rw [Nat.cast_sub hm3]
      norm_num
    have hr : 0 ≤ (m : ℝ) - 1 := by
      rw [← hcast1]
      exact_mod_cast (Nat.zero_le (m - 1))
    have ht : 0 ≤ (m : ℝ) - 3 := by
      rw [← hcast3]
      exact_mod_cast (Nat.zero_le (m - 3))
    have hpoly : 4 * (m : ℝ) ^ 2 ≤ 9 * ((m : ℝ) - 1) ^ 2 := by
      have hfive : 0 ≤ 5 * (m : ℝ) - 3 := by
        nlinarith
      have hp : 0 ≤ ((m : ℝ) - 3) * (5 * (m : ℝ) - 3) :=
        mul_nonneg ht hfive
      nlinarith
    have hA : 4 * C * (m : ℝ) ^ 2 ≤ K * ((m : ℝ) - 1) ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hpoly hC
      have h2 := mul_le_mul_of_nonneg_right hK9
        (sq_nonneg ((m : ℝ) - 1))
      nlinarith
    have hsK0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
    have hsKsq : (Real.sqrt K) ^ 2 = K := by
      simpa using Real.sq_sqrt hKnon
    have hsK : 8 ≤ Real.sqrt K := by
      nlinarith
    have hB : 8 * ((m : ℝ) - 3) ≤ Real.sqrt K * ((m : ℝ) - 1) := by
      have h1 : 8 * ((m : ℝ) - 3) ≤ 8 * ((m : ℝ) - 1) := by
        nlinarith
      have h2 : 8 * ((m : ℝ) - 1) ≤ Real.sqrt K * ((m : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right hsK hr
      linarith
    have hmul :=
      mul_le_mul_of_nonneg_right hB
        (mul_nonneg hsK0 hr)
    have hcore :
        2 * C * (m : ℝ) ^ 2 +
            4 * ((m : ℝ) - 3) * Real.sqrt K * ((m : ℝ) - 1) ≤
          K * ((m : ℝ) - 1) ^ 2 := by
      nlinarith [hA, hmul, hsKsq]
    have hsq : 0 ≤ ((m : ℝ) - 1) ^ 2 :=
      sq_nonneg ((m : ℝ) - 1)
    have hKsq : 0 ≤ K * ((m : ℝ) - 1) ^ 2 :=
      mul_nonneg hKnon hsq
    have hx' :
        0 ≤ envelope K (m - 1) *
          (K * ((m : ℝ) - 1) ^ 2 * envelope K (m - 1)) := by
      exact mul_nonneg hb (mul_nonneg hKsq hb)
    have hs :
        Real.sqrt (envelope K (m - 1) * envelope K m) ^ 2 =
          envelope K (m - 1) *
            (K * ((m : ℝ) - 1) ^ 2 * envelope K (m - 1)) := by
      calc
        Real.sqrt (envelope K (m - 1) * envelope K m) ^ 2 =
            Real.sqrt
              (envelope K (m - 1) *
                (K * ((m : ℝ) - 1) ^ 2 * envelope K (m - 1))) ^ 2 := by
              rw [hrec, hcast1]
        _ = envelope K (m - 1) *
            (K * ((m : ℝ) - 1) ^ 2 * envelope K (m - 1)) :=
          Real.sq_sqrt hx'
    have hq : 0 ≤ Real.sqrt K * ((m : ℝ) - 1) * envelope K (m - 1) :=
      mul_nonneg (mul_nonneg hsK0 hr) hb
    have hq_sq :
        (Real.sqrt K * ((m : ℝ) - 1) * envelope K (m - 1)) ^ 2 =
          envelope K (m - 1) *
            (K * ((m : ℝ) - 1) ^ 2 * envelope K (m - 1)) := by
      calc
        (Real.sqrt K * ((m : ℝ) - 1) * envelope K (m - 1)) ^ 2 =
            (Real.sqrt K) ^ 2 * ((m : ℝ) - 1) ^ 2 *
              envelope K (m - 1) ^ 2 := by ring
        _ = envelope K (m - 1) *
            (K * ((m : ℝ) - 1) ^ 2 * envelope K (m - 1)) := by
          rw [hsKsq]
          ring
    have hroot :
        Real.sqrt (envelope K (m - 1) * envelope K m) =
          Real.sqrt K * ((m : ℝ) - 1) * envelope K (m - 1) := by
      nlinarith [hs, hq_sq,
        Real.sqrt_nonneg (envelope K (m - 1) * envelope K m)]
    have hfinal := mul_le_mul_of_nonneg_right hcore hb
    calc
      2 * C * (m : ℝ) ^ 2 * envelope K (m - 1) +
            4 * ((m - 3 : ℕ) : ℝ) *
              Real.sqrt (envelope K (m - 1) * envelope K m) =
          (2 * C * (m : ℝ) ^ 2 +
            4 * ((m : ℝ) - 3) * Real.sqrt K * ((m : ℝ) - 1)) *
              envelope K (m - 1) := by
            rw [hroot, hcast3]
            ring
      _ ≤ K * ((m : ℝ) - 1) ^ 2 * envelope K (m - 1) := hfinal
      _ = envelope K m := by
        rw [hrec, hcast1]

end FunctionalInequalities.KLS.BKL
