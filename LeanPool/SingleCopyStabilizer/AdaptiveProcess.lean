/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity


/-!
# A finite-tree tail bound for adaptive rank-decreasing processes

A state may store the entire previous history. At each state, a finite kernel
chooses an outcome and the state updates deterministically. Rank never
increases, and while positive it strictly decreases with probability at least
`p`. The probability of positive rank after `t` rounds is bounded using a
killed exponential potential. This yields a coarse exponential tail; it does
not establish the paper's sharper leading constant `2n`.
-/

@[expose] public section

noncomputable section

namespace LeanPool.SingleCopyStabilizer.AdaptiveProcess

open scoped BigOperators

/-- A finite outcome kernel together with a monotone natural-valued rank.
There is no Markov restriction: `S` can contain the complete history. -/
structure RankedProcess (S Ω : Type*) [Fintype Ω] where
  /-- Conditional probability of an outcome at the current state. -/
  weight : S → Ω → ℝ
  /-- State reached after observing the chosen outcome. -/
  next : S → Ω → S
  /-- Natural-valued obstruction whose disappearance marks success. -/
  rank : S → ℕ
  weight_nonneg : ∀ s o, 0 ≤ weight s o
  weight_sum : ∀ s, ∑ o, weight s o = 1
  rank_mono : ∀ s o, rank (next s o) ≤ rank s

/-- The exponential potential is killed on reaching rank zero. -/
def potential (r : ℕ) : ℝ := if r = 0 then 0 else 2 ^ r

@[simp] theorem potential_zero : potential 0 = 0 := by simp [potential]

theorem potential_nonneg (r : ℕ) : 0 ≤ potential r := by
  unfold potential
  split_ifs <;> positivity

theorem potential_le_pow (r : ℕ) : potential r ≤ (2 : ℝ) ^ r := by
  unfold potential
  split_ifs
  · positivity
  · exact le_rfl

theorem potential_mono {a b : ℕ} (h : a ≤ b) : potential a ≤ potential b := by
  by_cases ha : a = 0
  · simpa [ha] using potential_nonneg b
  have hb : b ≠ 0 := by omega
  simpa [potential, ha, hb] using
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h)

/-- Strict rank progress at least halves the killed exponential potential. -/
theorem potential_le_half_of_lt {a b : ℕ} (h : a < b) :
    potential a ≤ potential b / 2 := by
  have hb : b ≠ 0 := by omega
  by_cases ha : a = 0
  · rw [ha, potential_zero]
    exact div_nonneg (potential_nonneg b) (by norm_num)
  have hp : (2 : ℝ) ^ (a + 1) ≤ 2 ^ b :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_succ] at hp
  simp only [potential, ite_eq_right ha, ite_eq_right hb]
  linarith

variable {S Ω : Type*} [Fintype Ω]

namespace RankedProcess

variable (P : RankedProcess S Ω)

/-- Total probability assigned to strict progress at the current state. -/
def progressMass (s : S) : ℝ :=
  ∑ o, if P.rank (P.next s o) < P.rank s then P.weight s o else 0

/-- Probability of positive rank after the given number of rounds, defined
by the finite probability tree. Each recursive layer is one fresh kernel draw. -/
def failureProbability : ℕ → S → ℝ
  | 0, s => if P.rank s = 0 then 0 else 1
  | t + 1, s => ∑ o, P.weight s o * failureProbability t (P.next s o)

theorem failure_probability_nonneg (t : ℕ) (s : S) :
    0 ≤ P.failureProbability t s := by
  induction t generalizing s with
  | zero => simp only [failureProbability]; split_ifs <;> norm_num
  | succ t ih =>
      exact Finset.sum_nonneg fun o _ => mul_nonneg (P.weight_nonneg s o) (ih _)

theorem failure_probability_le_one (t : ℕ) (s : S) :
    P.failureProbability t s ≤ 1 := by
  induction t generalizing s with
  | zero => simp only [failureProbability]; split_ifs <;> norm_num
  | succ t ih =>
      calc
        P.failureProbability (t + 1) s =
            ∑ o, P.weight s o * P.failureProbability t (P.next s o) := rfl
        _ ≤ ∑ o, P.weight s o * 1 := Finset.sum_le_sum fun o _ =>
          mul_le_mul_of_nonneg_left (ih _) (P.weight_nonneg s o)
        _ = 1 := by simp [P.weight_sum]

/-- Rank zero is absorbing, so positive rank after `t` rounds is equivalent
to not having reached rank zero earlier. -/
theorem failure_probability_of_rank_zero (t : ℕ) (s : S) (hs : P.rank s = 0) :
    P.failureProbability t s = 0 := by
  induction t generalizing s with
  | zero => simp [failureProbability, hs]
  | succ t ih =>
      have hnext : ∀ o, P.rank (P.next s o) = 0 := fun o => by
        have hm := P.rank_mono s o
        omega
      simp [failureProbability, ih _ (hnext _)]

/-- A per-node strict-progress mass bound gives a one-step contraction
of the killed potential, including at the terminal states. -/
theorem potential_drift (p : ℝ)
    (hprogress : ∀ s, 0 < P.rank s → p ≤ P.progressMass s) (s : S) :
    (∑ o, P.weight s o * potential (P.rank (P.next s o))) ≤
      (1 - p / 2) * potential (P.rank s) := by
  by_cases hs : P.rank s = 0
  · have hnext : ∀ o, P.rank (P.next s o) = 0 := fun o => by
      have hm := P.rank_mono s o
      omega
    simp [hs, hnext]
  have hpoint (o : Ω) :
      P.weight s o * potential (P.rank (P.next s o)) ≤
        P.weight s o * potential (P.rank s) -
          (if P.rank (P.next s o) < P.rank s then P.weight s o else 0) *
            potential (P.rank s) / 2 := by
    split_ifs with hlt
    · have hh := mul_le_mul_of_nonneg_left (potential_le_half_of_lt hlt)
        (P.weight_nonneg s o)
      linarith
    · simpa using mul_le_mul_of_nonneg_left (potential_mono (P.rank_mono s o))
        (P.weight_nonneg s o)
  calc
    _ ≤ ∑ o, (P.weight s o * potential (P.rank s) -
        (if P.rank (P.next s o) < P.rank s then P.weight s o else 0) *
          potential (P.rank s) / 2) := Finset.sum_le_sum fun o _ => hpoint o
    _ = potential (P.rank s) - P.progressMass s * potential (P.rank s) / 2 := by
      simp only [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul,
        P.weight_sum, one_mul, progressMass]
    _ ≤ (1 - p / 2) * potential (P.rank s) := by
      have hh := mul_le_mul_of_nonneg_right (hprogress s (by omega))
        (potential_nonneg (P.rank s))
      nlinarith

/-- Finite adaptive-tree tail bound. The success assumption is checked at
every reachable or unreachable state of the supplied process, so it applies
uniformly to states encoding arbitrary previous histories. -/
theorem failure_probability_le_potential (p : ℝ) (hp : p ≤ 2)
    (hprogress : ∀ s, 0 < P.rank s → p ≤ P.progressMass s)
    (t : ℕ) (s : S) :
    P.failureProbability t s ≤ (1 - p / 2) ^ t * potential (P.rank s) := by
  have hq : 0 ≤ 1 - p / 2 := by linarith
  induction t generalizing s with
  | zero =>
      by_cases hs : P.rank s = 0
      · simp [failureProbability, potential, hs]
      · simpa [failureProbability, potential, hs] using
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2 ^ P.rank s)
  | succ t ih =>
      calc
        P.failureProbability (t + 1) s =
            ∑ o, P.weight s o * P.failureProbability t (P.next s o) := rfl
        _ ≤ ∑ o, P.weight s o * ((1 - p / 2) ^ t * potential (P.rank (P.next s o))) :=
          Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (ih _) (P.weight_nonneg s o)
        _ = (1 - p / 2) ^ t * ∑ o, P.weight s o * potential (P.rank (P.next s o)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro o _
          ring
        _ ≤ (1 - p / 2) ^ t * ((1 - p / 2) * potential (P.rank s)) :=
          mul_le_mul_of_nonneg_left (P.potential_drift p hprogress s) (pow_nonneg hq t)
        _ = (1 - p / 2) ^ (t + 1) * potential (P.rank s) := by rw [pow_succ]; ring

/-- A simpler tail bound using only an upper bound on the initial rank. -/
theorem failure_probability_le (p : ℝ) (hp : p ≤ 2)
    (hprogress : ∀ s, 0 < P.rank s → p ≤ P.progressMass s)
    (t n : ℕ) (s : S) (hrank : P.rank s ≤ n) :
    P.failureProbability t s ≤ (2 : ℝ) ^ n * (1 - p / 2) ^ t := by
  have hq : 0 ≤ 1 - p / 2 := by linarith
  have hpow : potential (P.rank s) ≤ (2 : ℝ) ^ n :=
    (potential_le_pow _).trans (pow_le_pow_right₀ (by norm_num) hrank)
  calc
    _ ≤ (1 - p / 2) ^ t * potential (P.rank s) :=
      P.failure_probability_le_potential p hp hprogress t s
    _ ≤ (1 - p / 2) ^ t * (2 : ℝ) ^ n := mul_le_mul_of_nonneg_left hpow (pow_nonneg hq t)
    _ = _ := by ring

/-- If each nonterminal state progresses with probability at least one
quarter, failure after `t` rounds is at most `2^n (7/8)^t`. -/
theorem failure_probability_le_seven_eighths
    (hprogress : ∀ s, 0 < P.rank s → (1 / 4 : ℝ) ≤ P.progressMass s)
    (t n : ℕ) (s : S) (hrank : P.rank s ≤ n) :
    P.failureProbability t s ≤ (2 : ℝ) ^ n * (7 / 8 : ℝ) ^ t := by
  convert P.failure_probability_le (1 / 4) (by norm_num) hprogress t n s hrank using 1
  norm_num

/-- A concrete confidence budget: `8(n+k)` rounds give failure probability
at most `2^(-k)` under the quarter-progress hypothesis. This is deliberately
coarser than the paper's sharp geometric-sum estimate. -/
theorem failure_probability_eight_rounds_per_bit
    (hprogress : ∀ s, 0 < P.rank s → (1 / 4 : ℝ) ≤ P.progressMass s)
    (n k : ℕ) (s : S) (hrank : P.rank s ≤ n) :
    P.failureProbability (8 * (n + k)) s ≤ (1 / 2 : ℝ) ^ k := by
  have hblock : (7 / 8 : ℝ) ^ 8 ≤ 1 / 2 := by norm_num
  have hp : (7 / 8 : ℝ) ^ (8 * (n + k)) ≤ (1 / 2 : ℝ) ^ (n + k) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hblock _
  calc
    _ ≤ (2 : ℝ) ^ n * (7 / 8 : ℝ) ^ (8 * (n + k)) :=
      P.failure_probability_le_seven_eighths hprogress _ n s hrank
    _ ≤ (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ (n + k) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (1 / 2 : ℝ) ^ k := by
      rw [pow_add, ← mul_assoc, ← mul_pow]
      norm_num

end RankedProcess

end LeanPool.SingleCopyStabilizer.AdaptiveProcess
