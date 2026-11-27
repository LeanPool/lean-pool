/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.EffectiveNormalization
public import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A rational reserve for small finite-event martingales

Only finite sums are needed. At target length `n` the gambler uses the first
`2*n+6` accounts. Comparison with any larger finite sum bounds the cumulative
wager error by `1/32` and leaves a positive reserve.
-/

@[expose] public section

namespace Klr.Splitting

open scoped BigOperators

/-- A sequence of nonnegative rational martingales with rapidly decreasing costs. -/
structure SmallMartingales where
  /-- Rational capital of each component martingale at a finite transcript. -/
  value : ℕ → List Bool → ℚ
  nonneg : ∀ m v, 0 ≤ value m v
  fair : ∀ m v, value m (v ++ [false]) + value m (v ++ [true]) = 2 * value m v
  initial_le : ∀ m, value m [] ≤ (1 / 2 : ℚ) ^ (2 * m + 2)

namespace SmallMartingales

variable (d : SmallMartingales)

theorem successor_le (m : ℕ) (v : List Bool) (b : Bool) :
    d.value m (v ++ [b]) ≤ 2 * d.value m v := by
  have hf := d.fair m v
  have h₀ := d.nonneg m (v ++ [false])
  have h₁ := d.nonneg m (v ++ [true])
  cases b <;> linarith

theorem value_le (m : ℕ) (v : List Bool) :
    d.value m v ≤ (2 : ℚ) ^ v.length * d.value m [] := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v b ih =>
    calc
      d.value m (v ++ [b]) ≤ 2 * d.value m v := d.successor_le m v b
      _ ≤ 2 * ((2 : ℚ) ^ v.length * d.value m []) := by gcongr
      _ = _ := by simp [pow_succ]; ring

theorem weighted_le (m : ℕ) (v : List Bool) :
    (2 : ℚ) ^ m * d.value m v ≤ (2 : ℚ) ^ v.length * (1 / 2 : ℚ) ^ (m + 2) := by
  have hpow : (2 : ℚ) ^ m * (1 / 2 : ℚ) ^ (2 * m + 2) =
      (1 / 2 : ℚ) ^ (m + 2) := by
    rw [show 2 * m + 2 = m + (m + 2) by omega, pow_add, ← mul_assoc, ← mul_pow]
    norm_num
  calc
    _ ≤ (2 : ℚ) ^ m * ((2 : ℚ) ^ v.length * d.value m []) := by
      gcongr
      exact d.value_le m v
    _ ≤ (2 : ℚ) ^ m * ((2 : ℚ) ^ v.length * (1 / 2 : ℚ) ^ (2 * m + 2)) := by
      gcongr
      exact d.initial_le m
    _ = _ := by rw [mul_left_comm, hpow]

/-- Weighted capital of the components below the given cutoff. -/
def sumCapital (K : ℕ) (v : List Bool) : ℚ :=
  ∑ m ∈ Finset.range K, (2 : ℚ) ^ m * d.value m v

@[simp] theorem sumCapital_zero (v : List Bool) : d.sumCapital 0 v = 0 := by
  simp [sumCapital]

theorem sumCapital_nonneg (K : ℕ) (v : List Bool) : 0 ≤ d.sumCapital K v :=
  Finset.sum_nonneg fun m _ => mul_nonneg (by positivity) (d.nonneg m v)

theorem sumCapital_fair (K : ℕ) (v : List Bool) :
    d.sumCapital K (v ++ [false]) + d.sumCapital K (v ++ [true]) =
      2 * d.sumCapital K v := by
  simp only [sumCapital, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← mul_add, d.fair m v]
  ring

theorem tail_nonneg (M K : ℕ) (hMK : M ≤ K) (v : List Bool) :
    0 ≤ d.sumCapital K v - d.sumCapital M v := by
  unfold sumCapital
  rw [← Finset.sum_Ico_eq_sub _ hMK]
  exact Finset.sum_nonneg fun m _ => mul_nonneg (by positivity) (d.nonneg m v)

theorem tail_le (M K : ℕ) (hMK : M ≤ K) (v : List Bool) :
    d.sumCapital K v - d.sumCapital M v ≤
      (2 : ℚ) ^ v.length * (1 / 2 : ℚ) ^ (M + 1) := by
  have hg := geom_sum_Ico_le_of_lt_one (K := ℚ) (m := M) (n := K)
    (by norm_num : 0 ≤ (1 / 2 : ℚ)) (by norm_num : (1 / 2 : ℚ) < 1)
  norm_num at hg
  unfold sumCapital
  rw [← Finset.sum_Ico_eq_sub _ hMK]
  calc
    _ ≤ ∑ m ∈ Finset.Ico M K, (2 : ℚ) ^ v.length * (1 / 2 : ℚ) ^ (m + 2) :=
      Finset.sum_le_sum fun m _ => d.weighted_le m v
    _ = (2 : ℚ) ^ v.length * ((∑ m ∈ Finset.Ico M K, (1 / 2 : ℚ) ^ m) / 4) := by
      simp only [pow_add, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ ≤ (2 : ℚ) ^ v.length * ((1 / 2 : ℚ) ^ M / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by rw [pow_succ]; ring

theorem sumCapital_initial_le (K : ℕ) : d.sumCapital K [] ≤ 1 / 2 := by
  simpa using d.tail_le 0 K (Nat.zero_le _) []

theorem term_le_sumCapital (K m : ℕ) (hm : m < K) (v : List Bool) :
    (2 : ℚ) ^ m * d.value m v ≤ d.sumCapital K v :=
  Finset.single_le_sum (fun j _ => mul_nonneg (by positivity) (d.nonneg j v))
    (Finset.mem_range.mpr hm)

/-- The finite precision increases faster than the target prefix length. -/
def cutoff (n : ℕ) : ℕ := 2 * n + 6

theorem cutoff_mono {m n : ℕ} (h : m ≤ n) : cutoff m ≤ cutoff n := by
  unfold cutoff
  omega

/-- Next signed stake of the sum with cutoff determined by the transcript length. -/
def stake (v : List Bool) : ℚ :=
  (d.sumCapital (cutoff v.length) (v ++ [true]) -
    d.sumCapital (cutoff v.length) (v ++ [false])) / 2

/-- Next signed stake of the sum with a fixed component cutoff. -/
def referenceStake (K : ℕ) (v : List Bool) : ℚ :=
  (d.sumCapital K (v ++ [true]) - d.sumCapital K (v ++ [false])) / 2

theorem reference_snoc (K : ℕ) (v : List Bool) (b : Bool) :
    d.sumCapital K (v ++ [b]) = d.sumCapital K v + answerSign b * d.referenceStake K v := by
  have hf := d.sumCapital_fair K v
  cases b <;> simp only [answerSign_false, answerSign_true, referenceStake] <;> linarith

theorem stake_error (K : ℕ) (v : List Bool) (hK : cutoff v.length ≤ K) :
    |d.stake v - d.referenceStake K v| ≤ (1 / 2 : ℚ) ^ (v.length + 6) := by
  have hbound (b : Bool) :
      d.sumCapital K (v ++ [b]) - d.sumCapital (cutoff v.length) (v ++ [b]) ≤
        (1 / 2 : ℚ) ^ (v.length + 6) := by
    have h := d.tail_le (cutoff v.length) K hK (v ++ [b])
    have he : (2 : ℚ) ^ (v.length + 1) * (1 / 2 : ℚ) ^ (cutoff v.length + 1) =
        (1 / 2 : ℚ) ^ (v.length + 6) := by
      rw [show cutoff v.length + 1 = (v.length + 1) + (v.length + 6) by
        unfold cutoff; omega, pow_add (1 / 2 : ℚ), ← mul_assoc, ← mul_pow]
      norm_num
    simpa only [List.length_append, List.length_singleton, he] using h
  have h₀ := d.tail_nonneg (cutoff v.length) K hK (v ++ [false])
  have h₁ := d.tail_nonneg (cutoff v.length) K hK (v ++ [true])
  have hb₀ := hbound false
  have hb₁ := hbound true
  have hp : 0 ≤ (1 / 2 : ℚ) ^ (v.length + 6) := by positivity
  rw [abs_le]
  unfold stake referenceStake
  constructor <;> linarith

/-- Advance the transcript and add the signed return to the reserve account. -/
def reserveStep (s : List Bool × ℚ) (b : Bool) : List Bool × ℚ :=
  (s.1 ++ [b], s.2 + answerSign b * d.stake s.1)

/-- The transcript and capital of the combined account at the given time. -/
def reserveAccount (v : List Bool) : List Bool × ℚ :=
  v.foldl d.reserveStep ([], 1)

/-- Capital of the combined account after a finite transcript. -/
def reserveValue (v : List Bool) : ℚ := (d.reserveAccount v).2

@[simp] theorem reserveAccount_snoc (v : List Bool) (b : Bool) :
    d.reserveAccount (v ++ [b]) = d.reserveStep (d.reserveAccount v) b := by
  simp [reserveAccount, List.foldl_append]

theorem reserveAccount_prefix (v : List Bool) : (d.reserveAccount v).1 = v := by
  induction v using List.reverseRecOn with
  | nil => rfl
  | append_singleton v b ih => simp [reserveStep, ih]

@[simp] theorem reserveValue_nil : d.reserveValue [] = 1 := rfl

theorem reserveValue_snoc (v : List Bool) (b : Bool) :
    d.reserveValue (v ++ [b]) = d.reserveValue v + answerSign b * d.stake v := by
  simp [reserveValue, reserveStep, reserveAccount_prefix]

theorem reserve_error_geometric (v : List Bool) (K : ℕ) (hK : cutoff v.length ≤ K) :
    |d.reserveValue v - (d.sumCapital K v + 1 - d.sumCapital K [])| ≤
      (1 / 32 : ℚ) * (1 - (1 / 2 : ℚ) ^ v.length) := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v b ih =>
    have hK' : cutoff v.length ≤ K :=
      (cutoff_mono (by simp)).trans hK
    have heq :
        d.reserveValue (v ++ [b]) - (d.sumCapital K (v ++ [b]) + 1 - d.sumCapital K []) =
          (d.reserveValue v - (d.sumCapital K v + 1 - d.sumCapital K [])) +
            answerSign b * (d.stake v - d.referenceStake K v) := by
      rw [reserveValue_snoc, reference_snoc]
      ring
    rw [heq]
    calc
      _ ≤ |d.reserveValue v - (d.sumCapital K v + 1 - d.sumCapital K [])| +
          |answerSign b * (d.stake v - d.referenceStake K v)| := abs_add_le _ _
      _ = |d.reserveValue v - (d.sumCapital K v + 1 - d.sumCapital K [])| +
          |d.stake v - d.referenceStake K v| := by simp [abs_mul]
      _ ≤ (1 / 32 : ℚ) * (1 - (1 / 2 : ℚ) ^ v.length) +
          (1 / 2 : ℚ) ^ (v.length + 6) := add_le_add (ih hK') (d.stake_error K v hK')
      _ = _ := by simp only [List.length_append, List.length_singleton, pow_add]; ring

theorem reserve_lower_sum (v : List Bool) (K : ℕ) (hK : cutoff v.length ≤ K) :
    d.sumCapital K v + 15 / 32 ≤ d.reserveValue v := by
  have h := (abs_le.mp (d.reserve_error_geometric v K hK)).1
  have hi := d.sumCapital_initial_le K
  have hp : 0 ≤ (1 / 2 : ℚ) ^ v.length := by positivity
  linarith

theorem reserve_positive (v : List Bool) : 0 < d.reserveValue v := by
  have h := d.reserve_lower_sum v (cutoff v.length) le_rfl
  have hn := d.sumCapital_nonneg (cutoff v.length) v
  linarith

theorem stake_legal (v : List Bool) : |d.stake v| ≤ d.reserveValue v := by
  have h₀ := d.reserve_positive (v ++ [false])
  have h₁ := d.reserve_positive (v ++ [true])
  rw [reserveValue_snoc] at h₀ h₁
  simp only [answerSign_false, answerSign_true] at h₀ h₁
  rw [abs_le]
  constructor <;> linarith

theorem term_le_reserveValue (v : List Bool) (m : ℕ) (hm : m < cutoff v.length) :
    (2 : ℚ) ^ m * d.value m v ≤ d.reserveValue v := by
  have h := d.reserve_lower_sum v (cutoff v.length) le_rfl
  have ht := d.term_le_sumCapital (cutoff v.length) m hm v
  linarith

end SmallMartingales

end Klr.Splitting
