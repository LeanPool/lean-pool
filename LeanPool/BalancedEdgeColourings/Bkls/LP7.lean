/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.BigOperators.Field

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 7: the linear-programming bound

`o j ≥ 0` (`2 ≤ j ≤ s`) is the number of empty squares at distance `j`; each has `j (j - 1)`
improvements, matched injectively with worsenings at smaller distances: `s (r - s - 1)` at `S₀` and
`(s - i)(r - s - i)` at each empty square at distance `i`. The cumulative constraints
`∑_{j ≤ t} j (j - 1) o j ≤ s (r - s - 1) + ∑_{i < t} (s - i)(r - s - i) o i` give
`∑ o j ≤ (C(r - 1, s - 1) - s) / (s - 1)` (`lp7_bound`).

The proof is the dual certificate: weights `Λ` with `j (j - 1) Λ j = 1 + (s - j)(r - s - j) Λ (j
+ 1)`,
`Λ (s + 1) = 0`, which are non-increasing (`lam_antitone`); the optimum is the extremal solution
`o* j = C(s, j) C(r - s - 1, j - 1) / (s - 1)` and Vandermonde's identity sums it. (Optimality of
this value on instances was certified by `certo opt`, the induction step by `certo farkas`.)
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.LP7

open Finset

/-- `j (j - 1)`: improvements at distance `j`. -/
def D (j : ℕ) : ℚ := (j : ℚ) * ((j : ℚ) - 1)

/-- `(s - i)(r - s - i)`: worsenings at distance `i`. -/
def W (r s i : ℕ) : ℚ := ((s - i : ℕ) : ℚ) * ((r - s - i : ℕ) : ℚ)

/-- The dual weights, indexed by `s + 1 - j`. -/
def lamA (r s : ℕ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => (1 + W r s (s - n) * lamA r s n) / D (s - n)

/-- The dual weight at distance `j`. -/
def lam (r s j : ℕ) : ℚ := lamA r s (s + 1 - j)

/-- Downward induction from `t`. -/
theorem down_ind (P : ℕ → Prop) (t : ℕ) (htop : P t) (hstep : ∀ j, j < t → P (j + 1) → P j) :
    ∀ j, j ≤ t → P j := by
  intro j hj
  obtain ⟨n, rfl⟩ : ∃ n, j = t - n := ⟨t - j, by omega⟩
  induction n with
  | zero => simpa using htop
  | succ n ih =>
    by_cases hn : n < t
    · have := hstep (t - (n + 1)) (by omega) (by
        rw [show t - (n + 1) + 1 = t - n by omega]
        exact ih (by omega))
      exact this
    · rw [show t - (n + 1) = t - n by omega]; exact ih (by omega)

variable {r s : ℕ}

theorem D_nonneg (j : ℕ) : 0 ≤ D j := by
  unfold D
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · have : (1 : ℚ) ≤ j := by exact_mod_cast hj
    positivity

theorem D_pos {j : ℕ} (hj : 2 ≤ j) : 0 < D j := by
  unfold D
  have : (2 : ℚ) ≤ j := by exact_mod_cast hj
  nlinarith

theorem D_succ (j : ℕ) : D (j + 1) = ((j : ℚ) + 1) * j := by
  unfold D; push_cast; ring

theorem D_mono (j : ℕ) : D j ≤ D (j + 1) := by
  rw [D_succ]; unfold D
  have : (0 : ℚ) ≤ j := by positivity
  nlinarith

theorem W_nonneg (i : ℕ) : 0 ≤ W r s i := by unfold W; positivity

theorem W_anti (i : ℕ) : W r s (i + 1) ≤ W r s i := by
  unfold W
  have h1 : ((s - (i + 1) : ℕ) : ℚ) ≤ ((s - i : ℕ) : ℚ) := by exact_mod_cast (by omega)
  have h2 : ((r - s - (i + 1) : ℕ) : ℚ) ≤ ((r - s - i : ℕ) : ℚ) := by exact_mod_cast (by omega)
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem lamA_nonneg (n : ℕ) : 0 ≤ lamA r s n := by
  induction n with
  | zero => simp [lamA]
  | succ n ih =>
    simp only [lamA]
    exact div_nonneg (by have := W_nonneg (r := r) (s := s) (s - n); positivity) (D_nonneg _)

theorem lam_nonneg (j : ℕ) : 0 ≤ lam r s j := lamA_nonneg _

theorem lam_top : lam r s (s + 1) = 0 := by simp [lam, lamA]

theorem lam_rec {j : ℕ} (hj : j ≤ s) :
    lam r s j = (1 + W r s j * lam r s (j + 1)) / D j := by
  unfold lam
  rw [show s + 1 - j = (s - j) + 1 by omega, lamA, show s - (s - j) = j by omega,
    show s + 1 - (j + 1) = s - j by omega]

theorem lam_rec' {j : ℕ} (h2 : 2 ≤ j) (hj : j ≤ s) :
    D j * lam r s j = 1 + W r s j * lam r s (j + 1) := by
  rw [lam_rec hj]; field_simp [(D_pos h2).ne']

/-- `Λ (j + 1) (D j - W j) ≤ 1`. -/
theorem lam_key {j : ℕ} (h2 : 2 ≤ j) (hj : j ≤ s) :
    lam r s (j + 1) * (D j - W r s j) ≤ 1 := by
  refine down_ind (fun j => 2 ≤ j → lam r s (j + 1) * (D j - W r s j) ≤ 1) s
    (fun _ => by rw [lam_top]; simp) (fun j hjs ih h2 => ?_) j hj h2
  · have ih := ih (by omega)
    have hl := lam_nonneg (r := r) (s := s) (j + 1)
    have hl2 := lam_nonneg (r := r) (s := s) (j + 1 + 1)
    by_cases he : D j - W r s j ≤ 0
    · nlinarith
    push Not at he
    have hmono : D j - W r s j ≤ D (j + 1) - W r s (j + 1) := by
      have := D_mono j; have := W_anti (r := r) (s := s) j; linarith
    have ha := D_pos (j := j + 1) (by omega)
    have hrec := lam_rec' (r := r) (s := s) (j := j + 1) (by omega) (by omega)
    have hw := W_nonneg (r := r) (s := s) (j + 1)
    -- `Λ (j + 1) (D (j + 1) - W (j + 1)) ≤ 1`
    have hy : lam r s (j + 1) * (D (j + 1) - W r s (j + 1)) ≤ 1 := by
      have hmul : lam r s (j + 1) * (D (j + 1) - W r s (j + 1)) * D (j + 1) ≤ D (j + 1) := by
        have e : lam r s (j + 1) * (D (j + 1) - W r s (j + 1)) * D (j + 1) =
            (1 + W r s (j + 1) * lam r s (j + 1 + 1)) * (D (j + 1) - W r s (j + 1)) := by
          rw [← hrec]; ring
        rw [e]
        nlinarith [mul_le_mul_of_nonneg_left ih hw]
      exact le_of_mul_le_mul_right (by linarith) ha
    nlinarith

theorem lam_antitone {j : ℕ} (h2 : 2 ≤ j) (hj : j ≤ s) : lam r s (j + 1) ≤ lam r s j := by
  have hrec := lam_rec' (r := r) (s := s) h2 hj
  have hk := lam_key (r := r) (s := s) h2 hj
  have hD := D_pos h2
  have : D j * (lam r s j - lam r s (j + 1)) ≥ 0 := by nlinarith
  by_contra h
  push Not at h
  nlinarith

/-- The remaining capacity before level `t`. -/
def R (r s : ℕ) (o : ℕ → ℚ) (t : ℕ) : ℚ :=
  (s : ℚ) * ((r - s - 1 : ℕ) : ℚ) + ∑ i ∈ Ico 2 t, (W r s i - D i) * o i

/-- **The dual bound.** -/
theorem sum_le_lam (hs : 1 ≤ s) (o : ℕ → ℚ) (_ : ∀ j, 0 ≤ o j)
    (hC : ∀ t, 2 ≤ t → t ≤ s → ∑ j ∈ Ico 2 (t + 1), D j * o j ≤
      (s : ℚ) * ((r - s - 1 : ℕ) : ℚ) + ∑ i ∈ Ico 2 t, W r s i * o i) :
    ∑ j ∈ Ico 2 (s + 1), o j ≤ lam r s 2 * R r s o 2 := by
  have key : ∀ t, 2 ≤ t → t ≤ s + 1 →
      ∑ j ∈ Ico t (s + 1), o j ≤ lam r s t * R r s o t := by
    intro t h2 ht
    refine down_ind (fun t => 2 ≤ t → ∑ j ∈ Ico t (s + 1), o j ≤ lam r s t * R r s o t) (s + 1)
      (fun _ => by simp [lam_top]) (fun t hts ih h2 => ?_) t ht h2
    · have ih := ih (by omega)
      have hts' : t ≤ s := by omega
      rw [sum_eq_sum_Ico_succ_bot (by omega)]
      have hR : R r s o (t + 1) = R r s o t + (W r s t - D t) * o t := by
        unfold R; rw [sum_Ico_succ_top (by omega)]; ring
      have hCt : D t * o t ≤ R r s o t := by
        have := hC t h2 hts'
        rw [sum_Ico_succ_top (by omega)] at this
        have e : ∑ i ∈ Ico 2 t, (W r s i - D i) * o i =
            ∑ i ∈ Ico 2 t, W r s i * o i - ∑ i ∈ Ico 2 t, D i * o i := by
          rw [← sum_sub_distrib]; exact sum_congr rfl (fun i _ => by ring)
        unfold R; rw [e]; linarith
      rw [hR] at ih
      have hdec := lam_antitone (r := r) (s := s) h2 hts'
      have hrec := lam_rec' (r := r) (s := s) h2 hts'
      have h1 := mul_le_mul_of_nonneg_left hCt (sub_nonneg.2 hdec)
      have h2' : o t * (D t * lam r s t) = o t * (1 + W r s t * lam r s (t + 1)) := by rw [hrec]
      nlinarith
  exact key 2 le_rfl (by omega)

/-- The extremal solution. -/
def ostar (r s m : ℕ) : ℚ := ((s.choose m : ℕ) : ℚ) * (((r - s - 1).choose (m - 1) : ℕ) : ℚ) /
    (s - 1)

theorem ostar_rec {m : ℕ} (hm : 1 ≤ m) :
    W r s m * ostar r s m = D (m + 1) * ostar r s (m + 1) := by
  have e1 : s.choose (m + 1) * (m + 1) = s.choose m * (s - m) := Nat.choose_succ_right_eq s m
  have e2 : (r - s - 1).choose (m - 1 + 1) * (m - 1 + 1) =
      (r - s - 1).choose (m - 1) * (r - s - 1 - (m - 1)) := Nat.choose_succ_right_eq _ _
  rw [show m - 1 + 1 = m by omega, show r - s - 1 - (m - 1) = r - s - m by omega] at e2
  have key : ((s - m : ℕ) : ℚ) * ((r - s - m : ℕ) : ℚ) * (s.choose m : ℚ) *
      ((r - s - 1).choose (m - 1) : ℚ) =
      ((m : ℚ) + 1) * m * (s.choose (m + 1) : ℚ) * ((r - s - 1).choose m : ℚ) := by
    have := congrArg (fun x : ℕ => (x : ℚ)) (congrArg₂ (· * ·) e1 e2)
    push_cast at this
    linear_combination (-1 : ℚ) * this
  unfold W ostar
  rw [D_succ, show m + 1 - 1 = m by omega]
  rw [mul_div_assoc', mul_div_assoc']
  congr 1
  linear_combination key

theorem D_ostar_lam {m : ℕ} (h2 : 2 ≤ m) (hm : m ≤ s + 1) :
    D m * ostar r s m * lam r s m = ∑ l ∈ Ico m (s + 1), ostar r s l := by
  refine down_ind (fun m => 2 ≤ m → D m * ostar r s m * lam r s m = ∑ l ∈ Ico m (s + 1), ostar
      r s l)
    (s + 1) (fun _ => by simp [lam_top]) (fun m hms ih h2 => ?_) m hm h2
  · have ih := ih (by omega)
    rw [sum_eq_sum_Ico_succ_bot (by omega), ← ih, ← ostar_rec (by omega)]
    have hrec := lam_rec' (r := r) (s := s) h2 (by omega)
    calc D m * ostar r s m * lam r s m = ostar r s m * (D m * lam r s m) := by ring
      _ = _ := by rw [hrec]; ring

theorem vandermonde_shift {s : ℕ} (hs : 1 ≤ s) (n : ℕ) :
    ∑ m ∈ Ico 1 (s + 1), s.choose m * n.choose (m - 1) = (s + n).choose (s - 1) := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => s.choose i * n.choose j)]
  rw [show (s - 1).succ = s by omega, ← sum_range_reflect, sum_Ico_eq_sum_range,
    show s + 1 - 1 = s by omega]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [show s - 1 - (s - 1 - j) = j by omega, show 1 + j - 1 = j by omega, add_comm 1 j,
    ← Nat.choose_symm (show s - 1 - j ≤ s by omega), show s - (s - 1 - j) = j + 1 by omega]

/-- **The linear-programming bound of Lemma 7.** -/
theorem lp7_bound (hs : 2 ≤ s) (hrs : s + 1 ≤ r) (o : ℕ → ℚ) (ho : ∀ j, 0 ≤ o j)
    (hC : ∀ t, 2 ≤ t → t ≤ s → ∑ j ∈ Ico 2 (t + 1), D j * o j ≤
      (s : ℚ) * ((r - s - 1 : ℕ) : ℚ) + ∑ i ∈ Ico 2 t, W r s i * o i) :
    ∑ j ∈ Ico 2 (s + 1), o j ≤ (((r - 1).choose (s - 1) : ℕ) - (s : ℚ)) / (s - 1) := by
  have h := sum_le_lam (by omega) o ho hC
  have hR2 : R r s o 2 = (s : ℚ) * ((r - s - 1 : ℕ) : ℚ) := by simp [R]
  have hs1 : (s : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ s := by exact_mod_cast hs
    linarith
  -- `D 2 · o* 2 = s (r - s - 1)`
  have hbase : D 2 * ostar r s 2 = (s : ℚ) * ((r - s - 1 : ℕ) : ℚ) := by
    unfold D ostar
    rw [Nat.cast_choose_two, show 2 - 1 = 1 by rfl, Nat.choose_one_right]
    field_simp
    ring
  have hsum := D_ostar_lam (r := r) (s := s) (le_refl 2) (by omega)
  rw [hbase] at hsum
  rw [hR2, mul_comm, hsum] at h
  -- the sum of `o*`
  have hv := vandermonde_shift (s := s) (by omega) (r - s - 1)
  rw [show s + (r - s - 1) = r - 1 by omega, sum_eq_sum_Ico_succ_bot (by omega)] at hv
  simp only [Nat.choose_one_right, show 1 - 1 = 0 from rfl, Nat.choose_zero_right, mul_one] at hv
  have hq : ∑ l ∈ Ico 2 (s + 1), ostar r s l =
      ((((r - 1).choose (s - 1) : ℕ) : ℚ) - s) / (s - 1) := by
    unfold ostar
    rw [← sum_div]
    congr 1
    rw [← hv]
    push_cast
    ring
  linarith

end Bkls.LP7

end LeanPool.BalancedEdgeColourings
