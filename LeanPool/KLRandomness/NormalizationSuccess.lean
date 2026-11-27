/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.Normalization
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic preservation of success

The second half of Lemma 2 in Liu and Meng, arXiv:2611.31004v1, uses Abel
summation to show that damping wagers preserves unbounded capital, provided
the original capital has first been kept above a positive reserve.

The main theorem `normalization_preserves_unbounded_capital` proves this
pathwise statement for real signed returns. Original and normalized capital
are the products of `1 + x t` and `1 + normalizedWager x t`, respectively.
The preceding file proves the uniform square-sum bound. Together they verify
the analytic damping step of Lemma 2; constructing the positive rational
reserve strategy and proving computability are separate tasks.

The estimates below use the sufficient bound
`log (1 + x) ≤ x - x^2 / 6` for `-1 < x ≤ 1`; the paper uses the sharper
constant `1 / 4`. The weaker constant admits an elementary proof from
`log y ≤ y - 1` and does not change the normalization.
-/

@[expose] public section

namespace Klr

open scoped BigOperators

/-- The cumulative signed return before time `n`. -/
def prefixReturn (x : ℕ → ℝ) (n : ℕ) : ℝ := ∑ t ∈ Finset.range n, x t

/-- A cumulative return with a weight chosen before each step. -/
def weightedReturn (a x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, a t * x t

@[simp] theorem prefixReturn_zero (x : ℕ → ℝ) : prefixReturn x 0 = 0 := by
  simp [prefixReturn]

@[simp] theorem prefixReturn_succ (x : ℕ → ℝ) (n : ℕ) :
    prefixReturn x (n + 1) = prefixReturn x n + x n := by
  simp [prefixReturn, Finset.sum_range_succ]

@[simp] theorem weightedReturn_zero (a x : ℕ → ℝ) : weightedReturn a x 0 = 0 := by
  simp [weightedReturn]

@[simp] theorem weightedReturn_succ (a x : ℕ → ℝ) (n : ℕ) :
    weightedReturn a x (n + 1) = weightedReturn a x n + a n * x n := by
  simp [weightedReturn, Finset.sum_range_succ]

/-- Abel summation with a terminal coefficient at `n`, avoiding subtraction on naturals. -/
theorem weightedReturn_abel (a x : ℕ → ℝ) (n : ℕ) :
    weightedReturn a x n = a n * prefixReturn x n +
      ∑ t ∈ Finset.range n, (a t - a (t + 1)) * prefixReturn x (t + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [weightedReturn_succ, Finset.sum_range_succ, ih, prefixReturn_succ]
      ring

theorem abel_coefficient_sum (a : ℕ → ℝ) (n : ℕ) :
    a n + (∑ t ∈ Finset.range n, (a t - a (t + 1))) = a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith

/-- Decreasing weights preserve a lower bound for cumulative returns, including
the contribution of the terminal cumulative return. -/
theorem weightedReturn_lower_bound (a x : ℕ → ℝ) (c : ℝ)
    (ha : ∀ t, a (t + 1) ≤ a t) (hx : ∀ t, c ≤ prefixReturn x t) (n : ℕ) :
    a n * (prefixReturn x n - c) + c * a 0 ≤ weightedReturn a x n := by
  have hsum : (∑ t ∈ Finset.range n, (a t - a (t + 1))) * c ≤
      ∑ t ∈ Finset.range n, (a t - a (t + 1)) * prefixReturn x (t + 1) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun t _ ↦
      mul_le_mul_of_nonneg_left (hx (t + 1)) (sub_nonneg.mpr (ha t))
  have hcoef := congrArg (fun z : ℝ ↦ z * c) (abel_coefficient_sum a n)
  rw [weightedReturn_abel]
  nlinarith

theorem weightedReturn_ge_initial (a x : ℕ → ℝ) (c : ℝ)
    (ha : ∀ t, a (t + 1) ≤ a t) (ha0 : ∀ t, 0 ≤ a t)
    (hx : ∀ t, c ≤ prefixReturn x t) (n : ℕ) :
    c * a 0 ≤ weightedReturn a x n := by
  have h := weightedReturn_lower_bound a x c ha hx n
  have hnonneg := mul_nonneg (ha0 n) (sub_nonneg.mpr (hx n))
  linarith

/-- An elementary quadratic upper estimate sufficient for preservation of success. -/
theorem log_one_add_le_sub_sq_sixth (x : ℝ) (hx0 : -1 < x) (hx1 : x ≤ 1) :
    Real.log (1 + x) ≤ x - x ^ 2 / 6 := by
  have h1 : 0 < 1 + x := by linarith
  have h2 : 0 < 1 + x / 2 := by linarith
  have h3 : 0 < 2 + x := by linarith
  have hlog1 := Real.log_le_sub_one_of_pos h2
  have hlog2 := Real.log_le_sub_one_of_pos (div_pos h1 h2)
  rw [Real.log_div (ne_of_gt h1) (ne_of_gt h2)] at hlog2
  have hrat : (1 + x / 2) - 1 + ((1 + x) / (1 + x / 2) - 1) =
      x - x ^ 2 / (2 * (2 + x)) := by
    field_simp
    ring
  have hden : 0 < 2 * (2 + x) := by positivity
  have hsq : x ^ 2 / 6 ≤ x ^ 2 / (2 * (2 + x)) := by
    apply div_le_div_of_nonneg_left (sq_nonneg x) hden
    linarith
  linarith

/-- On the interval used by the damped strategy, logarithms lose at most twice
the squared wager. -/
theorem sub_two_sq_le_log_one_add (x : ℝ) (hx : |x| ≤ (1 / 2 : ℝ)) :
    x - 2 * x ^ 2 ≤ Real.log (1 + x) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx
  have hpos : 0 < 1 + x := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hrat : 1 - (1 + x)⁻¹ = x - x ^ 2 / (1 + x) := by
    field_simp
    ring
  have hsq : x ^ 2 / (1 + x) ≤ 2 * x ^ 2 := by
    apply (div_le_iff₀ hpos).2
    nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ 1 + 2 * x)]
  linarith

/-- The positive, decreasing weight chosen from the original quadratic variation. -/
noncomputable def damping (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 / (2 * (1 + quadraticVariation x n))

@[simp] theorem damping_zero (x : ℕ → ℝ) : damping x 0 = (1 / 2 : ℝ) := by
  simp [damping]

theorem damping_pos (x : ℕ → ℝ) (n : ℕ) : 0 < damping x n := by
  have := quadraticVariation_nonneg x n
  unfold damping
  positivity

theorem damping_succ_le (x : ℕ → ℝ) (n : ℕ) : damping x (n + 1) ≤ damping x n := by
  have hq := quadraticVariation_nonneg x n
  unfold damping
  apply one_div_le_one_div_of_le (by positivity)
  rw [quadraticVariation_succ]
  nlinarith [sq_nonneg (x n)]

theorem normalizedWager_eq_damping_mul (x : ℕ → ℝ) (n : ℕ) :
    normalizedWager x n = damping x n * x n := by
  simp [normalizedWager, damping, div_eq_mul_inv, mul_comm]

theorem weightedReturn_damping (x : ℕ → ℝ) (n : ℕ) :
    weightedReturn (damping x) x n = prefixReturn (normalizedWager x) n := by
  simp [weightedReturn, prefixReturn, normalizedWager_eq_damping_mul]

theorem weightedReturn_sub_mul (a x y : ℕ → ℝ) (k : ℝ) (n : ℕ) :
    weightedReturn a (fun t ↦ x t - k * y t) n =
      weightedReturn a x n - k * weightedReturn a y n := by
  simp only [weightedReturn, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem prefixReturn_sub_sq (x : ℕ → ℝ) (k : ℝ) (n : ℕ) :
    prefixReturn (fun t ↦ x t - k * (x t) ^ 2) n =
      prefixReturn x n - k * quadraticVariation x n := by
  simp [prefixReturn, quadraticVariation, Finset.sum_sub_distrib, Finset.mul_sum]

/-- Abel summation transfers a quadratic lower envelope of the cumulative return
to a lower bound for the weighted cumulative return. -/
theorem weightedReturn_damping_lower_envelope (x : ℕ → ℝ) (c k : ℝ)
    (hx : ∀ n, c + k * quadraticVariation x n ≤ prefixReturn x n) (n : ℕ) :
    c / 2 + k * weightedReturn (damping x) (fun t ↦ (x t) ^ 2) n ≤
      weightedReturn (damping x) x n := by
  have hadj : ∀ t, c ≤ prefixReturn (fun s ↦ x s - k * (x s) ^ 2) t := by
    intro t
    rw [prefixReturn_sub_sq]
    linarith [hx t]
  have h := weightedReturn_ge_initial (damping x) (fun t ↦ x t - k * (x t) ^ 2)
    c (damping_succ_le x) (fun t ↦ (damping_pos x t).le) hadj n
  rw [weightedReturn_sub_mul, damping_zero] at h
  linarith

theorem log_quadraticVariation_step_le (x : ℕ → ℝ) (n : ℕ) :
    Real.log (1 + quadraticVariation x (n + 1)) -
      Real.log (1 + quadraticVariation x n) ≤ (x n) ^ 2 / (1 + quadraticVariation x n) := by
  have hq := quadraticVariation_nonneg x n
  have hq' := quadraticVariation_nonneg x (n + 1)
  have ha : 0 < 1 + quadraticVariation x n := by positivity
  have hb : 0 < 1 + quadraticVariation x (n + 1) := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)] at h
  have heq : (1 + quadraticVariation x (n + 1)) / (1 + quadraticVariation x n) - 1 =
      (x n) ^ 2 / (1 + quadraticVariation x n) := by
    rw [quadraticVariation_succ]
    field_simp
    ring
  rwa [heq] at h

/-- A finite logarithmic bound, without invoking convergence of any series. -/
theorem log_quadraticVariation_le_weighted_squares (x : ℕ → ℝ) (n : ℕ) :
    Real.log (1 + quadraticVariation x n) ≤
      2 * weightedReturn (damping x) (fun t ↦ (x t) ^ 2) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [weightedReturn_succ]
      have hstep := log_quadraticVariation_step_le x n
      have hterm : (x n) ^ 2 / (1 + quadraticVariation x n) =
          2 * (damping x n * (x n) ^ 2) := by
        simp [damping]
        ring
      rw [hterm] at hstep
      linarith

theorem weightedReturn_damping_log_lower_bound (x : ℕ → ℝ) (c k : ℝ) (hk : 0 ≤ k)
    (hx : ∀ n, c + k * quadraticVariation x n ≤ prefixReturn x n) (n : ℕ) :
    c / 2 + (k / 2) * Real.log (1 + quadraticVariation x n) ≤
      weightedReturn (damping x) x n := by
  have he := weightedReturn_damping_lower_envelope x c k hx n
  have hl := mul_le_mul_of_nonneg_left
    (log_quadraticVariation_le_weighted_squares x n) hk
  linarith

/-- With bounded quadratic variation, the damping weights stay uniformly positive. -/
theorem weightedReturn_damping_lower_bound_of_variation_le (x : ℕ → ℝ) (c b : ℝ)
    (hxb : ∀ n, quadraticVariation x n ≤ b)
    (hx : ∀ n, c ≤ prefixReturn x n) (n : ℕ) :
    (1 / (2 * (1 + b))) * (prefixReturn x n - c) + c / 2 ≤
      weightedReturn (damping x) x n := by
  have hweight : 1 / (2 * (1 + b)) ≤ damping x n := by
    unfold damping
    apply one_div_le_one_div_of_le
    · have := quadraticVariation_nonneg x n
      positivity
    · linarith [hxb n]
  have h := weightedReturn_lower_bound (damping x) x c (damping_succ_le x) hx n
  rw [damping_zero] at h
  have hm := mul_le_mul_of_nonneg_right hweight (sub_nonneg.mpr (hx n))
  linarith

/-- Under a positive quadratic lower envelope, bounding the damped cumulative
return bounds the original cumulative return. This packages both cases of the
paper's Abel-summation argument into a single implication. -/
theorem bddAbove_prefixReturn_of_bddAbove_dampedReturn (x : ℕ → ℝ) (c k : ℝ)
    (hk : 0 < k) (hx : ∀ n, c + k * quadraticVariation x n ≤ prefixReturn x n)
    (hbound : BddAbove (Set.range (weightedReturn (damping x) x))) :
    BddAbove (Set.range (prefixReturn x)) := by
  rcases hbound with ⟨a, ha⟩
  have hA : ∀ n, weightedReturn (damping x) x n ≤ a := fun n ↦ ha (Set.mem_range_self n)
  let b := Real.exp ((2 * a - c) / k)
  have hb : 0 < b := Real.exp_pos _
  have hQ : ∀ n, quadraticVariation x n ≤ b := by
    intro n
    have hl := weightedReturn_damping_log_lower_bound x c k hk.le hx n
    have hlog : Real.log (1 + quadraticVariation x n) ≤ (2 * a - c) / k := by
      apply (le_div_iff₀ hk).2
      linarith [hA n]
    have hq := quadraticVariation_nonneg x n
    have hexp := (Real.log_le_iff_le_exp (by positivity : 0 < 1 + quadraticVariation x n)).1 hlog
    change 1 + quadraticVariation x n ≤ b at hexp
    linarith
  have hM : ∀ n, c ≤ prefixReturn x n := by
    intro n
    have := mul_nonneg hk.le (quadraticVariation_nonneg x n)
    linarith [hx n]
  let d : ℝ := 1 / (2 * (1 + b))
  have hd : 0 < d := by unfold d; positivity
  refine ⟨c + (a - c / 2) / d, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hl := weightedReturn_damping_lower_bound_of_variation_le x c b hQ hM n
  change d * (prefixReturn x n - c) + c / 2 ≤ weightedReturn (damping x) x n at hl
  have hh : prefixReturn x n - c ≤ (a - c / 2) / d := by
    apply (le_div_iff₀ hd).2
    nlinarith [hA n]
  linarith

/-- Capital starting at one and updated by the signed multiplicative returns `x t`. -/
def multiplicativeCapital (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ t ∈ Finset.range n, (1 + x t)

@[simp] theorem multiplicativeCapital_zero (x : ℕ → ℝ) : multiplicativeCapital x 0 = 1 := by
  simp [multiplicativeCapital]

@[simp] theorem multiplicativeCapital_succ (x : ℕ → ℝ) (n : ℕ) :
    multiplicativeCapital x (n + 1) = multiplicativeCapital x n * (1 + x n) := by
  simp [multiplicativeCapital, Finset.prod_range_succ]

theorem multiplicativeCapital_pos (x : ℕ → ℝ) (hx : ∀ t, -1 < x t) (n : ℕ) :
    0 < multiplicativeCapital x n := by
  apply Finset.prod_pos
  intro t _
  linarith [hx t]

theorem log_multiplicativeCapital_le (x : ℕ → ℝ)
    (hx0 : ∀ t, -1 < x t) (hx1 : ∀ t, x t ≤ 1) (n : ℕ) :
    Real.log (multiplicativeCapital x n) ≤ prefixReturn x n - quadraticVariation x n / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [multiplicativeCapital_succ, Real.log_mul (ne_of_gt (multiplicativeCapital_pos x hx0 n))
        (by linarith [hx0 n]), prefixReturn_succ, quadraticVariation_succ]
      have hs := log_one_add_le_sub_sq_sixth (x n) (hx0 n) (hx1 n)
      linarith

theorem normalizedWager_abs_le_half (x : ℕ → ℝ) (hx : ∀ t, |x t| ≤ 1) (n : ℕ) :
    |normalizedWager x n| ≤ (1 / 2 : ℝ) := by
  have hq := quadraticVariation_nonneg x n
  have hden : 0 < 2 * (1 + quadraticVariation x n) := by positivity
  rw [normalizedWager, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  linarith [hx n]

theorem normalizedWager_gt_neg_one (x : ℕ → ℝ) (hx : ∀ t, |x t| ≤ 1) (n : ℕ) :
    -1 < normalizedWager x n := by
  have := (abs_le.mp (normalizedWager_abs_le_half x hx n)).1
  linarith

theorem sub_two_quadraticVariation_le_log_capital (x : ℕ → ℝ)
    (hx : ∀ t, |x t| ≤ (1 / 2 : ℝ)) (n : ℕ) :
    prefixReturn x n - 2 * quadraticVariation x n ≤ Real.log (multiplicativeCapital x n) := by
  have hpos : ∀ t, -1 < x t := by
    intro t
    have := (abs_le.mp (hx t)).1
    linarith
  induction n with
  | zero => simp
  | succ n ih =>
      rw [multiplicativeCapital_succ, Real.log_mul (ne_of_gt (multiplicativeCapital_pos x hpos n))
        (by linarith [hpos n]), prefixReturn_succ, quadraticVariation_succ]
      have hs := sub_two_sq_le_log_one_add (x n) (hx n)
      linarith

/-- The logarithm of normalized capital is within one of the damped cumulative
return. This is the lower capital estimate used in Lemma 2. -/
theorem dampedReturn_sub_one_le_log_normalizedCapital (x : ℕ → ℝ)
    (hx : ∀ t, |x t| ≤ 1) (n : ℕ) :
    weightedReturn (damping x) x n - 1 ≤
      Real.log (multiplicativeCapital (normalizedWager x) n) := by
  have hl := sub_two_quadraticVariation_le_log_capital (normalizedWager x)
    (normalizedWager_abs_le_half x hx) n
  have hq := sum_normalizedWager_sq_le_half x
    (fun t ↦ (sq_le_one_iff_abs_le_one _).2 (hx t)) n
  change quadraticVariation (normalizedWager x) n ≤ (1 / 2 : ℝ) at hq
  rw [weightedReturn_damping]
  linarith

theorem bddAbove_dampedReturn_of_bddAbove_normalizedCapital (x : ℕ → ℝ)
    (hx : ∀ t, |x t| ≤ 1)
    (hbound : BddAbove (Set.range (multiplicativeCapital (normalizedWager x)))) :
    BddAbove (Set.range (weightedReturn (damping x) x)) := by
  rcases hbound with ⟨b, hb⟩
  refine ⟨Real.log b + 1, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hl := dampedReturn_sub_one_le_log_normalizedCapital x hx n
  have hlog := Real.log_le_log
    (multiplicativeCapital_pos _ (normalizedWager_gt_neg_one x hx) n)
    (hb (Set.mem_range_self n))
  linarith

/-- A positive reserve turns the logarithmic capital bound into the quadratic
lower envelope needed by Abel summation. -/
theorem reserve_lower_envelope (x : ℕ → ℝ) (δ : ℝ)
    (hx0 : ∀ t, -1 < x t) (hx1 : ∀ t, x t ≤ 1) (hδ : 0 < δ)
    (hreserve : ∀ n, δ ≤ multiplicativeCapital x n) (n : ℕ) :
    Real.log δ + (1 / 6 : ℝ) * quadraticVariation x n ≤ prefixReturn x n := by
  have hl := Real.log_le_log hδ (hreserve n)
  have hu := log_multiplicativeCapital_le x hx0 hx1 n
  linarith

theorem bddAbove_capital_of_bddAbove_prefixReturn (x : ℕ → ℝ)
    (hx0 : ∀ t, -1 < x t) (hx1 : ∀ t, x t ≤ 1)
    (hbound : BddAbove (Set.range (prefixReturn x))) :
    BddAbove (Set.range (multiplicativeCapital x)) := by
  rcases hbound with ⟨b, hb⟩
  refine ⟨Real.exp b, ?_⟩
  rintro _ ⟨n, rfl⟩
  apply (Real.log_le_iff_le_exp (multiplicativeCapital_pos x hx0 n)).1
  have hu := log_multiplicativeCapital_le x hx0 hx1 n
  have hq := quadraticVariation_nonneg x n
  linarith [hb (Set.mem_range_self n)]

/-- If reserved original capital were unbounded, the normalized capital could
not be bounded. This is the deterministic success-preservation argument of
Lemma 2, stated in its contrapositive form. -/
theorem bddAbove_capital_of_bddAbove_normalizedCapital (x : ℕ → ℝ) (δ : ℝ)
    (hx : ∀ t, |x t| < 1) (hδ : 0 < δ)
    (hreserve : ∀ n, δ ≤ multiplicativeCapital x n)
    (hbound : BddAbove (Set.range (multiplicativeCapital (normalizedWager x)))) :
    BddAbove (Set.range (multiplicativeCapital x)) := by
  have hx0 : ∀ t, -1 < x t := fun t ↦ (abs_lt.mp (hx t)).1
  have hx1 : ∀ t, x t ≤ 1 := fun t ↦ (abs_lt.mp (hx t)).2.le
  have hA := bddAbove_dampedReturn_of_bddAbove_normalizedCapital x (fun t ↦ (hx t).le) hbound
  have hM := bddAbove_prefixReturn_of_bddAbove_dampedReturn x (Real.log δ) (1 / 6)
    (by norm_num) (reserve_lower_envelope x δ hx0 hx1 hδ hreserve) hA
  exact bddAbove_capital_of_bddAbove_prefixReturn x hx0 hx1 hM

/-- Damping the signed returns preserves success along any path on which the
original capital stays above a positive reserve. -/
theorem normalization_preserves_unbounded_capital (x : ℕ → ℝ) (δ : ℝ)
    (hx : ∀ t, |x t| < 1) (hδ : 0 < δ)
    (hreserve : ∀ n, δ ≤ multiplicativeCapital x n)
    (hunbounded : ¬ BddAbove (Set.range (multiplicativeCapital x))) :
    ¬ BddAbove (Set.range (multiplicativeCapital (normalizedWager x))) := by
  intro hbound
  exact hunbounded (bddAbove_capital_of_bddAbove_normalizedCapital x δ hx hδ hreserve hbound)

end Klr
