/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Level.Basic
public import LeanPool.AaronsonAmbainis.Level.Median
public import LeanPool.AaronsonAmbainis.Level.ThirdMoment

/-!
# The mean absolute increments: from the third-moment inequality to the variance

Let `f` be a real function on the cube with rows of cost at most `K` at every point, and let
`M ≥ 0` bound all the mean absolute increments `L_j = meanAbsIncr f j`. With a median `m` of `f`,
the third-moment inequality and the inequality on the other side (`Level.thirdMoment_lower`) give
`E|f - m|^3 ≤ 6 K² M` (`Level.exists_abs_cube_le`). Since `Var f ≤ E (f - m)²` and
`(E z²)^3 ≤ (E |z|^3)^2`, it follows that

`Var(f)^3 ≤ 36 K^4 M²`                                  (`Level.variance_cube_le`).

Taking `M = max_j L_j` (Theorem 7.10 of the paper):

* `meanIncrement_of_thirdMoment : ThirdMomentInequality → MeanIncrementBound` — some `j` has
  `Var(f)^3 ≤ 36 K^4 L_j²`;
* `Level.exists_meanAbsIncr_ge_sqrt` — the same with the power `3/2` written as `Var · √Var`:
  `Var(f)^{3/2} ≤ 6 K² L_j` (the two forms are equivalent: `Level.cube_le_iff_mul_sqrt_le`).

No bound on the values of `f` is used. That `K > 0` under these hypotheses is `Level.cost_pos`.
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

namespace Level

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `E|f - m|^3 ≤ 6 K² M` for a median `m` of `f`. -/
theorem exists_abs_cube_le (hTM : ThirdMomentInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M) :
    ∃ m : ℝ, (∑ x, |f x - m| ^ 3) / 2 ^ Fintype.card ι ≤ 6 * K ^ 2 * M := by
  obtain ⟨m, hm1, hm2⟩ := exists_median f
  refine ⟨m, ?_⟩
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hcard : ((Fintype.card (Cube ι) : ℕ) : ℝ) = 2 ^ Fintype.card ι := card_cube
  -- each of the two sets `{f ≤ m}`, `{m ≤ f}` has measure at least `1/2`
  have hB1 : (1 : ℝ) / 2
      ≤ ((univ.filter (fun y : Cube ι => f y ≤ m)).card : ℝ) / 2 ^ Fintype.card ι := by
    rw [le_div_iff₀ h2]
    have h : ((Fintype.card (Cube ι) : ℕ) : ℝ)
        ≤ 2 * ((univ.filter (fun y : Cube ι => f y ≤ m)).card : ℝ) := by exact_mod_cast hm1
    rw [hcard] at h
    linarith
  have hB2 : (1 : ℝ) / 2
      ≤ ((univ.filter (fun y : Cube ι => m ≤ f y)).card : ℝ) / 2 ^ Fintype.card ι := by
    rw [le_div_iff₀ h2]
    have h : ((Fintype.card (Cube ι) : ℕ) : ℝ)
        ≤ 2 * ((univ.filter (fun y : Cube ι => m ≤ f y)).card : ℝ) := by exact_mod_cast hm2
    rw [hcard] at h
    linarith
  have hup := hTM ι f K a ha hsum hrow M hM0 hM m
  have hlo := thirdMoment_lower hTM f a ha hsum hrow hM0 hM m
  have hPnn : 0 ≤ (∑ x, max (f x - m) 0 ^ 3) / 2 ^ Fintype.card ι :=
    div_nonneg (Finset.sum_nonneg fun x _ => pow_nonneg (le_max_right _ _) 3) h2.le
  have hQnn : 0 ≤ (∑ x, max (m - f x) 0 ^ 3) / 2 ^ Fintype.card ι :=
    div_nonneg (Finset.sum_nonneg fun x _ => pow_nonneg (le_max_right _ _) 3) h2.le
  have hP : (∑ x, max (f x - m) 0 ^ 3) / 2 ^ Fintype.card ι ≤ 3 * K ^ 2 * M := by
    have h := mul_le_mul_of_nonneg_left hB1 hPnn
    linarith
  have hQ : (∑ x, max (m - f x) 0 ^ 3) / 2 ^ Fintype.card ι ≤ 3 * K ^ 2 * M := by
    have h := mul_le_mul_of_nonneg_left hB2 hQnn
    linarith
  have hsplit : ∑ x, |f x - m| ^ 3
      = ∑ x, max (f x - m) 0 ^ 3 + ∑ x, max (m - f x) 0 ^ 3 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rcases le_total 0 (f x - m) with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith : m - f x ≤ 0)]
      ring
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith : 0 ≤ m - f x)]
      ring
  rw [hsplit, add_div]
  linarith

/-- `Var(f)^3 ≤ 36 K^4 M²` when `f` has rows of cost at most `K` everywhere and `M ≥ 0` bounds
all the mean absolute increments `L_j = meanAbsIncr f j`. -/
theorem variance_cube_le (hTM : ThirdMomentInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M) :
    variance f ^ 3 ≤ 36 * K ^ 4 * M ^ 2 := by
  obtain ⟨m, hm⟩ := exists_abs_cube_le hTM f a ha hsum hrow hM0 hM
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hV0 : 0 ≤ variance f := variance_nonneg f
  have hV := variance_le_sq_dist f m
  have hpm := sum_sq_cube_le (univ : Finset (Cube ι)) (fun x => f x - m)
  rw [Finset.card_univ, card_cube] at hpm
  have hT0 : 0 ≤ (∑ x, |f x - m| ^ 3) / 2 ^ Fintype.card ι :=
    div_nonneg (Finset.sum_nonneg fun x _ => pow_nonneg (abs_nonneg _) 3) h2.le
  calc variance f ^ 3 ≤ ((∑ x, (f x - m) ^ 2) / 2 ^ Fintype.card ι) ^ 3 :=
        pow_le_pow_left₀ hV0 hV 3
    _ ≤ ((∑ x, |f x - m| ^ 3) / 2 ^ Fintype.card ι) ^ 2 := by
        rw [div_pow, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        have h7 := mul_le_mul_of_nonneg_right hpm (sq_nonneg ((2 : ℝ) ^ Fintype.card ι))
        calc (∑ x, (f x - m) ^ 2) ^ 3 * ((2 : ℝ) ^ Fintype.card ι) ^ 2
            ≤ 2 ^ Fintype.card ι * (∑ x, |f x - m| ^ 3) ^ 2 * ((2 : ℝ) ^ Fintype.card ι) ^ 2 := h7
          _ = (∑ x, |f x - m| ^ 3) ^ 2 * ((2 : ℝ) ^ Fintype.card ι) ^ 3 := by ring
    _ ≤ (6 * K ^ 2 * M) ^ 2 := pow_le_pow_left₀ hT0 hm 2
    _ = 36 * K ^ 4 * M ^ 2 := by ring

end Level

/-- The bound for the mean absolute increments (Theorem 7.10 of the paper) from the third-moment
inequality (Theorem 7.6): if `Var(f) > 0` and `f` has rows of cost at most `K` everywhere, then
some coordinate `j` has `Var(f)^3 ≤ 36 K^4 L_j²`, where
`L_j = meanAbsIncr f j = E|f(x) - f(x^j)|`. -/
theorem meanIncrement_of_thirdMoment : ThirdMomentInequality → MeanIncrementBound := by
  intro hTM ι _ _ f K a ha hsum hrow hvar
  have hne : Nonempty ι := by
    by_contra hemp
    have hι : IsEmpty ι := not_nonempty_iff.mp hemp
    rw [Level.variance_eq_zero_of_isEmpty f] at hvar
    exact lt_irrefl 0 hvar
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image univ (meanAbsIncr f) univ_nonempty
  exact ⟨j, Level.variance_cube_le hTM f a ha hsum hrow (Level.meanAbsIncr_nonneg f j)
    (fun j' => hj j' (mem_univ _))⟩

namespace Level

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- For `V, L ≥ 0`: `V^3 ≤ 36 K^4 L²` if and only if `V^{3/2} ≤ 6 K² L`, where `V^{3/2}` is written
`V · √V`. -/
theorem cube_le_iff_mul_sqrt_le {V K L : ℝ} (hV : 0 ≤ V) (hL : 0 ≤ L) :
    V ^ 3 ≤ 36 * K ^ 4 * L ^ 2 ↔ V * Real.sqrt V ≤ 6 * K ^ 2 * L := by
  have ha : 0 ≤ V * Real.sqrt V := mul_nonneg hV (Real.sqrt_nonneg V)
  have hb : 0 ≤ 6 * K ^ 2 * L := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K)) hL
  have e1 : (V * Real.sqrt V) ^ 2 = V ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hV]
    ring
  have e2 : (6 * K ^ 2 * L) ^ 2 = 36 * K ^ 4 * L ^ 2 := by ring
  constructor
  · intro h
    apply le_of_pow_le_pow_left₀ two_ne_zero hb
    rw [e1, e2]
    exact h
  · intro h
    have h2 := pow_le_pow_left₀ ha h 2
    rw [e1, e2] at h2
    exact h2

/-- The bound for the mean absolute increments with the power `3/2` written as `Var · √Var`:
some coordinate `j` has `Var(f)^{3/2} ≤ 6 K² L_j`, that is, `L_j ≥ Var(f)^{3/2} / (6 K²)`. -/
theorem exists_meanAbsIncr_ge_sqrt (hMI : MeanIncrementBound) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (hvar : 0 < variance f) :
    ∃ j, variance f * Real.sqrt (variance f) ≤ 6 * K ^ 2 * meanAbsIncr f j := by
  obtain ⟨j, hj⟩ := hMI ι f K a ha hsum hrow hvar
  exact ⟨j, (cube_le_iff_mul_sqrt_le hvar.le (meanAbsIncr_nonneg f j)).mp hj⟩

end Level

end AaronsonAmbainis
