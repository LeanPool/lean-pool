/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Fekete's lemma with a bounded defect

If `u (m + n) ≤ u m + u n + C` for all `m, n`, then `u + C` is subadditive, so Fekete's lemma
applies directly. We record the resulting limit together with the uniform one-sided bound
`n * L - C ≤ u n`, its two-sided form for almost additive sequences, and the multiplicative form.

## Main statements

* `exists_tendsto_div_of_le_add_const`: bounded defect, with `n * L - C ≤ u n` for all `n`.
* `exists_tendsto_div_of_abs_sub_le`: almost additive sequences, with `|u n - n * L| ≤ C`.
* `exists_tendsto_rpow_inv_of_le_mul_const`: the multiplicative form, `a (m + n) ≤ K * a m * a n`
  gives `a n ^ (1 / n) → L` with `L ^ n ≤ K * a n`.

## References

* [S. Gouëzel, *Ergodic theory* (Isabelle AFP), lemma `almost_additive_converges`][Gouezel2015AFP]
-/

@[expose] public section

open Filter
open scoped Topology

/-- A linear lower bound `n * b ≤ u n` for `n > 0` bounds `u n / n` below. -/
private theorem bddBelow_div_of_mul_le {u : ℕ → ℝ} {b : ℝ} (h : ∀ n, 0 < n → n * b ≤ u n) :
    BddBelow (Set.range fun n : ℕ ↦ u n / n) := by
  refine ⟨min b 0, ?_⟩
  rintro _ ⟨n, rfl⟩
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  rw [le_div_iff₀ (Nat.cast_pos.2 hn)]
  linarith [h n hn, mul_le_mul_of_nonneg_right (min_le_left b 0) (Nat.cast_nonneg n)]

/-- **Fekete's lemma with a bounded defect.** If `u (m + n) ≤ u m + u n + C` for all `m, n` and
`u n / n` is bounded below, then `u n / n → L` for some `L` with `n * L - C ≤ u n` for all `n`. -/
theorem exists_tendsto_div_of_le_add_const {u : ℕ → ℝ} {C : ℝ}
    (h : ∀ m n, u (m + n) ≤ u m + u n + C) (hbdd : BddBelow (Set.range fun n ↦ u n / n)) :
    ∃ L, Tendsto (fun n ↦ u n / n) atTop (𝓝 L) ∧ ∀ n : ℕ, n * L - C ≤ u n := by
  have hs : Subadditive fun n ↦ u n + C := fun m n ↦ by linarith [h m n]
  have hbdd' : BddBelow (Set.range fun n : ℕ ↦ (u n + C) / n) := by
    obtain ⟨b, hb⟩ := hbdd
    refine bddBelow_div_of_mul_le (b := b - |C|) fun n hn ↦ ?_
    have := (le_div_iff₀ (Nat.cast_pos.2 hn)).1 (hb ⟨n, rfl⟩)
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [le_mul_of_one_le_left (abs_nonneg C) h1, neg_abs_le C]
  refine ⟨hs.lim, ?_, fun n ↦ ?_⟩
  · refine ((hs.tendsto_lim hbdd').sub (tendsto_const_div_atTop_nhds_zero_nat C)).congr' ?_
      |>.trans (by rw [sub_zero])
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [add_div, add_sub_cancel_right]
  · rcases n.eq_zero_or_pos with rfl | hn
    · simpa using (show -C ≤ u 0 by linarith [h 0 0])
    have := (le_div_iff₀ (Nat.cast_pos.2 hn)).1 (hs.lim_le_div hbdd' hn.ne')
    linarith

/-- **Almost additive sequences.** If `|u (m + n) - u m - u n| ≤ C` for all `m, n`, then
`u n / n → L` for some `L` with `|u n - n * L| ≤ C` for every `n`. -/
theorem exists_tendsto_div_of_abs_sub_le {u : ℕ → ℝ} {C : ℝ}
    (h : ∀ m n, |u (m + n) - u m - u n| ≤ C) :
    ∃ L, Tendsto (fun n ↦ u n / n) atTop (𝓝 L) ∧ ∀ n : ℕ, |u n - n * L| ≤ C := by
  have hup : ∀ m n, u (m + n) ≤ u m + u n + C := fun m n ↦ by linarith [(abs_le.1 (h m n)).2]
  have hlo : ∀ m n, -u (m + n) ≤ -u m + -u n + C := fun m n ↦ by
    linarith [(abs_le.1 (h m n)).1]
  -- `n * (u 1 - C) ≤ u n ≤ n * (u 1 + C)` for `n ≥ 1`, so `u n / n` is bounded
  have hC : 0 ≤ C := (abs_nonneg _).trans (h 0 0)
  have hlin : ∀ n, 0 < n → n * (u 1 - C) ≤ u n ∧ n * -(u 1 + C) ≤ -u n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => constructor <;> simp <;> linarith
    | succ n hn ih => push_cast; constructor <;> linarith [ih.1, ih.2, hup n 1, hlo n 1]
  obtain ⟨L, hL, hLu⟩ :=
    exists_tendsto_div_of_le_add_const hup (bddBelow_div_of_mul_le fun n hn ↦ (hlin n hn).1)
  obtain ⟨L', hL', hLu'⟩ :=
    exists_tendsto_div_of_le_add_const hlo (bddBelow_div_of_mul_le fun n hn ↦ (hlin n hn).2)
  obtain rfl : L' = -L := tendsto_nhds_unique hL' (by simpa [neg_div] using hL.neg)
  exact ⟨L, hL, fun n ↦ abs_le.2 ⟨by linarith [hLu n], by linarith [hLu' n, mul_neg (n : ℝ) L]⟩⟩

/-- **Submultiplicative sequences with a bounded defect.** If `a n > 0` for `n ≠ 0`,
`a (m + n) ≤ K * a m * a n` for all `m, n` with `K > 0`, and `a n ≥ c ^ n` for some `c > 0`, then
`a n ^ (1 / n) → L` for some `L > 0` with `L ^ n ≤ K * a n` for every `n`. (Positivity of `a 0`
follows from the hypotheses.) -/
theorem exists_tendsto_rpow_inv_of_le_mul_const {a : ℕ → ℝ} {K : ℝ} (ha : ∀ n, n ≠ 0 → 0 < a n)
    (hK : 0 < K) (h : ∀ m n, a (m + n) ≤ K * a m * a n) (hc : ∃ c > 0, ∀ n : ℕ, c ^ n ≤ a n) :
    ∃ L > 0, Tendsto (fun n ↦ a n ^ (n : ℝ)⁻¹) atTop (𝓝 L) ∧ ∀ n : ℕ, L ^ n ≤ K * a n := by
  have ha : ∀ n, 0 < a n := by
    have ha1 := ha 1 one_ne_zero
    have ha0 : 0 < a 0 := by
      by_contra! h0
      have := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hK.le h0) ha1.le
      linarith [zero_add 1 ▸ h 0 1]
    exact fun n ↦ (eq_or_ne n 0).elim (· ▸ ha0) (ha n)
  have hlog : ∀ m n, Real.log (a (m + n)) ≤ Real.log (a m) + Real.log (a n) + Real.log K :=
    fun m n ↦ by
      have := Real.log_le_log (ha _) (h m n)
      rwa [Real.log_mul (mul_pos hK (ha m)).ne' (ha n).ne', Real.log_mul hK.ne' (ha m).ne',
        add_comm (Real.log K), add_right_comm] at this
  obtain ⟨c, hc0, hcn⟩ := hc
  obtain ⟨ℓ, hℓ, hℓa⟩ := exists_tendsto_div_of_le_add_const hlog <|
    bddBelow_div_of_mul_le fun n _ ↦ by
      simpa [Real.log_pow] using Real.log_le_log (pow_pos hc0 n) (hcn n)
  refine ⟨Real.exp ℓ, Real.exp_pos ℓ, ((Real.continuous_exp.tendsto _).comp hℓ).congr
    fun n ↦ ?_, fun n ↦ ?_⟩
  · simp [Real.rpow_def_of_pos (ha n), div_eq_mul_inv]
  · rw [← Real.exp_nat_mul, ← Real.exp_log (mul_pos hK (ha n)), Real.log_mul hK.ne' (ha n).ne']
    exact Real.exp_le_exp.2 (by linarith [hℓa n])
