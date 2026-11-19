/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Superadditive and supermultiplicative sequences

We first complete Fekete's lemma for subadditive sequences with the unbounded case: if `u` is
subadditive and `u n / n` is not bounded below, then `u n / n → -∞`
(`Subadditive.tendsto_div_atBot`).

A sequence is superadditive if `u m + u n ≤ u (m + n)`, and supermultiplicative if
`u m * u n ≤ u (m + n)`. Fekete's lemma for these follows from the subadditive case: `u n / n`
converges to `⨆ n ≥ 1, u n / n` (possibly `+∞`), and for a positive supermultiplicative sequence
`u n ^ (1 / n)` converges to `⨆ n ≥ 1, u n ^ (1 / n)` (possibly `+∞`).

## Main definitions

* `Supermultiplicative u`: `u m * u n ≤ u (m + n)` for all `m, n`.
* `Superadditive u`: `u m + u n ≤ u (m + n)` for all `m, n`.

## Main statements

* `Subadditive.tendsto_div_atBot`: the unbounded case of Fekete's lemma.
* `superadditive_neg_iff`, `subadditive_neg_iff`: negation swaps the two notions.
* `Superadditive.tendsto_lim`, `Superadditive.tendsto_div_atTop`: Fekete's lemma.
* `Supermultiplicative.tendsto_lim`, `Supermultiplicative.tendsto_rpow_inv_atTop`:
  its multiplicative form, for sequences with `u n > 0` for `n ≠ 0`.

## Implementation notes

`Subadditive.tendsto_div_atBot` truncates `u` at a line: `w n = max (u n) (a * n)` is again
subadditive, since `max (x + y) (z + t) ≤ max x z + max y t`, and `w n / n` is bounded below, so
`Subadditive.tendsto_lim` applies to `w`.

The positivity hypothesis on supermultiplicative sequences (`u n > 0` for `n ≠ 0`; `u 0` is
unconstrained) cannot be weakened to `0 ≤ u n`: `u n = if Even n then 1 else 0` is nonnegative
and supermultiplicative, but `u n ^ (1 / n)` alternates between `0` and `1`
(`Supermultiplicative.exists_nonneg_not_tendsto_rpow_inv`). Unlike the submultiplicative case,
zeros of a supermultiplicative sequence do not propagate.

## References

* [S. Gouëzel, *Ergodic theory* (Isabelle AFP), theory `Fekete`][Gouezel2015AFP]
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

/-- **Fekete's lemma, unbounded case.** If `u` is subadditive and `u n / n` is not bounded below,
then `u n / n → -∞`. Together with `Subadditive.tendsto_lim` this says that `u n / n` always
converges in `[-∞, ∞)`. -/
theorem Subadditive.tendsto_div_atBot {u : ℕ → ℝ} (h : Subadditive u)
    (hbdd : ¬ BddBelow (range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop atBot := by
  refine tendsto_atBot.2 fun b ↦ ?_
  set a := min b 0 - 1
  have ha : a < 0 := by linarith [min_le_right b 0]
  -- truncating `u` at the line `a * n` keeps it subadditive and bounds `u n / n` below
  set w : ℕ → ℝ := fun n ↦ max (u n) (a * n)
  have hw : Subadditive w := fun m n ↦ by
    simp only [w, Nat.cast_add, mul_add]
    exact (max_le_max (h m n) le_rfl).trans max_add_add_le_max_add_max
  have hdiv : ∀ n : ℕ, n ≠ 0 → w n / n = max (u n / n) a := fun n hn ↦ by
    have hn' : (0 : ℝ) < n := by positivity
    rw [← mul_div_cancel_right₀ a hn'.ne', max_div_div_right hn'.le]
  have hbddw : BddBelow (range fun n ↦ w n / n) := ⟨a, by
    rintro _ ⟨n, rfl⟩
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha.le]
    · exact (le_max_right _ _).trans_eq (hdiv n hn).symm⟩
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := not_bddBelow_iff.1 hbdd a
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; linarith
  have hlim : hw.lim ≤ a := by
    simpa [hdiv k hk0, max_eq_right hk.le] using hw.lim_le_div hbddw hk0
  filter_upwards [(hw.tendsto_lim hbddw).eventually (gt_mem_nhds (show hw.lim < a + 1 by linarith))]
    with n hn
  calc u n / n ≤ w n / n := div_le_div_of_nonneg_right (le_max_left _ _) n.cast_nonneg
    _ ≤ b := by linarith [min_le_left b 0]

/-- A sequence is supermultiplicative if it satisfies the inequality `u m * u n ≤ u (m + n)`
for all `m, n`. -/
@[to_additive Superadditive /-- A sequence is superadditive if it satisfies the inequality
`u m + u n ≤ u (m + n)` for all `m, n`. -/]
def Supermultiplicative {α β : Type*} [Add α] [Mul β] [LE β] (u : α → β) : Prop :=
  ∀ m n, u m * u n ≤ u (m + n)

/-- The negation of a subadditive sequence is superadditive. -/
theorem Subadditive.superadditive_neg {u : ℕ → ℝ} (h : Subadditive u) :
    Superadditive fun n ↦ -u n := fun m n ↦ by linarith [h m n]

/-- The negation of a superadditive sequence is subadditive. -/
theorem Superadditive.subadditive_neg {u : ℕ → ℝ} (h : Superadditive u) :
    Subadditive fun n ↦ -u n := fun m n ↦ by linarith [h m n]

@[simp]
theorem superadditive_neg_iff {u : ℕ → ℝ} : (Superadditive fun n ↦ -u n) ↔ Subadditive u :=
  ⟨fun h ↦ by simpa using h.subadditive_neg, Subadditive.superadditive_neg⟩

@[simp]
theorem subadditive_neg_iff {u : ℕ → ℝ} : (Subadditive fun n ↦ -u n) ↔ Superadditive u :=
  ⟨fun h ↦ by simpa using h.superadditive_neg, Superadditive.subadditive_neg⟩

namespace Superadditive

variable {u : ℕ → ℝ} (h : Superadditive u)

/-- The limit `⨆ n ≥ 1, u n / n` of a bounded-above superadditive sequence; the convergence is
`Superadditive.tendsto_lim`. It takes the sequence, not the superadditivity proof, so that it has
no unused argument. -/
@[irreducible]
protected def lim (u : ℕ → ℝ) : ℝ :=
  sSup ((fun n : ℕ ↦ u n / n) '' Ici 1)

/-- Every `u n / n` with `n ≠ 0` is bounded by `Superadditive.lim u`. -/
theorem div_le_lim (hbdd : BddAbove (range fun n ↦ u n / n)) {n : ℕ} (hn : n ≠ 0) :
    u n / n ≤ Superadditive.lim u := by
  rw [Superadditive.lim]
  exact le_csSup (hbdd.mono (image_subset_range _ _)) ⟨n, Nat.one_le_iff_ne_zero.2 hn, rfl⟩

include h in
/-- **Fekete's lemma, superadditive form**: if `u n / n` is bounded above, it converges to its
supremum over `n ≥ 1`. -/
theorem tendsto_lim (hbdd : BddAbove (range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop (𝓝 (Superadditive.lim u)) := by
  have hbdd' : BddBelow (range fun n ↦ -u n / n) := by
    obtain ⟨b, hb⟩ := hbdd
    exact ⟨-b, by rintro _ ⟨n, rfl⟩; simpa [neg_div] using hb ⟨n, rfl⟩⟩
  have hs := h.subadditive_neg
  have hneg : Tendsto (fun n ↦ u n / n) atTop (𝓝 (-hs.lim)) := by
    simpa [neg_div] using (hs.tendsto_lim hbdd').neg
  suffices -hs.lim = Superadditive.lim u by rwa [← this]
  refine le_antisymm (le_of_tendsto hneg ?_) ?_
  · filter_upwards [eventually_ne_atTop 0] with n hn
    exact div_le_lim hbdd hn
  · rw [Superadditive.lim]
    refine csSup_le ((nonempty_Ici).image _) fun _ ⟨n, hn, h'⟩ ↦ h' ▸ ?_
    have := hs.lim_le_div hbdd' (Nat.one_le_iff_ne_zero.1 hn)
    rw [neg_div] at this
    linarith

include h in
/-- **Fekete's lemma, superadditive form, unbounded case**: if `u n / n` is not bounded above,
then `u n / n → ∞`. -/
theorem tendsto_div_atTop (hbdd : ¬ BddAbove (range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop atTop := by
  have hbdd' : ¬ BddBelow (range fun n ↦ -u n / n) := by
    rintro ⟨b, hb⟩
    exact hbdd ⟨-b, by rintro _ ⟨n, rfl⟩; have := hb ⟨n, rfl⟩; simp [neg_div] at this; linarith⟩
  have := tendsto_neg_atBot_atTop.comp (h.subadditive_neg.tendsto_div_atBot hbdd')
  simpa [neg_div, Function.comp_def] using this

end Superadditive

namespace Supermultiplicative

variable {u : ℕ → ℝ}

/-- The logarithm of a positive supermultiplicative sequence is superadditive. -/
theorem superadditive_log (h : Supermultiplicative u) (hpos : ∀ n, 0 < u n) :
    Superadditive fun n ↦ Real.log (u n) := fun m n ↦ by
  rw [← Real.log_mul (hpos m).ne' (hpos n).ne']
  exact Real.log_le_log (mul_pos (hpos m) (hpos n)) (h m n)

/-- `log ∘ u` with the value at `0` replaced by `0` is superadditive when `u n > 0` for `n ≠ 0`. -/
private theorem superadditive_log_ite (h : Supermultiplicative u)
    (hpos : ∀ n, n ≠ 0 → 0 < u n) :
    Superadditive fun n ↦ if n = 0 then 0 else Real.log (u n) := fun m n ↦ by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hmn : m + n ≠ 0 := by omega
  simp only [hm, hn, hmn, ↓reduceIte]
  rw [← Real.log_mul (hpos m hm).ne' (hpos n hn).ne']
  exact Real.log_le_log (mul_pos (hpos m hm) (hpos n hn)) (h m n)

private theorem ite_log_div (u : ℕ → ℝ) :
    (fun n : ℕ ↦ (if n = 0 then 0 else Real.log (u n)) / n) = fun n ↦ Real.log (u n) / n := by
  funext n
  split_ifs with hn <;> simp [hn]

private theorem rpow_inv_eq_exp (hpos : ∀ n, n ≠ 0 → 0 < u n) (n : ℕ) :
    u n ^ (n : ℝ)⁻¹ = Real.exp (Real.log (u n) / n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [Real.rpow_def_of_pos (hpos n hn), div_eq_mul_inv]

/-- The limit `⨆ n ≥ 1, u n ^ (1 / n)` of a bounded-above supermultiplicative sequence; the
convergence is `Supermultiplicative.tendsto_lim`. It takes the sequence, not the
supermultiplicativity proof, so that it has no unused argument. -/
@[irreducible]
protected def lim (u : ℕ → ℝ) : ℝ :=
  sSup ((fun n : ℕ ↦ u n ^ (n : ℝ)⁻¹) '' Ici 1)

/-- Every `u n ^ (1 / n)` with `n ≠ 0` is bounded by `Supermultiplicative.lim u`. -/
theorem rpow_le_lim (hbdd : BddAbove (range fun n ↦ u n ^ (n : ℝ)⁻¹)) {n : ℕ} (hn : n ≠ 0) :
    u n ^ (n : ℝ)⁻¹ ≤ Supermultiplicative.lim u := by
  rw [Supermultiplicative.lim]
  exact le_csSup (hbdd.mono (image_subset_range _ _)) ⟨n, Nat.one_le_iff_ne_zero.2 hn, rfl⟩

/-- **Fekete's lemma, supermultiplicative form**: if `u n > 0` for `n ≠ 0`, `u` is
supermultiplicative and `u n ^ (1 / n)` is bounded above, then it converges to its supremum over
`n ≥ 1`. -/
theorem tendsto_lim (h : Supermultiplicative u) (hpos : ∀ n, n ≠ 0 → 0 < u n)
    (hbdd : BddAbove (range fun n ↦ u n ^ (n : ℝ)⁻¹)) :
    Tendsto (fun n ↦ u n ^ (n : ℝ)⁻¹) atTop (𝓝 (Supermultiplicative.lim u)) := by
  have hs := h.superadditive_log_ite hpos
  have hbdd' : BddAbove (range fun n ↦ Real.log (u n) / n) := by
    obtain ⟨b, hb⟩ := hbdd
    have hb0 : 0 < b := one_pos.trans_le (by simpa using hb ⟨0, rfl⟩)
    refine ⟨Real.log b, ?_⟩
    rintro _ ⟨n, rfl⟩
    have := hb ⟨n, rfl⟩
    simp only [rpow_inv_eq_exp hpos] at this
    exact (Real.le_log_iff_exp_le hb0).2 this
  have hlim := hs.tendsto_lim (by rwa [ite_log_div])
  rw [ite_log_div] at hlim
  have hexp := (Real.continuous_exp.tendsto _).comp hlim
  have hfun : (Real.exp ∘ fun n ↦ Real.log (u n) / n) = fun n ↦ u n ^ (n : ℝ)⁻¹ :=
    funext fun n ↦ (rpow_inv_eq_exp hpos n).symm
  rw [hfun] at hexp
  convert hexp using 2
  rw [Supermultiplicative.lim, Superadditive.lim, ite_log_div,
    Real.exp_monotone.map_csSup_of_continuousAt Real.continuous_exp.continuousAt
      ((nonempty_Ici).image _) (hbdd'.mono (image_subset_range _ _)), image_image]
  simp [rpow_inv_eq_exp hpos]

/-- **Fekete's lemma, supermultiplicative form, unbounded case.** -/
theorem tendsto_rpow_inv_atTop (h : Supermultiplicative u) (hpos : ∀ n, n ≠ 0 → 0 < u n)
    (hbdd : ¬ BddAbove (range fun n ↦ u n ^ (n : ℝ)⁻¹)) :
    Tendsto (fun n ↦ u n ^ (n : ℝ)⁻¹) atTop atTop := by
  have hbdd' : ¬ BddAbove (range fun n ↦ Real.log (u n) / n) := fun ⟨b, hb⟩ ↦
    hbdd ⟨Real.exp b, by
      rintro _ ⟨n, rfl⟩
      exact (rpow_inv_eq_exp hpos n).trans_le (Real.exp_le_exp.2 (hb ⟨n, rfl⟩))⟩
  have := (h.superadditive_log_ite hpos).tendsto_div_atTop (by rwa [ite_log_div])
  rw [ite_log_div] at this
  exact (Real.tendsto_exp_atTop.comp this).congr fun n ↦ (rpow_inv_eq_exp hpos n).symm

end Supermultiplicative
