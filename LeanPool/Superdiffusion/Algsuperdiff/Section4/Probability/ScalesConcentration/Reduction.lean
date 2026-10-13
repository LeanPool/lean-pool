/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.ScalesConcentration.Weights

/-!
# Reduction

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Concentration for scale arrays — Step 1 (reduction to a counting problem)

This module formalizes Step 1 of the proof (`e.YktoZk.twosided`): the
deterministic reduction of the weighted-row exceedance
`𝟙{Y_k > 3 λ s⁻¹}` to the column exceedance counts `Z_j`.

The paper's threshold is `2 λ s⁻¹` (from the sharp geometric constant `4/s`);
we use `3 λ s⁻¹` (from the clean constant `6/s`), see `Weights.lean`.

Main results:

* `sum_wt_half_le`: `∑_j 3^{-(s/2)|k-j|} ≤ 6/s`;
* `Yk_le_of_pointwise`: the pointwise implication of Step 1;
* `exists_exceed_of_Yk_gt`: contrapositive — a large `Y_k` forces a column
  exceedance;
* `indicator_Yk_le_tsum`: the pointwise `ℝ≥0∞` counting bound, the row
  indicator `𝟙{Y_k > 3λs⁻¹}` below the tsum of the column indicators;
* `sum_indicator_Yk_le_tsum_Zcount`: summed over `k ∈ {0,…,m}`.
-/

namespace Algsuperdiff.Section4.Probability.ScalesConcentration

open MeasureTheory Finset Real
open scoped ENNReal NNReal

variable {Ω : Type*}

lemma idist_eq (k j : ℤ) : idist k j = ((k - j).natAbs : ℝ) := by
  rw [idist, ← Int.cast_sub, Nat.cast_natAbs, Int.cast_abs]

/-- Summability of the half-weights `j ↦ 3^{-(s/2)|k-j|}`. -/
lemma summable_wt_half {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (k : ℤ) :
    Summable (fun j : ℤ => wt (s / 2) k j) := by
  have ht : 0 < s / 2 := by linarith
  have ht1 : s / 2 ≤ 1 := by linarith
  have hre : (fun j : ℤ => wt (s / 2) k j)
      = fun j : ℤ => (3 : ℝ) ^ (-((s / 2) * ((k - j).natAbs : ℝ))) := by
    funext j; simp only [wt, idist_eq]
  rw [hre]
  have hq0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s / 2)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hq1 : (3 : ℝ) ^ (-(s / 2)) < 1 := by
    rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by norm_num]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).2 (by linarith)
  have hbase : Summable (fun ℓ : ℤ => (3 : ℝ) ^ (-((s / 2) * (ℓ.natAbs : ℝ)))) := by
    have hpow : (fun ℓ : ℤ => (3 : ℝ) ^ (-((s / 2) * (ℓ.natAbs : ℝ))))
        = fun ℓ : ℤ => ((3 : ℝ) ^ (-(s / 2))) ^ ℓ.natAbs := by
      funext ℓ
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(s / 2))) ℓ.natAbs,
        ← Real.rpow_mul (by norm_num)]
      congr 1; ring
    rw [hpow]; exact summable_pow_natAbs hq0 hq1
  have := ((Equiv.subLeft k).summable_iff
    (f := fun ℓ : ℤ => (3 : ℝ) ^ (-((s / 2) * (ℓ.natAbs : ℝ))))).2 hbase
  simpa only [Function.comp_def, Equiv.subLeft_apply] using this

/-- The half-weight sum bound: `∑_j 3^{-(s/2)|k-j|} ≤ 6/s` for `s ∈ (0,1]`. -/
lemma sum_wt_half_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (k : ℤ) :
    ∑' j : ℤ, wt (s / 2) k j ≤ 6 / s := by
  have ht : 0 < s / 2 := by linarith
  have ht1 : s / 2 ≤ 1 := by linarith
  have hreindex : ∑' j : ℤ, wt (s / 2) k j
      = ∑' ℓ : ℤ, (3 : ℝ) ^ (-((s / 2) * (ℓ.natAbs : ℝ))) := by
    rw [← (Equiv.subLeft k).tsum_eq (fun j => wt (s / 2) k j)]
    congr 1
    funext ℓ
    simp only [Equiv.subLeft_apply, wt, idist_eq]
    congr 2
    have : k - (k - ℓ) = ℓ := by ring
    rw [this]
  rw [hreindex]
  calc ∑' ℓ : ℤ, (3 : ℝ) ^ (-((s / 2) * (ℓ.natAbs : ℝ)))
      ≤ 3 / (s / 2) := tsum_three_rpow_neg_abs_le ht ht1
    _ = 6 / s := by rw [div_div_eq_mul_div]; norm_num

/-- The termwise comparison `3^{-s|k-j|} X_{k,j} ≤ (λ/2) 3^{-(s/2)|k-j|}`
under the columnwise threshold bound. -/
lemma wt_mul_le_of_bound {s lam : ℝ} (X : ℤ → ℤ → Ω → ℝ) (k j : ℤ) (ω : Ω)
    (hb : X k j ω ≤ thr s lam k j) :
    wt s k j * X k j ω ≤ (lam / 2) * wt (s / 2) k j := by
  have h1 : wt s k j * X k j ω ≤ wt s k j * thr s lam k j :=
    mul_le_mul_of_nonneg_left hb (wt_nonneg s k j)
  refine h1.trans (le_of_eq ?_)
  unfold wt thr
  rw [show (3 : ℝ) ^ (-(s * idist k j)) * ((lam / 2) * 3 ^ (s / 2 * idist k j))
      = (lam / 2) * ((3 : ℝ) ^ (-(s * idist k j)) * 3 ^ (s / 2 * idist k j)) by ring,
    ← Real.rpow_add (by norm_num),
    show -(s * idist k j) + s / 2 * idist k j = -(s / 2 * idist k j) by ring]

/-- Summability of the weighted row when `X` is bounded columnwise by the
Step-2 thresholds. -/
lemma summable_wt_mul_of_le {s lam : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (X : ℤ → ℤ → Ω → ℝ) (k : ℤ) (ω : Ω)
    (hXnn : ∀ j, 0 ≤ X k j ω)
    (hbound : ∀ j, X k j ω ≤ thr s lam k j) :
    Summable (fun j : ℤ => wt s k j * X k j ω) := by
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (wt_nonneg s k j) (hXnn j))
    (fun j => wt_mul_le_of_bound X k j ω (hbound j))
    ((summable_wt_half hs hs1 k).mul_left (lam / 2))

/-- **Step 1, pointwise bound.**  If every column at row `k` is below its
threshold, then the weighted row `Y_k` is at most `3 λ s⁻¹`. -/
lemma Yk_le_of_pointwise {s lam : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (X : ℤ → ℤ → Ω → ℝ) (k : ℤ) (ω : Ω) (hlam : 0 ≤ lam)
    (hXnn : ∀ j, 0 ≤ X k j ω)
    (hbound : ∀ j, X k j ω ≤ thr s lam k j) :
    Yk X s k ω ≤ 3 * lam / s := by
  have hsum1 := summable_wt_mul_of_le hs hs1 X k ω hXnn hbound
  have hsum2 : Summable (fun j : ℤ => (lam / 2) * wt (s / 2) k j) :=
    (summable_wt_half hs hs1 k).mul_left (lam / 2)
  have hle : Yk X s k ω ≤ ∑' j : ℤ, (lam / 2) * wt (s / 2) k j := by
    unfold Yk
    exact hsum1.tsum_le_tsum (fun j => wt_mul_le_of_bound X k j ω (hbound j)) hsum2
  refine hle.trans ?_
  rw [tsum_mul_left]
  have hbound' : ∑' j : ℤ, wt (s / 2) k j ≤ 6 / s := sum_wt_half_le hs hs1 k
  have : (lam / 2) * ∑' j : ℤ, wt (s / 2) k j ≤ (lam / 2) * (6 / s) :=
    mul_le_mul_of_nonneg_left hbound' (by linarith)
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

/-- **Step 1, contrapositive.**  If `Y_k > 3 λ s⁻¹` then some column exceeds
its threshold. -/
lemma exists_exceed_of_Yk_gt {s lam : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (X : ℤ → ℤ → Ω → ℝ) (k : ℤ) (ω : Ω) (hlam : 0 ≤ lam)
    (hXnn : ∀ j, 0 ≤ X k j ω)
    (hY : 3 * lam / s < Yk X s k ω) :
    ∃ j, thr s lam k j < X k j ω := by
  by_contra h
  push Not at h
  exact absurd (Yk_le_of_pointwise hs hs1 X k ω hlam hXnn h) (not_le.2 hY)

open Classical in
/-- The `ℝ≥0∞`-valued column count equals the cast of `Zcount`. -/
lemma zcount_cast_eq {s lam : ℝ} (X : ℤ → ℤ → Ω → ℝ) (m : ℕ) (j : ℤ) (ω : Ω) :
    (Zcount X s lam m j ω : ℝ≥0∞)
      = ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
          (if thr s lam k j < X k j ω then (1 : ℝ≥0∞) else 0) := by
  unfold Zcount
  push_cast
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : thr s lam k j < X k j ω <;> simp [h]

open Classical in
/-- **Step 1, pointwise `ℝ≥0∞` bound.**  The row indicator is dominated by the
tsum of column indicators. -/
lemma indicator_Yk_le_tsum {s lam : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (X : ℤ → ℤ → Ω → ℝ) (k : ℤ) (ω : Ω) (hlam : 0 ≤ lam)
    (hXnn : ∀ j, 0 ≤ X k j ω) :
    (if 3 * lam / s < Yk X s k ω then (1 : ℝ≥0∞) else 0)
      ≤ ∑' j : ℤ, (if thr s lam k j < X k j ω then (1 : ℝ≥0∞) else 0) := by
  by_cases hY : 3 * lam / s < Yk X s k ω
  · simp only [hY, ite_true]
    obtain ⟨j₀, hj₀⟩ := exists_exceed_of_Yk_gt hs hs1 X k ω hlam hXnn hY
    calc (1 : ℝ≥0∞) = (if thr s lam k j₀ < X k j₀ ω then (1 : ℝ≥0∞) else 0) := by
            simp [hj₀]
      _ ≤ ∑' j : ℤ, (if thr s lam k j < X k j ω then (1 : ℝ≥0∞) else 0) :=
            ENNReal.le_tsum (f := fun j => if thr s lam k j < X k j ω then (1 : ℝ≥0∞) else 0) j₀
  · simp [hY]

/-- Swap a finite sum and a `tsum` in `ℝ≥0∞` (both always defined). -/
lemma tsum_finsetSum_swap {ι : Type*} (s : Finset ι) (f : ι → ℤ → ℝ≥0∞) :
    ∑ i ∈ s, ∑' j : ℤ, f i j = ∑' j : ℤ, ∑ i ∈ s, f i j := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, ih, ← ENNReal.tsum_add]
      exact tsum_congr (fun j => (Finset.sum_cons (f := fun i => f i j) ha).symm)

open Classical in
/-- **Step 1, summed `ℝ≥0∞` bound** (`e.YktoZk.twosided`).  The number of rows
`k ∈ {0,…,m}` with `Y_k > 3 λ s⁻¹` is at most `∑_j Z_j`. -/
lemma sum_indicator_Yk_le_tsum_Zcount {s lam : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (X : ℤ → ℤ → Ω → ℝ) (m : ℕ) (ω : Ω) (hlam : 0 ≤ lam)
    (hXnn : ∀ k j, 0 ≤ X k j ω) :
    (∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
        (if 3 * lam / s < Yk X s k ω then (1 : ℝ≥0∞) else 0))
      ≤ ∑' j : ℤ, (Zcount X s lam m j ω : ℝ≥0∞) := by
  calc ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
          (if 3 * lam / s < Yk X s k ω then (1 : ℝ≥0∞) else 0)
      ≤ ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
          ∑' j : ℤ, (if thr s lam k j < X k j ω then (1 : ℝ≥0∞) else 0) :=
        Finset.sum_le_sum (fun k _ =>
          indicator_Yk_le_tsum hs hs1 X k ω hlam (fun j => hXnn k j))
    _ = ∑' j : ℤ, ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
          (if thr s lam k j < X k j ω then (1 : ℝ≥0∞) else 0) :=
        tsum_finsetSum_swap _ _
    _ = ∑' j : ℤ, (Zcount X s lam m j ω : ℝ≥0∞) := by
        exact tsum_congr (fun j => (zcount_cast_eq X m j ω).symm)

end Algsuperdiff.Section4.Probability.ScalesConcentration
