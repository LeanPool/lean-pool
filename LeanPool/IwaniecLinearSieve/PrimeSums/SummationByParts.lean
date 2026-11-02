/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Polynomial.Basic

/-!
# Comparing a Stieltjes-type sum with an integral

An abstract form of the summation by parts in [I71, Lemma 13]: if `g` is a cumulative counting
function that is within `ε` of `F` at the points `a 0 ≤ a 1 ≤ ⋯ ≤ a n`, with `F' = f ≥ 0` and
increments `F (a (j+1)) - F (a j) ≤ δ`, then for `b ≥ 0` monotone
`∑_j b (a (j+1)) (g (j+1) - g j) = ∫ b f + O((δ + 2ε) b (a n))`.
-/

@[expose] public section

open Finset MeasureTheory intervalIntegral

namespace IwaniecLinearSieve

/-- Abel summation bound: if `β` is nonnegative and monotone and `|e j| ≤ ε`, then
`|∑_{j<n} β (j+1) (e (j+1) - e j)| ≤ 2 ε β n`. -/
theorem abs_sum_mul_sub_le {n : ℕ} {β e : ℕ → ℝ} {ε : ℝ}
    (hβ : ∀ j < n, β j ≤ β (j + 1)) (hβ0 : 0 ≤ β 0) (he : ∀ j ≤ n, |e j| ≤ ε) :
    |∑ j ∈ range n, β (j + 1) * (e (j + 1) - e j)| ≤ 2 * ε * β n := by
  have key : ∀ m ≤ n, 0 ≤ β m ∧ β 0 ≤ β m ∧
      |∑ j ∈ range m, β (j + 1) * (e (j + 1) - e j) - β m * e m + β 0 * e 0| ≤
        ε * (β m - β 0) := by
    intro m hm
    induction m with
    | zero => simpa using hβ0
    | succ m ih =>
      obtain ⟨h0, h1, h2⟩ := ih (by omega)
      have hm' : β m ≤ β (m + 1) := hβ m (by omega)
      refine ⟨by linarith, by linarith, ?_⟩
      rw [sum_range_succ]
      have h3 : |(β (m + 1) - β m) * e m| ≤ (β (m + 1) - β m) * ε := by
        rw [abs_mul, abs_of_nonneg (by linarith)]
        exact mul_le_mul_of_nonneg_left (he m (by omega)) (by linarith)
      calc |∑ j ∈ range m, β (j + 1) * (e (j + 1) - e j) + β (m + 1) * (e (m + 1) - e m) -
            β (m + 1) * e (m + 1) + β 0 * e 0|
          = |(∑ j ∈ range m, β (j + 1) * (e (j + 1) - e j) - β m * e m + β 0 * e 0) -
              (β (m + 1) - β m) * e m| := by ring_nf
        _ ≤ |∑ j ∈ range m, β (j + 1) * (e (j + 1) - e j) - β m * e m + β 0 * e 0| +
              |(β (m + 1) - β m) * e m| := abs_sub _ _
        _ ≤ ε * (β m - β 0) + (β (m + 1) - β m) * ε := add_le_add h2 h3
        _ = ε * (β (m + 1) - β 0) := by ring
  obtain ⟨h0, h1, h2⟩ := key n le_rfl
  have hn : |β n * e n| ≤ β n * ε := by
    rw [abs_mul, abs_of_nonneg h0]; exact mul_le_mul_of_nonneg_left (he n le_rfl) h0
  have hz : |β 0 * e 0| ≤ β 0 * ε := by
    rw [abs_mul, abs_of_nonneg hβ0]; exact mul_le_mul_of_nonneg_left (he 0 (by omega)) hβ0
  rw [abs_le] at h2 hn hz ⊢
  constructor <;> nlinarith

/-- Abstract form of [I71, Lemma 13]. The points `a 0 ≤ ⋯ ≤ a n` partition `[a 0, a n]`;
`g j` is a cumulative counting function at `a j`, within `ε` of `F (a j)`, where `F' = f ≥ 0`
and `F` increases by at most `δ` on each piece. Then for `b ≥ 0` monotone,
`∑_j b (a (j+1)) (g (j+1) - g j)` is within `(δ + 2ε) b (a n)` of `∫ b f`. -/
theorem abs_sum_sub_integral_le {n : ℕ} {a : ℕ → ℝ} (ha : Monotone a) {b f F : ℝ → ℝ}
    {g : ℕ → ℝ} {δ ε : ℝ} (hδ0 : 0 ≤ δ)
    (hb : MonotoneOn b (Set.Icc (a 0) (a n))) (hb0 : 0 ≤ b (a 0))
    (hf : ∀ x ∈ Set.Icc (a 0) (a n), 0 ≤ f x) (hfc : ContinuousOn f (Set.Icc (a 0) (a n)))
    (hFf : ∀ j < n, ∫ x in a j..a (j + 1), f x = F (a (j + 1)) - F (a j))
    (hδ : ∀ j < n, F (a (j + 1)) - F (a j) ≤ δ)
    (hε : ∀ j ≤ n, |g j - F (a j)| ≤ ε) :
    |∑ j ∈ range n, b (a (j + 1)) * (g (j + 1) - g j) - ∫ x in a 0..a n, b x * f x| ≤
      (δ + 2 * ε) * b (a n) := by
  have hmem : ∀ j ≤ n, a j ∈ Set.Icc (a 0) (a n) := fun j hj ↦ ⟨ha (Nat.zero_le j), ha hj⟩
  have hsub : ∀ j < n, Set.Icc (a j) (a (j + 1)) ⊆ Set.Icc (a 0) (a n) := fun j hj x hx ↦
    ⟨(hmem j hj.le).1.trans hx.1, hx.2.trans (hmem (j + 1) hj).2⟩
  have hle : ∀ j, a j ≤ a (j + 1) := fun j ↦ ha (Nat.le_succ j)
  have hβ : ∀ j < n, b (a j) ≤ b (a (j + 1)) := fun j hj ↦
    hb (hmem j hj.le) (hmem (j + 1) hj) (hle j)
  have hint : ∀ j < n, IntervalIntegrable (fun x ↦ b x * f x) volume (a j) (a (j + 1)) := by
    intro j hj
    have h1 := hsub j hj
    rw [← Set.uIcc_of_le (hle j)] at h1
    exact (hb.mono h1).intervalIntegrable.mul_continuousOn (hfc.mono h1)
  have hintf : ∀ j < n, IntervalIntegrable f volume (a j) (a (j + 1)) := by
    intro j hj
    have h1 := hsub j hj
    rw [← Set.uIcc_of_le (hle j)] at h1
    exact (hfc.mono h1).intervalIntegrable
  -- the increments `I j = F (a (j+1)) - F (a j)` are nonnegative
  have hI : ∀ j < n, 0 ≤ F (a (j + 1)) - F (a j) := fun j hj ↦ by
    rw [← hFf j hj]
    exact intervalIntegral.integral_nonneg (hle j) fun x hx ↦ hf x (hsub j hj hx)
  -- each piece of the integral lies between `b (a j) I j` and `b (a (j+1)) I j`
  have hpiece : ∀ j < n, b (a j) * (F (a (j + 1)) - F (a j)) ≤ ∫ x in a j..a (j + 1), b x * f x ∧
      ∫ x in a j..a (j + 1), b x * f x ≤ b (a (j + 1)) * (F (a (j + 1)) - F (a j)) := by
    intro j hj
    rw [← hFf j hj, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    constructor
    · refine intervalIntegral.integral_mono_on (hle j) ((hintf j hj).const_mul _) (hint j hj)
        fun x hx ↦ mul_le_mul_of_nonneg_right ?_ (hf x (hsub j hj hx))
      exact hb (hmem j hj.le) (hsub j hj hx) hx.1
    · refine intervalIntegral.integral_mono_on (hle j) (hint j hj) ((hintf j hj).const_mul _)
        fun x hx ↦ mul_le_mul_of_nonneg_right ?_ (hf x (hsub j hj hx))
      exact hb (hsub j hj hx) (hmem (j + 1) hj) hx.2
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  -- split the sum into a main part and an error part
  have hsplit : ∑ j ∈ range n, b (a (j + 1)) * (g (j + 1) - g j) -
      ∑ j ∈ range n, ∫ x in a j..a (j + 1), b x * f x =
      ∑ j ∈ range n, (b (a (j + 1)) * (F (a (j + 1)) - F (a j)) -
        ∫ x in a j..a (j + 1), b x * f x) +
      ∑ j ∈ range n, b (a (j + 1)) * ((g (j + 1) - F (a (j + 1))) - (g j - F (a j))) := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hsplit]
  have hmain0 : 0 ≤ ∑ j ∈ range n, (b (a (j + 1)) * (F (a (j + 1)) - F (a j)) -
      ∫ x in a j..a (j + 1), b x * f x) :=
    sum_nonneg fun j hj ↦ sub_nonneg.2 (hpiece j (mem_range.1 hj)).2
  have hmain : ∑ j ∈ range n, (b (a (j + 1)) * (F (a (j + 1)) - F (a j)) -
      ∫ x in a j..a (j + 1), b x * f x) ≤ δ * b (a n) := by
    calc _ ≤ ∑ j ∈ range n, (b (a (j + 1)) - b (a j)) * δ := by
          refine sum_le_sum fun j hj ↦ ?_
          have hj := mem_range.1 hj
          have h1 := (hpiece j hj).1
          have h2 : (b (a (j + 1)) - b (a j)) * (F (a (j + 1)) - F (a j)) ≤
              (b (a (j + 1)) - b (a j)) * δ :=
            mul_le_mul_of_nonneg_left (hδ j hj) (sub_nonneg.2 (hβ j hj))
          linarith
      _ = (b (a n) - b (a 0)) * δ := by rw [← sum_mul, sum_range_sub (fun j ↦ b (a j))]
      _ ≤ δ * b (a n) := by nlinarith
  have herr := abs_sum_mul_sub_le (β := fun j ↦ b (a j)) (e := fun j ↦ g j - F (a j)) hβ hb0 hε
  rw [abs_le] at herr ⊢
  constructor <;> linarith

end IwaniecLinearSieve
