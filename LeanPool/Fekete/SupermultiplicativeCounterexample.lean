/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.Fekete.Superadditive

/-!
# Positivity is needed in Fekete's lemma for supermultiplicative sequences

`u n = if Even n then 1 else 0` is nonnegative and supermultiplicative, but `u n ^ (1 / n)` does
not converge. So `Supermultiplicative.tendsto_lim` cannot assume only `0 ≤ u n`: zeros of a
supermultiplicative sequence do not propagate, unlike those of a submultiplicative one.

## Main statements

* `Supermultiplicative.exists_nonneg_not_tendsto_rpow_inv`: the counterexample.
-/

@[expose] public section

open Filter Topology

namespace Supermultiplicative

/-- The indicator of the even numbers. -/
private noncomputable def evenIndicator (n : ℕ) : ℝ := if Even n then 1 else 0

private theorem evenIndicator_nonneg (n : ℕ) : 0 ≤ evenIndicator n := by
  unfold evenIndicator
  split_ifs <;> norm_num

private theorem supermultiplicative_evenIndicator : Supermultiplicative evenIndicator :=
  fun m n ↦ by
    unfold evenIndicator
    by_cases hm : Even m
    · by_cases hn : Even n
      · simp [hm, hn, hm.add hn]
      · simp only [hn, ↓reduceIte, mul_zero]
        split_ifs <;> norm_num
    · simp only [hm, ↓reduceIte, zero_mul]
      split_ifs <;> norm_num

private theorem not_tendsto_evenIndicator :
    ¬ ∃ L, Tendsto (fun n : ℕ ↦ evenIndicator n ^ (n : ℝ)⁻¹) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have h2 : Tendsto (fun k : ℕ ↦ 2 * k) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_mul_of_pos_left k two_pos) tendsto_id
  have h₀ := hL.comp h2
  have h₁ := hL.comp ((tendsto_add_atTop_nat 1).comp h2)
  have e₀ : ((fun n : ℕ ↦ evenIndicator n ^ (n : ℝ)⁻¹) ∘ fun k ↦ 2 * k) = fun _ ↦ 1 := by
    funext k
    simp [evenIndicator]
  have e₁ : ((fun n : ℕ ↦ evenIndicator n ^ (n : ℝ)⁻¹) ∘ (fun k ↦ k + 1) ∘ fun k ↦ 2 * k) =
      fun _ ↦ 0 := by
    funext k
    have hk : ((2 * k + 1 : ℕ) : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
    simp only [Function.comp_apply, evenIndicator, Nat.not_even_two_mul_add_one, ↓reduceIte]
    exact Real.zero_rpow hk
  rw [e₀] at h₀
  rw [e₁] at h₁
  exact one_ne_zero ((tendsto_nhds_unique tendsto_const_nhds h₀).trans
    (tendsto_nhds_unique tendsto_const_nhds h₁).symm)

/-- **Positivity is needed in `Supermultiplicative.tendsto_lim`.** Some nonnegative
supermultiplicative sequence `u` has no limit of `u n ^ (1 / n)`. -/
theorem exists_nonneg_not_tendsto_rpow_inv :
    ∃ u : ℕ → ℝ, (∀ n, 0 ≤ u n) ∧ Supermultiplicative u ∧
      ¬ ∃ L, Tendsto (fun n : ℕ ↦ u n ^ (n : ℝ)⁻¹) atTop (𝓝 L) :=
  ⟨evenIndicator, evenIndicator_nonneg, supermultiplicative_evenIndicator,
    not_tendsto_evenIndicator⟩

end Supermultiplicative
