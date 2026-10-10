/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Iteration.Parameters

/-!
Uniform positive derivative and angle-width bounds for all stages of the iteration.
-/

@[expose] public section
noncomputable section
open scoped NNReal
namespace KamProject.Arnold1963.Iteration

/-- The lower frequency-derivative bound after the accumulated multiplicative losses. -/
def lower (θ₀ δ₁ : ℝ≥0) (s : ℕ) : ℝ≥0 :=
  θ₀ * ∏ j ∈ Finset.range s, (1 - delta δ₁ j)
/-- The upper frequency-derivative bound after the accumulated multiplicative growth. -/
def upper (Θ₀ δ₁ : ℝ≥0) (s : ℕ) : ℝ≥0 :=
  Θ₀ * ∏ j ∈ Finset.range s, (1 + delta δ₁ j)
/-- The remaining angle-strip width after all preceding strip losses. -/
def width (n : ℕ) (ρ₀ δ₁ : ℝ≥0) (s : ℕ) : ℝ≥0 :=
  ρ₀ - 3 * ∑ j ∈ Finset.range s, gamma n δ₁ j

@[simp] theorem lower_zero (θ₀ δ₁ : ℝ≥0) : lower θ₀ δ₁ 0 = θ₀ := by simp [lower]
@[simp] theorem upper_zero (Θ₀ δ₁ : ℝ≥0) : upper Θ₀ δ₁ 0 = Θ₀ := by simp [upper]
@[simp] theorem width_zero (n : ℕ) (ρ₀ δ₁ : ℝ≥0) : width n ρ₀ δ₁ 0 = ρ₀ := by
  simp [width]

theorem lower_succ (θ₀ δ₁ : ℝ≥0) (s : ℕ) :
    lower θ₀ δ₁ (s + 1) = lower θ₀ δ₁ s * (1 - delta δ₁ s) := by
  simp [lower, Finset.prod_range_succ, mul_assoc]

theorem upper_succ (Θ₀ δ₁ : ℝ≥0) (s : ℕ) :
    upper Θ₀ δ₁ (s + 1) = upper Θ₀ δ₁ s * (1 + delta δ₁ s) := by
  simp [upper, Finset.prod_range_succ, mul_assoc]

theorem width_succ (n : ℕ) (ρ₀ δ₁ : ℝ≥0) (s : ℕ) :
    width n ρ₀ δ₁ (s + 1) = width n ρ₀ δ₁ s - 3 * gamma n δ₁ s := by
  simp [width, Finset.sum_range_succ, mul_add, tsub_add_eq_tsub_tsub]

private theorem prod_one_sub_lower (u : ℕ → ℝ) (hu : ∀ j, 0 ≤ u j)
    (hu1 : ∀ j, u j ≤ 1) (s : ℕ) :
    1 - ∑ j ∈ Finset.range s, u j ≤ ∏ j ∈ Finset.range s, (1 - u j) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hm := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr (hu1 s))
    have hp := mul_nonneg (Finset.sum_nonneg (fun j _ => hu j) :
      0 ≤ ∑ j ∈ Finset.range s, u j) (hu s)
    nlinarith

theorem lower_gt_half {θ₀ δ₁ : ℝ≥0} (hθ : 0 < θ₀) (hδ : δ₁ < 1 / 4) (s : ℕ) :
    (θ₀ : ℝ) / 2 < (lower θ₀ δ₁ s : ℝ) := by
  have hδ1 : δ₁ ≤ 1 := hδ.le.trans (by
    exact_mod_cast (show (1 / 4 : ℝ) ≤ 1 by norm_num))
  have hd (j : ℕ) : delta δ₁ j ≤ 1 := (decay_le hδ1 j).trans hδ1
  have he : (lower θ₀ δ₁ s : ℝ) =
      (θ₀ : ℝ) * ∏ j ∈ Finset.range s, (1 - (delta δ₁ j : ℝ)) := by
    simp only [lower, NNReal.coe_mul, NNReal.coe_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    exact NNReal.coe_sub (hd j)
  rw [he]
  have hs := decay_sum_le hδ.le s
  have hp := prod_one_sub_lower (fun j => (delta δ₁ j : ℝ))
    (fun j => (delta δ₁ j).coe_nonneg) (fun j => hd j) s
  have hδ' : (δ₁ : ℝ) < 1 / 4 := hδ
  have hθ' : (0 : ℝ) < θ₀ := hθ
  have : (1 / 2 : ℝ) < ∏ j ∈ Finset.range s, (1 - (delta δ₁ j : ℝ)) := by
    change (∑ j ∈ Finset.range s, (delta δ₁ j : ℝ)) ≤ 2 * (δ₁ : ℝ) at hs
    linarith
  nlinarith

theorem upper_lt_twice {Θ₀ δ₁ : ℝ≥0} (hΘ : 0 < Θ₀) (hδ : δ₁ < 1 / 4) (s : ℕ) :
    (upper Θ₀ δ₁ s : ℝ) < 2 * (Θ₀ : ℝ) := by
  have hs := decay_sum_le hδ.le s
  have hδ' : (δ₁ : ℝ) < 1 / 4 := hδ
  have hs' : (∑ j ∈ Finset.range s, (delta δ₁ j : ℝ)) < 1 / 2 := by
    change (∑ j ∈ Finset.range s, (delta δ₁ j : ℝ)) ≤ 2 * (δ₁ : ℝ) at hs
    linarith
  have he : Real.exp (1 / 2) < 2 :=
    (Real.exp_lt_two_add_div_two_sub (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num)).trans (by norm_num)
  have hp := (Real.prod_one_add_le_exp_sum (Finset.range s)
    (fun j => (delta δ₁ j).coe_nonneg)).trans_lt ((Real.exp_lt_exp.mpr hs').trans he)
  simp only [upper, NNReal.coe_mul, NNReal.coe_prod, NNReal.coe_add, NNReal.coe_one]
  have hΘ' : (0 : ℝ) < Θ₀ := hΘ
  nlinarith

theorem width_gt_two_fifths {n : ℕ} {ρ₀ δ₁ : ℝ≥0}
    (hγ : gamma n δ₁ 0 ≤ 1 / 4) (hρ : (gamma n δ₁ 0 : ℝ) < (ρ₀ : ℝ) / 10) (s : ℕ) :
    2 * (ρ₀ : ℝ) / 5 < (width n ρ₀ δ₁ s : ℝ) := by
  have hs : (∑ j ∈ Finset.range s, (gamma n δ₁ j : ℝ)) ≤
      2 * (gamma n δ₁ 0 : ℝ) := by
    simpa only [gamma, decay_zero] using decay_sum_le (by
      simpa only [gamma, decay_zero] using hγ) s
  have hρ0 := ρ₀.coe_nonneg
  have hb : 3 * (∑ j ∈ Finset.range s, gamma n δ₁ j) ≤ ρ₀ := by
    have : 3 * (∑ j ∈ Finset.range s, (gamma n δ₁ j : ℝ)) ≤ (ρ₀ : ℝ) := by linarith
    exact_mod_cast this
  simp only [width, NNReal.coe_sub hb, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_sum]
  linarith

theorem uniform_bounds_of_threshold {n : ℕ} (hn : 0 < n)
    {θ₀ Θ₀ ρ₀ δ₁ : ℝ≥0} {κ D : ℝ} (hθ : 0 < θ₀) (hΘ : 0 < Θ₀)
    (hδ : (δ₁ : ℝ) < threshold5 n θ₀ Θ₀ ρ₀ κ D) (s : ℕ) :
    (θ₀ : ℝ) / 2 < (lower θ₀ δ₁ s : ℝ) ∧
      (upper Θ₀ δ₁ s : ℝ) < 2 * (Θ₀ : ℝ) ∧
      2 * (ρ₀ : ℝ) / 5 < (width n ρ₀ δ₁ s : ℝ) ∧
      3 * (gamma n δ₁ s : ℝ) < (width n ρ₀ δ₁ s : ℝ) := by
  have hd := delta_initial_lt_quarter hδ
  obtain ⟨hγρ, hγ4⟩ := gamma_initial_bounds hn (threshold5_bounds hδ).2.1
  have hγ4' : gamma n δ₁ 0 ≤ 1 / 4 := by exact_mod_cast hγ4.le
  have hw := width_gt_two_fifths hγ4' hγρ s
  have hγ1 : δ₁ ^ (1 / (4 * (n : ℝ))) ≤ 1 := by
    have : (gamma n δ₁ 0 : ℝ) ≤ 1 := by linarith
    simp only [gamma, decay_zero] at this
    exact_mod_cast this
  have hg : (gamma n δ₁ s : ℝ) ≤ (gamma n δ₁ 0 : ℝ) := by
    simp only [gamma, decay_zero]
    exact_mod_cast decay_le hγ1 s
  refine ⟨lower_gt_half hθ hd s, upper_lt_twice hΘ hd s, hw, ?_⟩
  have := ρ₀.coe_nonneg
  linarith

end KamProject.Arnold1963.Iteration
