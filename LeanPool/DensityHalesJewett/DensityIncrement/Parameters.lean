/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

/-!
# Numerical parameters of the density increment

The thresholds `θ`, `η` and `γ` for `k` letters and density `δ`, and their monotonicity and
positivity. They also depend on a number `N`: the proof applies density Hales--Jewett over `k`
letters at density `δ / 4` in dimension `N + 1`.
-/

@[expose] public section

namespace DensityHalesJewett

namespace Parameters

/-- The denominator of `θ`, the number of lines in dimension `N + 1` over `k` letters, is
positive. -/
lemma θ_denominator_pos (k N : ℕ) : 0 < (k + 1) ^ (N + 1) - k ^ (N + 1) :=
  Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (lt_add_one k) N.succ_ne_zero)

/-- The correlated-fibers threshold for `k` letters and density `δ`. -/
noncomputable def θ (k N : ℕ) (δ : ℝ) : ℝ :=
  δ / 4 / ((k + 1) ^ (N + 1) - k ^ (N + 1) : ℕ)

/-- The threshold is monotone in the density. -/
lemma θ_mono (k N : ℕ) {δ ρ : ℝ} (hδρ : δ ≤ ρ) : θ k N δ ≤ θ k N ρ := by
  unfold θ
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

lemma θ_pos (k N : ℕ) {δ : ℝ} (hδ : 0 < δ) : 0 < θ k N δ := by
  unfold θ
  exact div_pos (by positivity) (Nat.cast_pos.2 (θ_denominator_pos k N))

/-- The error tolerance for `k` letters and density `δ`. -/
noncomputable def η (k N : ℕ) (δ : ℝ) : ℝ :=
  min (δ * θ k N δ / 48) (min (θ k N δ / 4) (δ / 6))

/-- The error tolerance is monotone in the density. -/
lemma η_mono (k N : ℕ) {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) : η k N δ ≤ η k N ρ := by
  unfold η
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · apply div_le_div_of_nonneg_right
    · exact mul_le_mul hδρ (θ_mono k N hδρ) (θ_pos k N hδ).le (hδ.trans_le hδρ).le
    · norm_num
  · exact div_le_div_of_nonneg_right (θ_mono k N hδρ) (by norm_num)
  · exact div_le_div_of_nonneg_right hδρ (by norm_num)

lemma η_pos (k N : ℕ) {δ : ℝ} (hδ : 0 < δ) : 0 < η k N δ := by
  unfold η
  apply lt_min
  · positivity [θ_pos k N hδ]
  · apply lt_min
    · positivity [θ_pos k N hδ]
    · positivity

/-- The density increment for `k` letters and density `δ`. -/
noncomputable def γ (k N : ℕ) (δ : ℝ) : ℝ :=
  min (δ * η k N δ ^ 2 / k) (min (η k N δ ^ 2 / 2) (3 * η k N δ))

/-- The increment is monotone in the density. -/
lemma γ_mono (k N : ℕ) {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) : γ k N δ ≤ γ k N ρ := by
  have hη := η_mono k N hδ hδρ
  have hηsq : η k N δ ^ 2 ≤ η k N ρ ^ 2 := pow_le_pow_left₀ (η_pos k N hδ).le hη 2
  unfold γ
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · apply div_le_div_of_nonneg_right
    · exact mul_le_mul hδρ hηsq (by positivity) (hδ.trans_le hδρ).le
    · positivity
  · exact div_le_div_of_nonneg_right hηsq (by norm_num)
  · exact mul_le_mul_of_nonneg_left hη (by norm_num)

lemma γ_pos {k : ℕ} (hk : 2 ≤ k) (N : ℕ) {δ : ℝ} (hδ : 0 < δ) : 0 < γ k N δ := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  unfold γ
  positivity [η_pos k N hδ]

lemma η_lt_θ_div_two (k N : ℕ) {δ : ℝ} (hδ : 0 < δ) : η k N δ < θ k N δ / 2 := by
  unfold η
  apply lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
  linarith [θ_pos k N hδ]

lemma η_le_δ_div_six (k N : ℕ) (δ : ℝ) : η k N δ ≤ δ / 6 := by
  unfold η
  exact (min_le_right _ _).trans (min_le_right _ _)

lemma γ_le_η_sq_div_two (k N : ℕ) (δ : ℝ) : γ k N δ ≤ η k N δ ^ 2 / 2 := by
  unfold γ
  exact (min_le_right _ _).trans (min_le_left _ _)

lemma γ_le_three_mul_η (k N : ℕ) (δ : ℝ) : γ k N δ ≤ 3 * η k N δ := by
  unfold γ
  exact (min_le_right _ _).trans (min_le_right _ _)

/-- The correlated-fiber threshold is at most one in the admissible parameter range. -/
lemma θ_le_one (k N : ℕ) {δ : ℝ} (hδ₁ : δ ≤ 1) : θ k N δ ≤ 1 := by
  unfold θ
  rw [div_le_one (Nat.cast_pos.2 (θ_denominator_pos k N))]
  exact (by linarith : δ / 4 ≤ 1).trans (Nat.one_le_cast.2 (θ_denominator_pos k N))

/-- The numerical parameters turn the absolute density left outside a large intersection into
the required relative density gain. -/
lemma mul_one_sub_θ_div_four_le (k N : ℕ) {δ : ℝ} (hδ₀ : 0 < δ) :
    (δ + 6 * η k N δ) * (1 - θ k N δ / 4) ≤ δ - 3 * η k N δ := by
  have hη : η k N δ ≤ δ * θ k N δ / 48 :=
    min_le_left (δ * θ k N δ / 48) (min (θ k N δ / 4) (δ / 6))
  nlinarith [hη, θ_pos k N hδ₀, η_pos k N hδ₀,
    mul_nonneg hδ₀.le (θ_pos k N hδ₀).le,
    mul_nonneg (η_pos k N hδ₀).le (θ_pos k N hδ₀).le]

/-- On a set of density at least `δ / 2`, the gain `6 * η` absorbs `k` increments `γ`. -/
lemma add_γ_mul_add_mul_γ_le {k : ℕ} (hk : 0 < k) (N : ℕ) {δ c : ℝ} (hδ₀ : 0 < δ)
    (hδ₁ : δ ≤ 1) (hc : δ / 2 ≤ c) :
    (δ + γ k N δ) * c + k * γ k N δ ≤ (δ + 6 * η k N δ) * c := by
  have hγ : k * γ k N δ ≤ δ * η k N δ ^ 2 :=
    (le_div_iff₀' (by positivity)).1 (min_le_left _ _)
  have hη := η_le_δ_div_six k N δ
  nlinarith [mul_nonneg (sub_nonneg.2 (γ_le_three_mul_η k N δ)) (by linarith : 0 ≤ c),
    mul_le_mul_of_nonneg_left hc (η_pos k N hδ₀).le,
    mul_le_mul_of_nonneg_left (hη.trans (by linarith) : η k N δ ≤ 1 / 6)
      (mul_pos hδ₀ (η_pos k N hδ₀)).le]

end Parameters

end DensityHalesJewett
