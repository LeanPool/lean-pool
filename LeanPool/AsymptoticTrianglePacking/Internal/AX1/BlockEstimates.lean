/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Shared estimates for the two block-allocation reductions

The local and coupled constructions use the same scale, density and exceptional-budget
bounds. Keeping the arithmetic here avoids repeating their proofs in the two reductions.
-/

public section

namespace Nibble.AX1.BlockEstimates

/-- A positive density small enough for both the linear and quadratic accuracy windows. -/
theorem exists_small_density {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ δ ≤ ε / 2 ∧ δ / 2 ≤ (ε / 2) ^ 2 := by
  have h0 : 0 < min 1 ε := lt_min one_pos hε
  have h1 : min 1 ε ≤ 1 := min_le_left _ _
  have h2 : min 1 ε ≤ ε := min_le_right _ _
  refine ⟨min 1 ε * min 1 ε / 8, by positivity, ?_, ?_, ?_⟩
  · nlinarith only [h0, h1]
  · nlinarith only [h0, h1, h2]
  · nlinarith only [h0, h2]

/-- The blocks have size between `¾·τδ` and `⁵⁄₄·τ`. -/
theorem block_size_bounds {τ δ s dens : ℝ} (hτ : 0 < τ)
    (hτδ : 8 ≤ τ * δ) (h1 : δ ≤ dens) (h2 : dens ≤ 1) (habs : |s - τ * dens| ≤ 1) :
    3 / 4 * (τ * δ) ≤ s ∧ s ≤ 5 / 4 * τ := by
  rw [abs_le] at habs
  have h3 : τ * δ ≤ τ * dens := mul_le_mul_of_nonneg_left h1 hτ.le
  have h4 : τ * dens ≤ τ := mul_le_of_le_one_right hτ.le h2
  have h6 : τ * δ ≤ τ := h3.trans h4
  exact ⟨by linarith [habs.1], by linarith [habs.2]⟩

/-- The area and the support of a sub-triple, in terms of the scale. -/
theorem area_bounds {τ δ a b c : ℝ} (hτ : 0 < τ) (hτδ : 8 ≤ τ * δ)
    (ha : 3 / 4 * (τ * δ) ≤ a) (ha' : a ≤ 5 / 4 * τ)
    (hb : 3 / 4 * (τ * δ) ≤ b) (hb' : b ≤ 5 / 4 * τ)
    (hc : 3 / 4 * (τ * δ) ≤ c) (hc' : c ≤ 5 / 4 * τ) :
    0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a * b + a * c + b * c ≤ 5 * τ ^ 2 ∧
      0 ≤ a * b + a * c + b * c ∧ a + b + c ≤ 4 * τ ∧ 0 ≤ a + b + c := by
  have hbase : 0 ≤ 3 / 4 * (τ * δ) := by linarith only [hτδ]
  have ha0 : 0 ≤ a := hbase.trans ha
  have hb0 : 0 ≤ b := hbase.trans hb
  have hc0 : 0 ≤ c := hbase.trans hc
  have hab := mul_le_mul ha' hb' hb0 (by positivity : (0 : ℝ) ≤ 5 / 4 * τ)
  have hac := mul_le_mul ha' hc' hc0 (by positivity : (0 : ℝ) ≤ 5 / 4 * τ)
  have hbc := mul_le_mul hb' hc' hc0 (by positivity : (0 : ℝ) ≤ 5 / 4 * τ)
  refine ⟨ha0, hb0, hc0, ?_, by positivity, ?_, add_nonneg (add_nonneg ha0 hb0) hc0⟩
  · linarith only [hab, hac, hbc, sq_nonneg τ]
  · linarith only [ha', hb', hc', hτ]

/-- The `Elo` of a sub-triple is at least a quarter of `τ²δ³`. -/
theorem edge_count_lower_bound {τ δ ε₁ a b c dAB dAC dBC : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hε₁b : ε₁ ≤ δ / 2) (hx : δ - ε₁ / 8 ≤ dAB)
    (hAC0 : 0 ≤ dAC) (hBC0 : 0 ≤ dBC)
    (ha : 3 / 4 * (τ * δ) ≤ a) (hb : 3 / 4 * (τ * δ) ≤ b) (hc0 : 0 ≤ c) (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) :
    1 / 4 * (τ ^ 2 * δ ^ 3) ≤ dAB * a * b + dAC * a * c + dBC * b * c := by
  have hAB : 15 / 16 * δ ≤ dAB := by linarith only [hε₁b, hx]
  have hnn : (0:ℝ) ≤ 3 / 4 * (τ * δ) := by positivity
  have hab : 9 / 16 * (τ ^ 2 * δ ^ 2) ≤ a * b := by
    linarith only [mul_le_mul ha hb hnn ha0]
  have hmain : 1 / 4 * (τ ^ 2 * δ ^ 3) ≤ dAB * a * b := by
    have h1 : (15 / 16 * δ) * (9 / 16 * (τ ^ 2 * δ ^ 2)) ≤ dAB * (a * b) :=
      mul_le_mul hAB hab (by positivity) (le_trans (by positivity) hAB)
    have h2 : dAB * a * b = dAB * (a * b) := by ring
    have h3 : (15 / 16 * δ) * (9 / 16 * (τ ^ 2 * δ ^ 2)) = 135 / 256 * (τ ^ 2 * δ ^ 3) := by ring
    have h4 : (0:ℝ) ≤ τ ^ 2 * δ ^ 3 := by positivity
    rw [h2]
    rw [h3] at h1
    linarith only [h1, h4]
  have h2 : 0 ≤ dAC * a * c := by positivity
  have h3 : 0 ≤ dBC * b * c := by positivity
  linarith only [hmain, h2, h3]

/-- The product of three densities at least `δ` is at least `δ³`. -/
theorem density_product_lower_bound {δ x y z : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) (hy : δ ≤ y)
    (hz : δ ≤ z) :
    δ ^ 3 ≤ x * y * z := by
  have h1 : δ * δ ≤ x * y := mul_le_mul hx hy hδ.le (by linarith)
  have h2 : (δ * δ) * δ ≤ (x * y) * z :=
    mul_le_mul h1 hz hδ.le (le_trans (by positivity : (0:ℝ) ≤ δ * δ) h1)
  linarith only [h2]

/-- The triangle-degree scale of a sub-triple is above the floor `d₀`. -/
theorem degree_scale_lower_bound {τ δ d₀ x y z : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hx : δ ≤ x) (hy : δ ≤ y)
    (hz : δ ≤ z) (hd₀ : d₀ ≤ τ * δ ^ 3) : d₀ ≤ τ * (x * y * z) :=
  le_trans hd₀ (mul_le_mul_of_nonneg_left (density_product_lower_bound hδ hx hy hz) hτ.le)

/-- The triangle-degree scale of a sub-triple is nonnegative. -/
theorem degree_scale_nonnegative {τ δ x y z : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hx : δ ≤ x) (hy : δ ≤ y)
    (hz : δ ≤ z) : 0 ≤ τ * (x * y * z) := by
  have h := density_product_lower_bound hδ hx hy hz
  have h0 : (0:ℝ) < δ ^ 3 := by positivity
  exact mul_nonneg hτ.le (by linarith)

/-- The pruning slack `t` is at most half of `(μ - μ₂)` times the triangle-degree scale. -/
theorem slack_bound {μ μ₂ τ δ x y z : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hx : δ ≤ x) (hy : δ ≤ y) (hz : δ ≤ z) (hμ₂ : 2 * μ₂ ≤ μ) (hμ₂'₀ : 0 < μ₂) :
    2 * ((μ - μ₂) * τ * δ ^ 3 / 2) ≤ (μ - μ₂) * (τ * (x * y * z)) := by
  have h : τ * δ ^ 3 ≤ τ * (x * y * z) :=
    mul_le_mul_of_nonneg_left (density_product_lower_bound hδ hx hy hz) hτ.le
  have hd : (0:ℝ) ≤ μ - μ₂ := by linarith only [hμ₂, hμ₂'₀]
  linarith only [mul_le_mul_of_nonneg_left h hd]

/-- The pruning slack `t = (μ - μ₂)τδ³/2` is positive. -/
theorem pruning_slack_pos {μ μ₂ τ δ : ℝ} (hτ : 0 < τ) (hδ3 : 0 < δ ^ 3) (hμ₂ : 0 < μ₂)
    (h : 2 * μ₂ ≤ μ) : 0 < (μ - μ₂) * τ * δ ^ 3 / 2 := by
  exact div_pos (mul_pos (mul_pos (by linarith only [h, hμ₂]) hτ) hδ3) (by norm_num)

/-- The pruning slack `t = (μ - μ₂)τδ³/2` is at least `μ₂τδ³/2`. -/
theorem pruning_slack_lower_bound {μ μ₂ τ δ : ℝ} (hτ : 0 < τ) (hδ3 : 0 < δ ^ 3) (h : 2 * μ₂ ≤ μ) :
    μ₂ * τ * δ ^ 3 / 2 ≤ (μ - μ₂) * τ * δ ^ 3 / 2 := by
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith only [h]) hτ.le) hδ3.le

/-- One term of the covering estimate: replacing the cluster densities by the block densities and
subtracting the exceptional budget costs at most `17ε₁/24` times the area. -/
theorem cover_step {ε₁ ε₂ dAB dAC dBC eAB eAC eBC a b c : ℝ}
    (h1 : |eAB - dAB| ≤ ε₁ / 8) (h2 : |eAC - dAC| ≤ ε₁ / 8) (h3 : |eBC - dBC| ≤ ε₁ / 8)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) :
    (dAB * a * b + dAC * a * c + dBC * b * c) / 3
        - (ε₁ / 8 + 4 * ε₂) / 3 * (a * b + a * c + b * c)
      ≤ (eAB * a * b + eAC * a * c + eBC * b * c
          - 4 * ε₂ * (a * b + a * c + b * c)) / 3 := by
  have k1 : -(ε₁ / 8) ≤ eAB - dAB := by linarith only [(abs_le.mp h1).1]
  have k2 : -(ε₁ / 8) ≤ eAC - dAC := by linarith only [(abs_le.mp h2).1]
  have k3 : -(ε₁ / 8) ≤ eBC - dBC := by linarith only [(abs_le.mp h3).1]
  have hab : (0:ℝ) ≤ a * b := mul_nonneg ha0 hb0
  have hac : (0:ℝ) ≤ a * c := mul_nonneg ha0 hc0
  have hbc : (0:ℝ) ≤ b * c := mul_nonneg hb0 hc0
  have m1 : -(ε₁ / 8) * (a * b) ≤ (eAB - dAB) * (a * b) :=
    mul_le_mul_of_nonneg_right k1 hab
  have m2 : -(ε₁ / 8) * (a * c) ≤ (eAC - dAC) * (a * c) :=
    mul_le_mul_of_nonneg_right k2 hac
  have m3 : -(ε₁ / 8) * (b * c) ≤ (eBC - dBC) * (b * c) :=
    mul_le_mul_of_nonneg_right k3 hbc
  linarith only [m1, m2, m3]

/-- The accumulated covering loss is absorbed by half of the accuracy. -/
theorem cover_tail {ε K N : ℝ} (h : K ≤ ε) (hN : 0 ≤ N) :
    K * (N / 2) ≤ ε / 2 * N := by
  have := mul_le_mul_of_nonneg_right h hN
  linarith only [this]

/-- The block uniformity scale `ε₂ = (ε₁/8)/α` at `α = δ/2`, bounded from a bound on `ε₁`. -/
theorem uniformity_bound {x δ B : ℝ} (hδ : 0 < δ) (h : x ≤ B * δ) : x / (4 * δ) ≤ B / 4 := by
  rw [div_le_iff₀ (by positivity)]
  linarith only [h]

/-- Multiplying a nonnegative quantity by `δ ≤ 1` only decreases it. -/
theorem mul_density_le {B δ : ℝ} (hB : 0 ≤ B) (hδ1 : δ ≤ 1) : B * δ ≤ B := by
  exact mul_le_of_le_one_right hB hδ1

/-- The block scale is large: `2 ≤ τ·μ₂δ³` and `μ₂ ≤ 1` give `2 ≤ τδ³`. -/
theorem scale_density_cube_lower_bound {τ δ μ₂ : ℝ} (hτ : 0 < τ) (hδ3 : 0 < δ ^ 3) (hμ₂1 : μ₂ ≤ 1)
    (h : 2 ≤ τ * (μ₂ * δ ^ 3)) : 2 ≤ τ * δ ^ 3 := by
  refine h.trans ?_
  calc τ * (μ₂ * δ ^ 3) = (τ * δ ^ 3) * μ₂ := by ring
    _ ≤ τ * δ ^ 3 := mul_le_of_le_one_right (mul_nonneg hτ.le hδ3.le) hμ₂1

/-- The block scale is large: `2 ≤ τδ³` and `δ ≤ 1/2` give `8 ≤ τδ`. -/
theorem scale_density_lower_bound {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (h : 2 ≤ τ * δ ^ 3) : 8 ≤ τ * δ := by
  have hsq : δ ^ 2 ≤ 1 / 4 := by nlinarith only [hδ, hδhalf]
  have hnn : 0 ≤ τ * δ := mul_nonneg hτ.le hδ.le
  nlinarith only [h, hsq, hnn]

/-- The exceptional-edge clause of the design, as an inequality between real numbers. -/
theorem exceptional_budget_bound {ε₂ δ μ₂ η τ t S sup Elo : ℝ}
    (hτ : 0 < τ) (hδ : 0 < δ) (hμ₂0 : 0 < μ₂) (hη : 0 < η)
    (hε₂0 : 0 < ε₂) (hε₂c : ε₂ ≤ η * μ₂ * δ ^ 6 / 2560) (hε₂d : ε₂ ≤ δ ^ 3 / 160)
    (hS : S ≤ 5 * τ ^ 2) (hsup : sup ≤ 4 * τ) (hsup0 : 0 ≤ sup)
    (hElo : 1 / 4 * (τ ^ 2 * δ ^ 3) ≤ Elo) (ht : μ₂ * τ * δ ^ 3 / 2 ≤ t) (ht0 : 0 < t) :
    2 * (4 * ε₂ * S) / t * sup ≤ η * (Elo - 4 * ε₂ * S) := by
  rw [div_mul_eq_mul_div, div_le_iff₀ ht0]
  have hτ3 : (0:ℝ) < τ ^ 3 := by positivity
  have h1 : 2 * (4 * ε₂ * S) * sup ≤ 160 * ε₂ * τ ^ 3 := by
    have hSs : S * sup ≤ (5 * τ ^ 2) * (4 * τ) := mul_le_mul hS hsup hsup0 (by positivity)
    linarith only [mul_le_mul_of_nonneg_left hSs (by positivity : (0 : ℝ) ≤ 8 * ε₂)]
  have hbr : 1 / 8 * (τ ^ 2 * δ ^ 3) ≤ Elo - 4 * ε₂ * S := by
    have hεS : 4 * ε₂ * S ≤ 4 * (δ ^ 3 / 160) * (5 * τ ^ 2) := by
      calc 4 * ε₂ * S ≤ 4 * ε₂ * (5 * τ ^ 2) :=
            mul_le_mul_of_nonneg_left hS (by positivity)
        _ ≤ 4 * (δ ^ 3 / 160) * (5 * τ ^ 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hε₂d (by norm_num)) (by positivity)
    linarith only [hElo, hεS]
  have h2 : η * (1 / 8 * (τ ^ 2 * δ ^ 3)) * (μ₂ * τ * δ ^ 3 / 2)
      ≤ η * (Elo - 4 * ε₂ * S) * t := by
    have hle1 : η * (1 / 8 * (τ ^ 2 * δ ^ 3)) ≤ η * (Elo - 4 * ε₂ * S) :=
      mul_le_mul_of_nonneg_left hbr hη.le
    have hnn : (0:ℝ) ≤ η * (1 / 8 * (τ ^ 2 * δ ^ 3)) := by positivity
    have hnn2 : (0:ℝ) ≤ μ₂ * τ * δ ^ 3 / 2 := by positivity
    exact mul_le_mul hle1 ht hnn2 (le_trans hnn hle1)
  have h3 : 160 * ε₂ * τ ^ 3 ≤ η * (1 / 8 * (τ ^ 2 * δ ^ 3)) * (μ₂ * τ * δ ^ 3 / 2) := by
    have hkey : 160 * ε₂ ≤ η * μ₂ * δ ^ 6 / 16 := by linarith only [hε₂c]
    linarith only [mul_le_mul_of_nonneg_right hkey hτ3.le]
  linarith only [h1, h2, h3]

end Nibble.AX1.BlockEstimates
