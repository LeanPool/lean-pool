/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.CurryingDensity
public import LeanPool.LiebThirring.Kinetic.LayerCakeBasic

/-!
# Density lower bounds for high Fourier fields

The positive part of a norm difference is bounded by the difference norm.

A quadratic low-field bound gives the corresponding square-root bound.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- The positive part of a norm difference is bounded by the difference norm. -/
theorem max_norm_sub_norm_le_norm_sub {H : Type*} [NormedAddCommGroup H] (a b : H) :
    max (‖a‖ - ‖b‖) 0 ≤ ‖a - b‖ :=
  max_le (norm_sub_norm_le a b) (norm_nonneg _)

/-- A quadratic low-field bound gives the corresponding square-root bound. -/
theorem norm_le_sqrt_mul_rpow_of_norm_sq_le {H : Type*} [NormedAddCommGroup H]
    (u : H) (C E : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hu : ‖u‖ ^ 2 ≤ C * E ^ ((3 : ℝ) / 2)) :
    ‖u‖ ≤ Real.sqrt C * E ^ ((3 : ℝ) / 4) := by
  have hs : (Real.sqrt C * E ^ ((3 : ℝ) / 4)) ^ 2 = C * E ^ ((3 : ℝ) / 2) := by
    rw [mul_pow, Real.sq_sqrt hC,
      ← Real.rpow_mul_natCast hE ((3 : ℝ) / 4) 2]
    norm_num
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hE _))).mp (hu.trans_eq hs.symm)

/-- Density finiteness and its real norm identification hold on one conull set. -/
theorem densityField_density_data_ae {N q : ℕ} (i : Fin N) (ψ : State N q)
    (hψ : antisymmetric ψ) :
    ∀ᵐ x : Position,
      density ψ x ≠ ⊤ ∧
      (density ψ x).toReal = ‖densityField i ψ x‖ ^ 2 ∧
      Real.sqrt ((density ψ x).toReal) = ‖densityField i ψ x‖ := by
  filter_upwards [density_eq_densityField_norm_sq_ae i ψ hψ] with x hx
  have hreal : (density ψ x).toReal = ‖densityField i ψ x‖ ^ 2 := by
    rw [hx, ENNReal.toReal_pow, ENNReal.coe_toReal]
    rfl
  refine ⟨?_, hreal, ?_⟩
  · rw [hx]
    exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  · rw [hreal, Real.sqrt_sq (norm_nonneg _)]

/-- the layer cake reverse triangle bound on a single density-conull set for every energy,
assembled conditionally from the exact pointwise the low-momentum bound low-field estimate. -/
theorem densityField_high_bound_ae_of_lowMomentumBound {N q : ℕ} (i : Fin N) (ψ : State N q)
    (hψ : antisymmetric ψ)
    (hLow : ∀ E : ℝ, 0 ≤ E → ∀ x : Position,
      ‖lowFourierField (densityField i ψ) E x‖ ^ 2 ≤
        (q : ℝ) * (1 / (6 * Real.pi ^ 2)) * E ^ ((3 : ℝ) / 2)) :
    ∀ᵐ x : Position, ∀ E : ℝ, 0 ≤ E →
      max (Real.sqrt ((density ψ x).toReal) -
        Real.sqrt ((q : ℝ) * (1 / (6 * Real.pi ^ 2))) * E ^ ((3 : ℝ) / 4)) 0 ≤
          ‖highFourierField (densityField i ψ) E x‖ := by
  filter_upwards [densityField_density_data_ae i ψ hψ] with x hx
  intro E hE
  have hC : 0 ≤ (q : ℝ) * (1 / (6 * Real.pi ^ 2)) := by positivity
  have hnorm := norm_le_sqrt_mul_rpow_of_norm_sq_le
    (lowFourierField (densityField i ψ) E x) _ E hC hE (hLow E hE x)
  rw [hx.2.2]
  calc
    _ ≤ max (‖densityField i ψ x‖ - ‖lowFourierField (densityField i ψ) E x‖) 0 :=
      max_le_max (sub_le_sub_left hnorm _) le_rfl
    _ ≤ ‖densityField i ψ x - lowFourierField (densityField i ψ) E x‖ :=
      max_norm_sub_norm_le_norm_sub _ _
    _ = _ := rfl

end LiebThirring
end
