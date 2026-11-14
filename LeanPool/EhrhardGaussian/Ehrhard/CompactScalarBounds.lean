/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.ScalarLinearBounds
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Uniform bounds for smooth scalar functions constant outside a compact set -/

@[expose] public noncomputable section

namespace EhrhardGaussian.Ehrhard

/-- Compact support of the first derivative bounds all scalar derivatives
used by interpolation, including the drift term `y f'(y)`. -/
theorem exists_compact_scalar_derivative_bounds {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (hcompact : HasCompactSupport (deriv f)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, |deriv f y| ≤ M ∧ |deriv (deriv f) y| ≤ M ∧
      |deriv (deriv (deriv f)) y| ≤ M ∧ |y * deriv f y| ≤ M := by
  have hf₂ : ContDiff ℝ 2 (deriv f) := hf.deriv'
  have hf₁ : ContDiff ℝ 1 (deriv (deriv f)) := hf₂.deriv'
  have hf₀ : ContDiff ℝ 0 (deriv (deriv (deriv f))) := hf₁.deriv'
  obtain ⟨C₀, hC₀⟩ := hcompact.exists_bound_of_continuous hf₂.continuous
  obtain ⟨C₁, hC₁⟩ := hcompact.deriv.exists_bound_of_continuous hf₁.continuous
  obtain ⟨C₂, hC₂⟩ := hcompact.deriv.deriv.exists_bound_of_continuous hf₀.continuous
  have hweighted : HasCompactSupport (fun y : ℝ => y * deriv f y) := hcompact.mul_left
  obtain ⟨C₃, hC₃⟩ := hweighted.exists_bound_of_continuous (continuous_id.mul hf₂.continuous)
  obtain ⟨N, hN⟩ := Finite.exists_le (![C₀, C₁, C₂, C₃] : Fin 4 → ℝ)
  have h₀ : C₀ ≤ max 0 N := (show C₀ ≤ N by simpa using hN (0 : Fin 4)).trans (le_max_right _ _)
  have h₁ : C₁ ≤ max 0 N := (show C₁ ≤ N by simpa using hN (1 : Fin 4)).trans (le_max_right _ _)
  have h₂ : C₂ ≤ max 0 N := (show C₂ ≤ N by simpa using hN (2 : Fin 4)).trans (le_max_right _ _)
  have h₃ : C₃ ≤ max 0 N := (show C₃ ≤ N by simpa using hN (3 : Fin 4)).trans (le_max_right _ _)
  refine ⟨max 0 N, le_max_left _ _, ?_⟩
  intro y
  simpa only [Real.norm_eq_abs] using
    And.intro ((hC₀ y).trans h₀) (And.intro ((hC₁ y).trans h₁)
      (And.intro ((hC₂ y).trans h₂) ((hC₃ y).trans h₃)))

/-- The derivative of a differentiable function constant outside a compact set has compact support.
-/
theorem hasCompactSupport_deriv_of_sub_const {f : ℝ → ℝ} {c : ℝ}
    (hf : Differentiable ℝ f) (hcompact : HasCompactSupport (fun y => f y - c)) :
    HasCompactSupport (deriv f) := by
  have heq : deriv (fun y => f y - c) = deriv f := by
    funext y
    exact ((hf y).hasDerivAt.sub_const c).deriv
  rw [← heq]
  exact hcompact.deriv

end EhrhardGaussian.Ehrhard

end
