/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiate Integral Mul Test Function

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Topology Filter

noncomputable section

namespace CIV

/-- Differentiation under the integral sign for a `τ`-parametrised field paired against a fixed
function `ψ` (a smooth compactly-supported test function in the intended use, though nothing here
needs that) — the step that turns a pointwise-in-`τ` derivative bound coming from the zoom PDE
into an actual derivative of the paired integral `∫ y, Θ (y, τ) ψ y`, which the two-point Lipschitz
bound of `CIV.abs_sub_le_of_hasDerivWithinAt_le_abs` then turns into the shape "the time-pairing
estimate `hpair`" needs. -/
theorem hasDerivAt_integral_mul_testfunction_of_dominated
    {Θ D : ℝ × ℝ → ℝ → ℝ} {ψ bound : ℝ × ℝ → ℝ} {s : Set ℝ} {τ₀ : ℝ}
    (hs : s ∈ 𝓝 τ₀)
    (hF_meas : ∀ᶠ τ in 𝓝 τ₀, AEStronglyMeasurable (fun y => Θ y τ * ψ y) volume)
    (hF_int : Integrable (fun y => Θ y τ₀ * ψ y) volume)
    (hF'_meas : AEStronglyMeasurable (fun y => D y τ₀ * ψ y) volume)
    (h_bound : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), ∀ τ ∈ s, |D y τ * ψ y| ≤ bound y)
    (h_bound_int : Integrable bound volume)
    (h_diff : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), ∀ τ ∈ s,
      HasDerivAt (fun τ' => Θ y τ' * ψ y) (D y τ * ψ y) τ) :
    Integrable (fun y => D y τ₀ * ψ y) volume ∧
      HasDerivAt (fun τ => ∫ y, Θ y τ * ψ y) (∫ y, D y τ₀ * ψ y) τ₀ := by
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
    h_bound_int h_diff

/-- Specialisation of `hasDerivAt_integral_mul_testfunction_of_dominated` to the case where the
neighbourhood `s` is all of `ℝ`. -/
theorem hasDerivAt_integral_mul_testfunction_of_dominated_univ
    {Θ D : ℝ × ℝ → ℝ → ℝ} {ψ bound : ℝ × ℝ → ℝ} {τ₀ : ℝ}
    (hF_meas : ∀ᶠ τ in 𝓝 τ₀, AEStronglyMeasurable (fun y => Θ y τ * ψ y) volume)
    (hF_int : Integrable (fun y => Θ y τ₀ * ψ y) volume)
    (hF'_meas : AEStronglyMeasurable (fun y => D y τ₀ * ψ y) volume)
    (h_bound : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), ∀ τ : ℝ, |D y τ * ψ y| ≤ bound y)
    (h_bound_int : Integrable bound volume)
    (h_diff : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), ∀ τ : ℝ,
      HasDerivAt (fun τ' => Θ y τ' * ψ y) (D y τ * ψ y) τ) :
    Integrable (fun y => D y τ₀ * ψ y) volume ∧
      HasDerivAt (fun τ => ∫ y, Θ y τ * ψ y) (∫ y, D y τ₀ * ψ y) τ₀ := by
  exact hasDerivAt_integral_mul_testfunction_of_dominated Filter.univ_mem hF_meas hF_int
    hF'_meas (h_bound.mono fun _y hy τ' _ => hy τ') h_bound_int
    (h_diff.mono fun _y hy τ' _ => hy τ')

/-- If `|x| ≤ M` and `|y| ≤ N` with `M, N ≥ 0`, then `|x * y| ≤ M * N`. -/
theorem abs_mul_le_of_abs_le_of_abs_le {x y M N : ℝ} (hx : |x| ≤ M) (hy : |y| ≤ N)
    (hM : 0 ≤ M) : |x * y| ≤ M * N := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) hM

end CIV
