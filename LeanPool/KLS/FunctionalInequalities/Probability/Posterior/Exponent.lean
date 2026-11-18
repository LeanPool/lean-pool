/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Convex.Function

/-!
# The linear–quadratic exponent of the BKL posterior

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19, (67): the localization posterior of a prior `μ` with
parameters `(c, Q)` is the tilt of `μ` by the exponent `x ↦ ⟪c, x⟫ − ½⟪Q x, x⟫`. This module defines
the
exponent, records that it is affine in the parameters, bounds it polynomially, and writes a tilted
expectation as a ratio of prior integrals. Analytic inputs for the parameter response are in
`Probability/Posterior/{CompactPrior, Coercive, CompactQuadratic}.lean`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Probability.Posterior

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exponent `⟪c, x⟫ − ½⟪Q x, x⟫` of the BKL posterior (67) with parameters `(c, Q)`. -/
def quadraticExponent (c : E) (Q : E →L[ℝ] E) (x : E) : ℝ :=
  ⟪c, x⟫ - (1 / 2 : ℝ) * ⟪Q x, x⟫

/-- The exponent is affine along a parameter line: `E_{c+th, Q+tH} = E_{c,Q} + t E_{h,H}`. -/
theorem quadraticExponent_add_smul (c h : E) (Q H : E →L[ℝ] E) (t : ℝ) (x : E) :
    quadraticExponent (c + t • h) (Q + t • H) x =
      quadraticExponent c Q x + t * quadraticExponent h H x := by
  simp only [quadraticExponent, inner_add_left, real_inner_smul_left, add_apply, smul_apply]
  ring

/-- Quadratic growth bound for the exponent. -/
theorem norm_quadraticExponent_le (h : E) (H : E →L[ℝ] E) (x : E) :
    ‖quadraticExponent h H x‖ ≤ (‖h‖ + ‖H‖ / 2) * (1 + ‖x‖) ^ 2 := by
  have hquad : ‖⟪H x, x⟫‖ ≤ ‖H‖ * ‖x‖ ^ 2 := by
    calc
      ‖⟪H x, x⟫‖ ≤ ‖H x‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ (‖H‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (H.le_opNorm x) (norm_nonneg x)
      _ = ‖H‖ * ‖x‖ ^ 2 := by ring
  have h1 : ‖x‖ ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
  have h2 : ‖x‖ ^ 2 ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
  calc
    ‖quadraticExponent h H x‖ ≤ ‖⟪h, x⟫‖ + ‖(1 / 2 : ℝ) * ⟪H x, x⟫‖ := norm_sub_le _ _
    _ ≤ ‖h‖ * ‖x‖ + (1 / 2 : ℝ) * (‖H‖ * ‖x‖ ^ 2) := by
      have hhalf : ‖(1 / 2 : ℝ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [norm_mul, hhalf]
      exact add_le_add (norm_inner_le_norm h x)
        (mul_le_mul_of_nonneg_left hquad (by norm_num))
    _ ≤ ‖h‖ * (1 + ‖x‖) ^ 2 + (1 / 2 : ℝ) * (‖H‖ * (1 + ‖x‖) ^ 2) := by
      gcongr
    _ = (‖h‖ + ‖H‖ / 2) * (1 + ‖x‖) ^ 2 := by ring

open Set in
/-- The exponent `⟪c,x⟫ − ½⟪Qx,x⟫` is concave for symmetric nonnegative `Q`. -/
theorem quadraticExponent_concave (c : E) (Q : E →L[ℝ] E)
    (hSym : ∀ u v : E, ⟪Q u, v⟫ = ⟪u, Q v⟫)
    (hQ : ∀ x : E, 0 ≤ ⟪Q x, x⟫) : ConcaveOn ℝ univ (quadraticExponent c Q) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hcross : ⟪Q y, x⟫ = ⟪Q x, y⟫ := by
    rw [hSym y x, real_inner_comm]
  have hdiff : 0 ≤ ⟪Q x, x⟫ - 2 * ⟪Q x, y⟫ + ⟪Q y, y⟫ := by
    have h := hQ (x - y)
    simp only [map_sub, inner_sub_left, inner_sub_right] at h
    rw [hcross] at h
    linarith
  have he : quadraticExponent c Q (a • x + b • y) -
      (a * quadraticExponent c Q x + b * quadraticExponent c Q y) =
      (a * b / 2) * (⟪Q x, x⟫ - 2 * ⟪Q x, y⟫ + ⟪Q y, y⟫) := by
    obtain rfl : b = 1 - a := by linarith
    simp only [quadraticExponent, map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, inner_smul_right]
    rw [hcross]
    ring
  have hh := mul_nonneg (div_nonneg (mul_nonneg ha hb) (by norm_num : (0 : ℝ) ≤ 2)) hdiff
  simp only [smul_eq_mul]
  linarith

/-- A tilted expectation as the ratio of prior integrals. -/
theorem integral_tilted_eq_div {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    (φ f : Ω → ℝ) :
    (∫ x, f x ∂((μ : Measure Ω).tilted φ)) =
      (∫ x, Real.exp (φ x) * f x ∂(μ : Measure Ω)) / ∫ x, Real.exp (φ x) ∂(μ : Measure Ω) := by
  rw [integral_tilted]
  simp only [smul_eq_mul, div_mul_eq_mul_div]
  exact integral_div _ _

end FunctionalInequalities.Probability.Posterior
