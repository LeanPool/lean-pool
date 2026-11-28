/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Jumps.JumpDiffusionProcess
public import Mathlib.Probability.Moments.Tilted

/-!
# The moments of a jump-diffusion log-return

For a jump law whose moment-generating function is finite near `0`, the cumulant generating
function of the log-return `Y` over `τ` is `κ(θ)τ` near `0`
(`cgf_id_jumpDiffusionIncrementLaw_eventuallyEq`), with `κ` the Laplace exponent. Its first two
derivatives at `0` are the first two cumulants per unit time, `κ'(0) = b + Λ𝔼[J]`
(`deriv_jumpDiffusionExponent_zero`) and `κ''(0) = σ² + Λ𝔼[J²]`
(`iteratedDeriv_two_jumpDiffusionExponent_zero`). So:

* `integral_id_jumpDiffusionIncrementLaw`: `𝔼[Y] = (b + Λ𝔼[J])τ` (Mathlib's `deriv_cgf_zero`), the
  jump-diffusion form of Mathlib's `integral_id_gaussianReal`;
* `variance_id_jumpDiffusionIncrementLaw`: `Var[Y] = (σ² + Λ𝔼[J²])τ` (Mathlib's
  `variance_tilted_mul` at `0`), the jump-diffusion form of `variance_id_gaussianReal`;
* `integral_sq_jumpDiffusionIncrementLaw`: `𝔼[Y²] = (σ² + Λ𝔼[J²])τ + ((b + Λ𝔼[J])τ)²`, the variance
  plus the squared mean (Mathlib's `variance_eq_sub`).

The hypothesis on the moment-generating function is the one the cumulant generating function
needs. The mean itself needs only `𝔼|J| < ∞` and the variance `𝔼[J²] < ∞`; those weaker forms are
not formalized.

## Main results

* `deriv_jumpDiffusionExponent_zero`: `κ'(0) = b + Λ𝔼[J]` for a jump law with exponential moments
  near `0`.
* `iteratedDeriv_two_jumpDiffusionExponent_zero`: `κ''(0) = σ² + Λ𝔼[J²]` under the same condition.
* `integral_id_jumpDiffusionIncrementLaw`: the mean of the log-return over `τ` is
  `(b + Λ𝔼[J])τ`.
* `variance_id_jumpDiffusionIncrementLaw`: the variance of the log-return is `(σ² + Λ𝔼[J²])τ`.
* `integral_sq_jumpDiffusionIncrementLaw`: the second moment is the variance plus the squared mean,
  `(σ² + Λ𝔼[J²])τ + ((b + Λ𝔼[J])τ)²`.

## References

* [Cont and Tankov, *Financial Modelling with Jump Processes*][ContTankov2004]

## Tags

cumulants, cumulant generating function, log-return moments, mean and variance, Laplace exponent,
jump-diffusion, MSC 60G51, MSC 60E10, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped NNReal

/-- **The first cumulant per unit time**: `κ'(0) = b + Λ𝔼[J]` for a jump law with exponential
moments near `0` (`hasDerivAt_jumpDiffusionExponent`, Mathlib's `deriv_mgf_zero`). -/
lemma deriv_jumpDiffusionExponent_zero (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    (hν : 0 ∈ interior (integrableExpSet id ν)) :
    deriv (jumpDiffusionExponent b σ Λ ν) 0 = b + Λ * ∫ x, x ∂ν := by
  rw [(hasDerivAt_jumpDiffusionExponent b σ Λ hν).deriv, deriv_mgf_zero hν]
  simp

/-- **The second cumulant per unit time**: `κ''(0) = σ² + Λ𝔼[J²]` for a jump law with exponential
moments near `0`. Near `0`, `κ' = b + σ²θ + ΛM'` (`hasDerivAt_jumpDiffusionExponent`), and
`M''(0) = 𝔼[J²]` (Mathlib's `hasDerivAt_iteratedDeriv_mgf`). -/
lemma iteratedDeriv_two_jumpDiffusionExponent_zero (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    (hν : 0 ∈ interior (integrableExpSet id ν)) :
    iteratedDeriv 2 (jumpDiffusionExponent b σ Λ ν) 0 = σ ^ 2 + Λ * ∫ x, x ^ 2 ∂ν := by
  have h2 := hasDerivAt_iteratedDeriv_mgf hν 1
  rw [iteratedDeriv_one] at h2
  have hd : deriv (jumpDiffusionExponent b σ Λ ν) =ᶠ[𝓝 0]
      fun θ ↦ b + σ ^ 2 * θ + Λ * deriv (mgf id ν) θ :=
    eventuallyEq_of_mem (isOpen_interior.mem_nhds hν) fun θ hθ ↦
      (hasDerivAt_jumpDiffusionExponent b σ Λ hθ).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq,
    ((((hasDerivAt_id' (0 : ℝ)).const_mul (σ ^ 2)).const_add b).fun_add
      (h2.const_mul (Λ : ℝ))).deriv]
  simp

/-- **The mean of the jump-diffusion log-return**: `𝔼[Y] = (b + Λ𝔼[J])τ` for a jump law with
exponential moments near `0`: the derivative at `0` of the cumulant generating function `κ(θ)τ`
(Mathlib's `deriv_cgf_zero`), with `κ'(0) = b + Λ𝔼[J]` (`deriv_jumpDiffusionExponent_zero`).
Without jumps it is `bτ`, the mean of `N(bτ, σ²τ)` (Mathlib's `integral_id_gaussianReal`). -/
theorem integral_id_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν)) (τ : ℝ≥0) :
    ∫ y, y ∂(jumpDiffusionIncrementLaw b σ Λ ν τ) = (b + Λ * ∫ x, x ∂ν) * τ := by
  have h := deriv_cgf_zero
    (zero_mem_interior_integrableExpSet_jumpDiffusionIncrementLaw b σ Λ hν τ)
  rw [(cgf_id_jumpDiffusionIncrementLaw_eventuallyEq b σ Λ hν τ).deriv_eq, deriv_mul_const_field,
    deriv_jumpDiffusionExponent_zero b σ Λ hν] at h
  simpa using h.symm

/-- **The variance of the jump-diffusion log-return**: `Var[Y] = (σ² + Λ𝔼[J²])τ` for a jump law
with exponential moments near `0`. Mathlib's `variance_tilted_mul` at `0` makes it the second
derivative at `0` of the cumulant generating function `κ(θ)τ`, and
`κ''(0) = σ² + Λ𝔼[J²]` (`iteratedDeriv_two_jumpDiffusionExponent_zero`). The Gaussian part
contributes `σ²τ`, the variance of `N(bτ, σ²τ)` (Mathlib's `variance_id_gaussianReal`), and the
jumps `Λ𝔼[J²]τ`. -/
theorem variance_id_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν)) (τ : ℝ≥0) :
    Var[id; jumpDiffusionIncrementLaw b σ Λ ν τ] = (σ ^ 2 + Λ * ∫ x, x ^ 2 ∂ν) * τ := by
  have h := variance_tilted_mul
    (zero_mem_interior_integrableExpSet_jumpDiffusionIncrementLaw b σ Λ hν τ)
  rw [(cgf_id_jumpDiffusionIncrementLaw_eventuallyEq b σ Λ hν τ).iteratedDeriv_eq 2,
    iteratedDeriv_mul_const_field, iteratedDeriv_two_jumpDiffusionExponent_zero b σ Λ hν] at h
  simpa using h

/-- **The second moment of the jump-diffusion log-return**:
`𝔼[Y²] = (σ² + Λ𝔼[J²])τ + ((b + Λ𝔼[J])τ)²`, the variance plus the squared mean (Mathlib's
`variance_eq_sub`; the log-return has moments of every order,
`memLp_of_mem_interior_integrableExpSet`). -/
theorem integral_sq_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν)) (τ : ℝ≥0) :
    ∫ y, y ^ 2 ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)
      = (σ ^ 2 + Λ * ∫ x, x ^ 2 ∂ν) * τ + ((b + Λ * ∫ x, x ∂ν) * τ) ^ 2 := by
  have h := variance_eq_sub (memLp_of_mem_interior_integrableExpSet
    (zero_mem_interior_integrableExpSet_jumpDiffusionIncrementLaw b σ Λ hν τ) 2)
  rw [variance_id_jumpDiffusionIncrementLaw b σ Λ hν τ] at h
  simp only [Pi.pow_apply, id_eq] at h
  rw [← integral_id_jumpDiffusionIncrementLaw b σ Λ hν τ]
  linarith

end MathFin
