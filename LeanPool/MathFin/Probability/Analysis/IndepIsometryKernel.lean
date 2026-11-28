/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.Independence.Integration

/-!
# The isometry kernel: a past-measurable coefficient against an independent increment

The Itô isometry for the Brownian integral and for the compensated-Poisson integral is a sum of
the same three one-term facts, each about a coefficient `φ` (measurable for the past) and a fresh
increment `X` (a Brownian increment, a compensated Poisson count) independent of it:

* the coefficient pairs to zero against a centred increment, `𝔼[φ·X] = 0`
  (`IndepFun.integral_mul_eq_zero`), which makes the integral a martingale;
* the diagonal energy `𝔼[χ·X²] = 𝔼[χ]·𝔼[X²]` (`IndepFun.integral_mul_sq`), with `χ = φ²`;
* `L²`-membership of the product `φ·X` (`IndepFun.memLp_two_mul`).

Nothing here knows where the independence comes from: the Brownian kernel
(`ItoIsometryAdapted`) supplies it from `IsFilteredPreBrownian.indep`, the Poisson kernel
(`PoissonCompensatedIsometryAdapted`) from `indep_of_disjoint_region`, and both then read the
one-term facts off these three lemmas.

## Main results

* `IndepFun.integral_mul_comp`: if `φ` is independent of `X`, then `𝔼[φ·g(X)] = 𝔼[φ]·𝔼[g(X)]`
  for measurable `g`.
* `IndepFun.integral_mul_eq_zero`: if `φ` is independent of a centred `X`, then `𝔼[φ·X] = 0`.
* `IndepFun.integral_mul_sq`: if `φ` is independent of `X`, then `𝔼[φ·X²] = 𝔼[φ]·𝔼[X²]`.
* `IndepFun.memLp_two_mul`: the product of an independent pair in `L²` is in `L²`.

## Tags

Itô isometry, independent increments, martingale difference, compensated Poisson, second moment,
orthogonality, MSC 60H05, MSC 60G51, MSC 60G55
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {φ X : Ω → ℝ}

/-- **A coefficient against a function of an independent increment factorises**:
`𝔼[φ·g(X)] = 𝔼[φ]·𝔼[g(X)]` (Mathlib's `IndepFun.integral_fun_comp_mul_comp` at `f = id`, the
form every isometry kernel uses: `g` a power of the increment, possibly shifted). -/
theorem IndepFun.integral_mul_comp (h : IndepFun φ X μ) {g : ℝ → ℝ} (hg : Measurable g)
    (hφ : AEStronglyMeasurable φ μ) (hX : AEMeasurable X μ) :
    ∫ ω, φ ω * g (X ω) ∂μ = (∫ ω, φ ω ∂μ) * ∫ ω, g (X ω) ∂μ :=
  h.integral_fun_comp_mul_comp (f := id) hφ.aemeasurable hX aestronglyMeasurable_id
    hg.aestronglyMeasurable

/-- **A coefficient independent of a centred increment pairs to zero**: `𝔼[φ·X] = 0`. -/
theorem IndepFun.integral_mul_eq_zero (h : IndepFun φ X μ) (hφ : AEStronglyMeasurable φ μ)
    (hX : AEStronglyMeasurable X μ) (h0 : ∫ ω, X ω ∂μ = 0) : ∫ ω, φ ω * X ω ∂μ = 0 := by
  rw [h.integral_fun_mul_eq_mul_integral hφ hX, h0, mul_zero]

/-- **Diagonal energy**: for `χ` independent of `X`, `𝔼[χ·X²] = 𝔼[χ]·𝔼[X²]`. With `χ = φ²` and
`𝔼[X²]` the variance of the increment, this is the diagonal term of the isometry. -/
theorem IndepFun.integral_mul_sq (h : IndepFun φ X μ) (hφ : AEStronglyMeasurable φ μ)
    (hX : AEStronglyMeasurable X μ) :
    ∫ ω, φ ω * X ω ^ 2 ∂μ = (∫ ω, φ ω ∂μ) * ∫ ω, X ω ^ 2 ∂μ :=
  h.integral_mul_comp (g := fun x : ℝ ↦ x ^ 2) (by fun_prop) hφ hX.aemeasurable

/-- **A square-integrable coefficient times an independent square-integrable increment is
square-integrable**, since `𝔼[(φ·X)²] = 𝔼[φ²]·𝔼[X²]` is finite. -/
theorem IndepFun.memLp_two_mul (h : IndepFun φ X μ) (hφ : MemLp φ 2 μ) (hX : MemLp X 2 μ) :
    MemLp (fun ω ↦ φ ω * X ω) 2 μ :=
  (memLp_two_iff_integrable_sq (hφ.aestronglyMeasurable.mul hX.aestronglyMeasurable)).2 <| by
    simpa [Pi.mul_def, Function.comp_def, mul_pow] using
      (h.comp (φ := fun x : ℝ ↦ x ^ 2) (ψ := fun x : ℝ ↦ x ^ 2) (by fun_prop)
        (by fun_prop)).integrable_mul hφ.integrable_sq hX.integrable_sq

end ProbabilityTheory
