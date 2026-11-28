/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.
public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralCLM
/-! # Covariation of Itô integrals: the bilinear Itô isometry

The Itô isometry `‖∫φ dB‖ = ‖φ‖` (`ItoIntegralCLM.itoIntegralCLM_norm`) says
the Itô integral preserves L²-*norms*. A linear norm-isometry between real
inner-product spaces automatically preserves the *inner product* — the
polarization identity recovers `⟪x, y⟫` from norms — so the integral preserves
L²-inner-products too: `⟪∫φ dB, ∫ψ dB⟫ = ⟪φ, ψ⟫`. Unfolding both Hilbert inner
products as Bochner integrals (`L2.inner_def`; the real inner product on `ℝ` is
multiplication) this is the **covariation of two Itô integrals**

  `𝔼_μ[(∫φ dB)·(∫ψ dB)] = ∫ φ·ψ d(trim)`,

the polarized companion of the isometry — the L²-level statement of
`⟨∫φ dB, ∫ψ dB⟩ = ∫₀ᵀ φ_s ψ_s ds` (the predictable `trim` measure *is* `ds ⊗ μ`
trimmed to the predictable σ-algebra — a `.trim`, agreeing with `ds ⊗ μ` on
predictable integrands). The diagonal `φ = ψ` recovers the isometry exactly.

The reusable artifact is the bundled `LinearIsometry` `itoIsometry`: every Itô
inner-product fact is now one application of `LinearIsometry.inner_map_map`. This
is the bilinear completion of the B1 finite-horizon analytic tower and the
covariance backbone for multi-factor / covariance-swap pricing.

The unbounded-horizon `[0,∞)` analog (`itoIntegralL2`, B2) is identical once the
full predictable trim measure is exposed behind a named def; deferred.

## Main definitions

* `itoIsometry`: the `[0,T]` Itô integral bundled as a linear isometry
  `Lp ℝ 2 trim_T →ₗᵢ[ℝ] Lp ℝ 2 μ`.

## Main results

* `inner_itoIntegralCLM`: the `[0,T]` integral preserves the `L²` inner product,
  `⟪∫φ dB, ∫ψ dB⟫ = ⟪φ, ψ⟫`.
* `covariation_itoIntegralCLM`: `𝔼_μ[(∫φ dB)(∫ψ dB)] = ⟪φ, ψ⟫`.
* `variance_itoIntegralCLM`: on the diagonal, `𝔼_μ[(∫φ dB)²] = ‖φ‖²`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Ch 7

## Tags

covariation, bilinear Itô isometry, polarization identity, inner product, stochastic integral,
covariance, MSC 60H05, MSC 60G44
-/

@[expose] public section

namespace MathFin
namespace ItoIntegralCovariation

open MeasureTheory Filter Topology NNReal ENNReal ProbabilityTheory
open scoped MeasureTheory NNReal ENNReal InnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-- The `[0,T]` Itô integral bundled as a **linear isometry**
`Lp ℝ 2 trim_T →ₗᵢ[ℝ] Lp ℝ 2 μ`: the CLM `itoIntegralCLM` together with the
Itô isometry `itoIntegralCLM_norm`. The `norm_map'` field rewrites the
`ContinuousLinearMap`→`LinearMap` coercion (`coe_coe`) rather than forcing a
defeq through the underlying `extendOfNorm` term. -/
noncomputable def itoIsometry (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    Lp ℝ 2 (ItoIntegralCLM.trimMeasure (μ := μ) T hBmeas) →ₗᵢ[ℝ] Lp ℝ 2 μ where
  toLinearMap := (ItoIntegralCLM.itoIntegralCLM hB T hBmeas).toLinearMap
  norm_map' x := by
    simpa only [ContinuousLinearMap.coe_coe] using
      ItoIntegralCLM.itoIntegralCLM_norm hB T hBmeas x

/-- **Covariation of Itô integrals (inner-product form).** The `[0,T]` integral
preserves the L²-inner product: `⟪∫φ dB, ∫ψ dB⟫ = ⟪φ, ψ⟫`. Polarization of the
Itô isometry, via `LinearIsometry.inner_map_map`. -/
theorem inner_itoIntegralCLM (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ ψ : Lp ℝ 2 (ItoIntegralCLM.trimMeasure (μ := μ) T hBmeas)) :
    ⟪ItoIntegralCLM.itoIntegralCLM hB T hBmeas φ,
        ItoIntegralCLM.itoIntegralCLM hB T hBmeas ψ⟫_ℝ = ⟪φ, ψ⟫_ℝ :=
  (itoIsometry hB T hBmeas).inner_map_map φ ψ

/-- **Covariation of Itô integrals (expectation form).**
`𝔼_μ[(∫φ dB)·(∫ψ dB)] = ⟪φ, ψ⟫` — the expectation of the product of two Itô
integrals is the L²(trim) inner product of their integrands, i.e.
`∫ φ·ψ d(trim) = 𝔼_μ ∫₀ᵀ φ_s ψ_s ds`. The cross-isometry; `φ = ψ` recovers the
Itô isometry (`variance_itoIntegralCLM`). -/
theorem covariation_itoIntegralCLM (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ ψ : Lp ℝ 2 (ItoIntegralCLM.trimMeasure (μ := μ) T hBmeas)) :
    ∫ ω, (ItoIntegralCLM.itoIntegralCLM hB T hBmeas φ : Ω → ℝ) ω
        * (ItoIntegralCLM.itoIntegralCLM hB T hBmeas ψ : Ω → ℝ) ω ∂μ
      = ⟪φ, ψ⟫_ℝ := by
  have h := inner_itoIntegralCLM hB T hBmeas φ ψ
  rw [L2.inner_def] at h
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using h

/-- **Itô isometry, recovered from covariation.** The diagonal `φ = ψ`:
`𝔼_μ[(∫φ dB)²] = ‖φ‖²`. The Itô integral is centered (mean zero), so this second
moment is also its variance — hence the name. -/
theorem variance_itoIntegralCLM (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (ItoIntegralCLM.trimMeasure (μ := μ) T hBmeas)) :
    ∫ ω, (ItoIntegralCLM.itoIntegralCLM hB T hBmeas φ : Ω → ℝ) ω ^ 2 ∂μ
      = ‖φ‖ ^ 2 := by
  have h := covariation_itoIntegralCLM hB T hBmeas φ φ
  rw [real_inner_self_eq_norm_sq] at h
  simpa only [pow_two] using h

end ItoIntegralCovariation
end MathFin
