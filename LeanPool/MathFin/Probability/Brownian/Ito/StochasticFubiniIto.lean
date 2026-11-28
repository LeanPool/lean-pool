/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralCLM
public import LeanPool.MathFin.Probability.Brownian.Ito.StochasticFubini

/-!
# Stochastic Fubini for the Itô and Wiener integrals

The Itô integral `itoIntegralCLM` on `[0,T]` and the Wiener integral `wienerIntegralLp` are
continuous linear maps out of `L²` of a finite measure, so `stochFubini_ofCLM` applies to each:
a parameter integral of Itô (Wiener) integrals is the Itô (Wiener) integral of the parameter
integral of the integrands.

## Main results

* `stochFubini_ito`: `∫ u, itoIntegralCLM (φ u) ∂ν = itoIntegralCLM g` for `g` representing the
  integrated integrand `s ↦ ∫ u, ψ u s ∂ν`.
* `stochFubini_wiener`: the same for `wienerIntegralLp` on `L²(Ioc 0 T)`.

## References

* [M. Veraar, *The stochastic Fubini theorem revisited*][Veraar2012], Thm 2.2

## Tags

stochastic Fubini theorem, Itô integral, Wiener integral, MSC 60H05
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin
namespace StochasticFubini

section Ito

open ProbabilityTheory ItoIntegralCLM ItoIntegralL2

variable {A Ω : Type*} {mA : MeasurableSpace A} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {ν : Measure A} [SFinite ν]

/-- **Stochastic Fubini for the Itô integral on `[0,T]`**: if `φ : A → L²(trim_T)` is Bochner
integrable, `ψ` is a jointly integrable family of representatives of `φ`, and `g ∈ L²(trim_T)`
represents `s ↦ ∫ u, ψ u s ∂ν`, then `∫ u, (∫ φ u dB) dν(u) = ∫ g dB` in `Lp ℝ 2 μ`. -/
theorem stochFubini_ito (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (φ : A → Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hφ : Integrable φ ν) (ψ : A → ℝ≥0 × Ω → ℝ)
    (hψ : JointIntegrable ψ ν (trimMeasure (μ := μ) T hBmeas))
    (hφψ : ∀ u, ⇑(φ u) =ᵐ[trimMeasure (μ := μ) T hBmeas] ψ u)
    (g : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hg : ⇑g =ᵐ[trimMeasure (μ := μ) T hBmeas] fun s ↦ ∫ u, ψ u s ∂ν) :
    ∫ u, itoIntegralCLM hB T hBmeas (φ u) ∂ν = itoIntegralCLM hB T hBmeas g :=
  stochFubini_ofCLM (itoIntegralCLM hB T hBmeas) φ hφ ψ hψ hφψ g hg

end Ito

section Wiener

open ProbabilityTheory WienerIntegralL2

variable {A Ω : Type*} {mA : MeasurableSpace A} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {ν : Measure A} [SFinite ν]

omit [IsProbabilityMeasure μ] in
/-- **Stochastic Fubini for the Wiener integral on `[0,T]`**: the parameter integral of the
Wiener integrals `∫ u, wienerIntegralLp (φ u) ∂ν` is the Wiener integral of any `g ∈ L²(Ioc 0 T)`
representing `s ↦ ∫ u, ψ u s ∂ν`. -/
theorem stochFubini_wiener (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (φ : A → Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) (hφ : Integrable φ ν)
    (ψ : A → ℝ → ℝ)
    (hψ : JointIntegrable ψ ν (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
    (hφψ : ∀ u, ⇑(φ u) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))] ψ u)
    (g : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
    (hg : ⇑g =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))] fun s ↦ ∫ u, ψ u s ∂ν) :
    ∫ u, wienerIntegralLp B hB T (φ u) ∂ν = wienerIntegralLp B hB T g :=
  stochFubini_ofCLM (wienerIntegralLp B hB T) φ hφ ψ hψ hφψ g hg

end Wiener

end StochasticFubini
end MathFin
