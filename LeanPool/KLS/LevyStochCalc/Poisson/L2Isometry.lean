/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.Compensated

/-!
# Itô-Lévy L² isometry

The L²-isometry for the compensated-Poisson Itô–Lévy integral:

  `𝔼[ (∫_0^T ∫_E φ(s, e) Ñ(ds, de))² ] = 𝔼[ ∫_0^T ∫_E |φ(s, e)|² ν(de) ds ]`

for predictable square-integrable `φ`. Its proof reduces to the quadratic-
variation identity from
`LevyStochCalc.Poisson.Compensated.quadVar_stochasticIntegral`.

## Source

Applebaum, *Lévy Processes and Stochastic Calculus*, Cambridge 2009,
Theorem 4.2.3.

## Structure

Wrapper around `Compensated.itoLevyIsometry`, the isometry conjunct of the
construction `itoIsometry_compensated_unified_existence`
(`Poisson/Compensated.lean`; Applebaum 2009 Thm 4.2.3).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.L2Isometry

universe u v

/-- **Itô-Lévy L² isometry.** For a Poisson random measure `N` with
σ-finite intensity `ν` on `(E, ℰ)`, and a predictable square-integrable
integrand `φ : Ω × [0,T] × E → ℝ`,

  `𝔼[ (∫_0^T ∫_E φ(s, e) Ñ(ds, de))² ] = 𝔼[ ∫_0^T ∫_E |φ(s, e)|² ν(de) ds ]`.

Wrapper around `LevyStochCalc.Poisson.Compensated.itoLevyIsometry`. -/
theorem itoLevyIsometry
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h_sq_int_global : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ
            h_meas h_progMeas h_sq_int_global T ω‖₊
        : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        ((‖φ ω s e‖₊ : ℝ≥0∞)) ^ 2 ∂ν ∂volume ∂P :=
  LevyStochCalc.Poisson.Compensated.itoLevyIsometry N ℱ hℱ φ
    h_meas h_progMeas h_sq_int_global T hT

end LevyStochCalc.Poisson.L2Isometry
