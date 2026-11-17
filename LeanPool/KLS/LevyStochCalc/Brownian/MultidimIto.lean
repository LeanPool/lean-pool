/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.MultidimFiltered
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoL2Completion

/-!
# Multidimensional Brownian Itô integral

The multidim L² Itô integral `∫_0^T Z_s · dW_s := ∑_i ∫_0^T Z_s^i dW_s^i`,
defined as the sum (over components `i : Fin d`) of the 1D Brownian Itô
integrals `LevyStochCalc.Brownian.SimplePredictableRefine.stochasticIntegral`
against the component Brownian motions `W.W i`.

The integral is taken with respect to a filtration `ℱ` for which every coordinate
`W.W i` is a Brownian motion (`hℱ`). For each component, the integrand
`(s, ω) ↦ Z s ω i` must be:
* jointly measurable (`h_meas`),
* progressively measurable with respect to `ℱ` (`h_progMeas`),
* L²-bounded on every `[0, T']`, `T' > 0` (`h_sq_int_global`).

These per-component hypotheses are exactly the ones the 1D primitive
requires; the multidim version just threads them through.

This file is in its own module (not in `Multidim.lean`) because the 1D
stochastic integral primitive lives in `SimplePredictableRefine.lean`,
which transitively imports `Multidim.lean` via `Brownian/Ito.lean`. Putting
the multidim integral here breaks the cycle.

## Reference

* Karatzas–Shreve §3.2 (multidim Itô integral as component sum).
* Le Gall §5.4 (Itô integral of vector-valued processes).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Multidim
namespace MultidimBrownianMotion

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {d : ℕ}

/-- The multidim Brownian Itô integral
`(∫_0^T Z_s · dW_s)(ω) = ∑_i ∫_0^T Z_s^i dW_s^i (ω)`.

`Z s ω i` is the `i`-th component of the integrand at `(s, ω)`. The result
at time `T` is the sum (over components) of the 1D Itô integrals against
the component Brownian motions `W.W i`.

Each component's 1D integral is `LevyStochCalc.Brownian.Ito.stochasticIntegral`
(`Brownian/ItoL2Completion.lean`), the coherent `L²`-limit of simple integrals
whose martingale, quadratic-variation and isometry properties are packaged in
`itoIsometry_brownian_unified_existence`. -/
noncomputable def stochasticIntegral
    (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (Z : ℝ → Ω → (Fin d → ℝ))
    (h_meas : ∀ i : Fin d, Measurable (Function.uncurry (fun ω s => Z s ω i)))
    (h_progMeas : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ (fun ω s => Z s ω i))
    (h_sq_int_global : ∀ i : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) : Ω → ℝ :=
  fun ω => ∑ i : Fin d,
    LevyStochCalc.Brownian.Ito.stochasticIntegral
      (W.W i) ℱ (hℱ i) (fun ω' s => Z s ω' i)
      (h_meas i) (h_progMeas i) (h_sq_int_global i) T ω

end MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim
