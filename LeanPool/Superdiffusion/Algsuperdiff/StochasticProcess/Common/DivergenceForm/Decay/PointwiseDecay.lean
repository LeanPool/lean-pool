/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.ExponentialPointwise
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.WeightedToBall

/-!
# PointwiseDecay

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Pointwise exponential decay away from the transition layer

This module assembles the exponentially weighted mass estimate, the conversion
of that estimate into a local `L²` bound, and the interior pointwise estimate
into a single statement: a bounded solution decays exponentially away from the
region where the localization is not yet constant, at the rate

`kappa * alpha / (alpha + d / 2)`,

where `kappa` is any rate admissible for the weighted estimate, in particular
`sqrt (lam * mass) / (2 * sqrt 2 * Lam)`.

The geometry enters only through four checkable conditions: the localization
is one near the point, the phase is at least `tx` near the point, the phase is
at most `tA` wherever the localization is not locally constant, and
`tA <= tx`.

What the estimate costs, stated plainly.  The dimension satisfies `2 <= d`;
`d = 1` is excluded, because the interior Hölder modulus comes from the
Schauder estimate on balls, which is stated for `2 <= d`.  The radius `r` of
that ball is arbitrary: any `0 < r` with `euclideanBall x r` inside the
domain will do, and the constant carries the explicit powers of `r`, so the
estimate may be applied at a small scale near the boundary.  The localization
and phase conditions are read on `euclideanBall x (r / 2)`, the largest
radius the balance uses.  The Hölder exponent satisfies `alpha` in
`[1/2, 1)`, and the coefficient field is within
`smallContrastThreshold d alpha` of the identity.  The constant is a sum of
two terms, not a single multiple of the uniform bound: the weighted `L²`
term, carrying `M`, the layer constant `Ceta` and the measure `volLayer` of
the transition layer, plus an additive Schauder summand built from the local
gradient size `E` and the forcing bound `G`; both are multiplied by the
exponential factor.  Finally the conclusion is a per-point existential: some
function continuous on `euclideanBall x (r / 2)` and almost everywhere equal
to the solution on `euclideanBall x r` is small at `x`.
`Decay/Representative.lean` transfers that bound to any fixed continuous
representative.

## Main results

- `DivergenceFormProcess.Decay.fderiv_eq_zero_of_eventuallyEq_one`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal

variable {d : ℕ}

/-- The admissible Agmon rate: the largest `kappa` allowed by the absorption
condition `8 Lam ^ 2 kappa ^ 2 <= lam * mass`. -/
def agmonRate (lam Lam mass : ℝ) : ℝ :=
  Real.sqrt (lam * mass) / (2 * Real.sqrt 2 * Lam)

theorem agmonRate_nonneg {lam Lam mass : ℝ} (hLam : 0 < Lam) :
    0 ≤ agmonRate lam Lam mass := by
  refine div_nonneg (Real.sqrt_nonneg _) ?_
  positivity

theorem agmonRate_admissible' {lam Lam mass : ℝ} (hlam : 0 ≤ lam)
    (hmass : 0 ≤ mass) (hLam : 0 < Lam) :
    8 * Lam ^ 2 * agmonRate lam Lam mass ^ 2 ≤ lam * mass :=
  agmonRate_admissible hlam hmass hLam

/-- A function equal to one on a neighbourhood has vanishing derivative. -/
theorem fderiv_eq_zero_of_eventuallyEq_one {f : Vec d → ℝ} {W : Set (Vec d)}
    (hW : IsOpen W) (hf : ∀ y ∈ W, f y = 1) {x : Vec d} (hx : x ∈ W) :
    fderiv ℝ f x = 0 := by
  have hev : f =ᶠ[nhds x] fun _ => (1 : ℝ) :=
    Filter.eventuallyEq_of_mem (hW.mem_nhds hx) hf
  rw [hev.fderiv_eq]
  simp

end DivergenceFormProcess.Decay
