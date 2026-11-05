/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PotentialOrder

/-!
# Positivity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Positivity and normalized alpha-shifted resolvent bounds

This module records fixed-coefficient, bounded-domain maximum-principle
estimates for the alpha-shifted divergence-form resolvent on its `ScalarL2`
carrier.  They are the zero-potential case of the corresponding estimates for
the resolvent with a bounded nonnegative potential.  All conclusions are
almost-everywhere statements with respect to `volumeMeasureOn U`: nonnegative
forcing gives a nonnegative resolvent, forcing bounded above by one gives an
upper bound of one after multiplication by the shift, and forcing in `[0, 1]`
is preserved by that normalized resolvent.  These are analytic `L2` results
only; this module does not construct a kernel, semigroup, or stochastic
process.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open scoped RealInnerProductSpace

variable {d : ℕ} {U : Set (Vec d)}

/-- The α-shifted resolvent preserves nonnegativity almost everywhere.
This is the counterpart of the weak maximum principle, which later recovers
the same conclusion for weak supersolutions. -/
theorem alphaShiftedResolvent_nonneg_ae (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U)
    (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    ∀ᵐ x ∂volumeMeasureOn U,
      0 ≤ alphaShiftedResolvent a hα hlam hEll f x := by
  have hq := isBoundedNonnegativePotential_zero (d := d) U
  have hnonneg :=
    potentialResolvent_nonneg_ae a hU hα hlam hEll _ hq f hf
  rwa [potentialResolvent_zero_potential a hα hlam hEll hq f] at hnonneg

end DivergenceFormProcess.Form
