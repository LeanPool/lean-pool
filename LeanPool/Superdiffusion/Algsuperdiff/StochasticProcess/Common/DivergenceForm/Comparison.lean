/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Positivity

/-!
# Comparison

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Same-coefficient resolvent comparison

This file records the fixed-coefficient almost-everywhere comparison principle
for the shifted resolvent as the zero-potential case of the comparison
principle for the resolvent with a bounded nonnegative potential.

The domain, coefficient field, and operator parameters are fixed. This is an
almost-everywhere analytic result on `ScalarL2` only; it does not compare
different coefficient fields or parameters, and it does not construct a
sub-Markov family, semigroup, kernel, or process.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory

variable {d : ℕ} {U : Set (Vec d)}

/-- The alpha-shifted resolvent preserves almost-everywhere order when the
coefficient field and all operator parameters are fixed.  This is also implied
by the later weak comparison principle. -/
theorem alphaShiftedResolvent_mono_ae [NeZero d]
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f g : ScalarL2 U)
    (hfg : ∀ᵐ x ∂volumeMeasureOn U, f x ≤ g x) :
    ∀ᵐ x ∂volumeMeasureOn U,
      alphaShiftedResolvent a hα hlam hEll f x ≤
        alphaShiftedResolvent a hα hlam hEll g x := by
  have hq := isBoundedNonnegativePotential_zero (d := d) U
  have hmono := potentialResolvent_mono_ae a hU hα hlam hEll _ hq f g hfg
  rwa [potentialResolvent_zero_potential a hα hlam hEll hq f,
    potentialResolvent_zero_potential a hα hlam hEll hq g] at hmono

end DivergenceFormProcess.Form
