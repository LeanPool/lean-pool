/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PotentialLinftyBound
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Positivity

/-!
# LinftyResolventBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Uniform bounds for the alpha-shifted resolvent

This module records fixed-coefficient analytic `L∞` bounds for the normalized
alpha-shifted divergence-form resolvent as the zero-potential case of the
corresponding bounds with a bounded nonnegative potential.  It transports an
almost-everywhere absolute bound on scalar `L²` forcing and records the
resulting contraction of the representative-invariant extended `L∞` seminorm.
No kernel, semigroup, or stochastic-process claim is made here.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory

variable {d : ℕ} {U : Set (Vec d)}

/-- If the forcing is almost everywhere bounded in absolute value by a
nonnegative constant, then the normalized alpha-shifted resolvent has the same
almost-everywhere absolute bound. -/
theorem abs_alpha_mul_alphaShiftedResolvent_le_ae [NeZero d]
    (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂volumeMeasureOn U, |f x| ≤ C) :
    ∀ᵐ x ∂volumeMeasureOn U,
      |α * alphaShiftedResolvent a hα hlam hEll f x| ≤ C := by
  have hq := isBoundedNonnegativePotential_zero (d := d) U
  have hbound :=
    abs_alpha_mul_potentialResolvent_le_ae a hU hα hlam hEll _ hq f C hC hf
  rwa [potentialResolvent_zero_potential a hα hlam hEll hq f] at hbound

end DivergenceFormProcess.Form
