/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.AlphaShiftedWeakSolution
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import LeanPool.HighContrastHomogenization.Support.Geometry.ConvexDomain
public import LeanPool.HighContrastHomogenization.Support.Sobolev.L2Ambient

/-!
# ResolventH10Representative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Honest Sobolev representatives of the domain resolvent

This file exposes the strongest representative statement currently supplied by the divergence-form
foundation.  On an open bounded convex domain, the `L²` resolvent has an honest zero-trace `H¹`
representative.  The theorem also identifies that representative with the canonical graph-carrier
weak solution.

No continuity is asserted.  Obtaining a continuous, or boundary-vanishing continuous,
representative requires a local-to-pointwise and boundary regularity bridge which is not currently
available in the declared dependencies.  That bridge may be supplied by a model-specific
consequence of Theorem C or by classical local regularity.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport
open scoped ZeroAtInfty

variable {d : ℕ} {U : Set (Vec d)}

/-- The shifted resolvent has an honest zero-trace Sobolev representative.  Both its `L²` value and
its gradient are the components of the canonical graph-carrier solution. -/
theorem exists_h10Function_alphaShiftedResolvent [NeZero d]
    (hU : IsOpenBoundedConvexDomain U) (a : CoeffField d) {alpha lam Lam : ℝ}
    (hAlpha : 0 < alpha) (hLam : 0 < lam) (hEll : IsEllipticFieldOn lam Lam U a)
    (f : ScalarL2 U) :
    ∃ u : H10Function U,
      ZeroTraceSobolev.ofH10Function u =
          alphaShiftedSolution a hAlpha hLam hEll f ∧
        IsAlphaShiftedWeakSolution a U alpha f
          (ZeroTraceSobolev.ofH10Function u) ∧
        u.toH1Function.toScalarL2 = alphaShiftedResolvent a hAlpha hLam hEll f := by
  obtain ⟨u, huValue, huGradient⟩ :=
    ZeroTraceSobolev.exists_h10Function hU
      (alphaShiftedSolution a hAlpha hLam hEll f)
  have hu : ZeroTraceSobolev.ofH10Function u =
      alphaShiftedSolution a hAlpha hLam hEll f := by
    apply ZeroTraceSobolev.ext
    · simpa only [ZeroTraceSobolev.toL2_ofH10Function] using huValue
    · simpa only [ZeroTraceSobolev.gradient_ofH10Function] using huGradient
  refine ⟨u, hu, ?_, ?_⟩
  · rw [hu]
    exact alphaShiftedSolution_isAlphaShiftedWeakSolution a hAlpha hLam hEll f
  calc
    u.toH1Function.toScalarL2 =
        ZeroTraceSobolev.toL2 (ZeroTraceSobolev.ofH10Function u) := by
      rw [ZeroTraceSobolev.toL2_ofH10Function]
    _ = ZeroTraceSobolev.toL2 (alphaShiftedSolution a hAlpha hLam hEll f) := by
      rw [hu]
    _ = alphaShiftedResolvent a hAlpha hLam hEll f := by
      rw [alphaShiftedResolvent_apply]

end DivergenceFormProcess.Form
