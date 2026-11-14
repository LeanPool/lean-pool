/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.Carrier
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ZeroExtensionGraph

/-!
# EquationRestriction

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Restriction of the matrix-coefficient equation

The Schauder iteration solves a comparison problem on every inner ball.  This
is the zero-extension transport of the ambient weak equation to those balls;
it is the matrix-valued analogue of the scalar Section 6 restriction lemma.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory
open HCPolySupport

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-- The zero extension of a test function pairs with a fixed vector field exactly
as the original test function does. -/
theorem setIntegral_vecDot_extendByZero {W V : Set (Vec d)} (hW : IsOpen W)
    (hV : IsOpen V) (hVW : V ⊆ W) (F : Vec d → Vec d) (phi : H10Function V) :
    ∫ p in W, vecDot (F p)
        ((phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function.grad p) ∂volume
      = ∫ p in V, vecDot (F p) (phi.toH1Function.grad p) ∂volume := by
  have hind : (fun p => vecDot (F p)
        ((phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function.grad p))
      = Set.indicator V (fun p => vecDot (F p) (phi.toH1Function.grad p)) := by
    funext p
    by_cases hp : p ∈ V
    · rw [Set.indicator_of_mem hp,
        HCPolySupport.H10Function.extendByZeroToOpenSuperset_grad,
        HCPolySupport.H10Function.zeroExtensionGrad_apply_of_mem phi hp]
    · rw [Set.indicator_of_notMem hp,
        HCPolySupport.H10Function.extendByZeroToOpenSuperset_grad,
        HCPolySupport.H10Function.zeroExtensionGrad_apply_of_not_mem phi hp,
        HCPolySupport.vecDot_zero_right]
  rw [hind, MeasureTheory.integral_indicator hV.measurableSet,
    Measure.restrict_restrict hV.measurableSet, Set.inter_eq_left.mpr hVW]

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
