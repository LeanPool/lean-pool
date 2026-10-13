/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCornerFinal

/-!
# OneStepOddClassCornerProducer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The corner producer: one leg

The corner sibling of the one-met-face gradient-Hölder producer:
at a window meeting two upper faces, the boundary gradient-Hölder producer has
a **single leg** — the interior display at the boundary, with no boundary-datum
contribution.  The odd-class defect at the corner datum `(0,0)` (the only
member of the collapsed class) is folded into the excess by the corner pricing
`(★★)` of `OneStepOddClassCornerFinal`.

This is the exact consumer shape the K-package chain
(`OneStepConditional.excessDecay_oneStep_of_harmonicApprox` through
`exists_gradientHolder_boundary_odd_ae`) expects, so the corner regime now
composes with the proved one-step contraction the same way the one-face regime
does.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The zero datum belongs to the odd affine class at every met
configuration. -/
theorem isOddAffineData_zero (x : Vec d) (m k : ℤ) :
    IsOddAffineData x m k (0 : ℝ) (0 : Vec d) := by
  have hlift : ∀ y : Vec d, affineLift x (0 : ℝ) (0 : Vec d) y = 0 := by
    intro y
    show (0 : ℝ) + vecDot (0 : Vec d) (y - x) = 0
    have hv0 : vecDot (0 : Vec d) (y - x) = 0 := by
      show ∑ l, (0 : Vec d) l * (y - x) l = 0
      refine Finset.sum_eq_zero fun l _ => ?_
      show (0 : ℝ) * (y - x) l = 0
      ring
    rw [hv0]
    ring
  exact ⟨fun i _ y _ => hlift y, fun i _ y _ => hlift y⟩

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

end

end Algsuperdiff.Section4.Provider.ExcessDecay
