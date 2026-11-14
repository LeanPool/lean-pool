/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepBoundarySchauder
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepConditional

/-!
# OneStepBoundaryEndpoint

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary-branch excess-decay endpoint

`OneStepSchauderChain.excessDecay_oneStep_interior_of_harmonicApprox` closed the
four Schauder slots of
`OneStepConditional.excessDecay_oneStep_of_harmonicApprox` on the interior
branch, at `K_h = 0`.  This module does the same on the **boundary** branch,
through the boundary branch's split Schauder bound:

```text
  Csch = boundarySchauderConst d = 48 · 3^{3/2} · schauderConst d · √((24(d+1))^d) ,
  K_h  = boundarySchauderConst d · (3^{-n})^{1/2} · (3^{-(n-2)} · boundaryDatumLeg …) .
```

The competitor enters through **classical harmonicity on the doubled window**
`reflectedWindow x m (n-2)` — which is what
`OneStepSchauderComposeBoundary.exists_classicalCompetitor_reflectedWindow`
produces from a variationally harmonic odd extension — together with its
square-integrability there.  Nothing here restricts the met set: the geometry
of `OneStepBoundaryGeometry` is uniform in it.

## What is still open, precisely

1. **The `_of_weaklyHarmonic` level.**
   `OneStepSchauderComposeInterior.excessDecay_oneStep_interior_of_weaklyHarmonic`
   removes the classical-harmonicity slot by applying Weyl's lemma on the
   anchor's *moved replacement cube* `y + □_{n-2}`, which is exactly where the
   anchor's `hharm` lives.  On the boundary branch the Schauder competitor lives
   on `reflectedWindow x m (n-2)`, and the moved replacement cube is **not**
   contained in it (in a met coordinate the clamped cube protrudes on the window
   side: `windowLo ≥ y_i − ½·3^{n-2}`), so the two representatives must be
   identified on `U_2` — where both are continuous and both agree a.e. with the
   competitor — before `hharm` can be transported.  That identification, plus the
   `EqOn` transfer of `gradField` and of `affineExcess`, is the remaining
   assembly; it is bookkeeping, not analysis.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory InnerProductSpace
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Square integrability against affine competitors on the doubled window -/

theorem integrableOn_sub_affineEval_sq_reflectedWindow {m k : ℤ} (x : Vec d)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict (reflectedWindow x m k)))
    (c : ℝ) (g : Vec d) :
    IntegrableOn (fun p => (u p - affineEval c g p) ^ 2) (reflectedWindow x m k) := by
  refine integrableOn_sub_affineEval_sq_of_axisCubeSandwich
    (zout := fun _ => -(1 / 2) * (3 : ℝ) ^ (m + 2)) (Lout := (3 : ℝ) ^ (m + 2))
    (zpow_pos (by norm_num) (m + 2)) (measurableSet_reflectedWindow x m k) ?_ hu c g
  refine subset_trans (reflectedWindow_subset_openCubeSet x m k) ?_
  rw [openCubeSet_originCube_eq_axisCube]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
