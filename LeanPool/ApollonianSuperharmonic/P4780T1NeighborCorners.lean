/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.Fintype.Card

public import LeanPool.ApollonianSuperharmonic.P4715T1VertexShift
public import LeanPool.ApollonianSuperharmonic.P4715T1BoundaryCycle

-- [TABLET NODE: P4780T1NeighborCorners]

/-!
# P4780T1NeighborCorners

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4780T1NeighborCorners (j : Fin 6) :
    let d : Int × Int := ![(1,0), (0,-1), (-1,-1), (-1,0), (0,1), (1,1)] j
    Set.range P4715T1BoundaryCycle ∩
      Set.range (P4715T1VertexShift d ∘ P4715T1BoundaryCycle) =
    {P4715T1BoundaryCycle j, P4715T1BoundaryCycle (j+1)} := by
-- BODY
  have hf : ∀ j : Fin 6,
      let d : Int × Int := ![(1,0), (0,-1), (-1,-1), (-1,0), (0,1), (1,1)] j
      (Finset.univ.image P4715T1BoundaryCycle) ∩
        (Finset.univ.image (P4715T1VertexShift d ∘ P4715T1BoundaryCycle)) =
      {P4715T1BoundaryCycle j, P4715T1BoundaryCycle (j+1)} := by
    decide +kernel
  have he := congrArg (fun s : Finset PeriodicSubtileIndex =>
    (s : Set PeriodicSubtileIndex)) (hf j)
  simpa only [Finset.coe_inter, Fintype.coe_image_univ,
    Finset.coe_insert, Finset.coe_singleton] using he

end ApollonianSuperharmonic

end
