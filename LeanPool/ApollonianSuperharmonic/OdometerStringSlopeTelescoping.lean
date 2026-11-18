/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.ZippedChainInvariant

public import LeanPool.ApollonianSuperharmonic.P4261T2AdjacentMatrixSlope
public import LeanPool.ApollonianSuperharmonic.P4250T1DefinedHalfIntegralSlope
public import LeanPool.ApollonianSuperharmonic.OdometerStringRespect

/-!
# OdometerStringSlopeTelescoping

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
The slope invariant and its telescoping argument hold for every band circle.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- Odometer strings with a common endpoint have slope difference given by the circle matrix
applied to the centroid difference of their tiles. -/
theorem odometerStringSlopeTelescoping
    (C : BandCircle)
    (orientation : Bool) (base R S : ProtoTile)
    (tiles reverseTiles : List ProtoTile) (hs reverseHs : List PartialOdometer)
    (hf : OdometerStringRespect C orientation base R S tiles hs)
    (hr : OdometerStringRespect C orientation base S R reverseTiles reverseHs)
    (hendpoint : PartialOdometer)
    (hh : hs.head? = some hendpoint) (hh' : reverseHs.getLast? = some hendpoint)
    (U V : ProtoTile) (g k : PartialOdometer)
    (hU : (U, g) ∈ tiles.zip hs) (hV : (V, k) ∈ reverseTiles.zip reverseHs) :
    ∃ s t : Real × Real,
      PartialOdometerSlope g = some s ∧ PartialOdometerSlope k = some t ∧
      t.1 - s.1 = CircleMatrix C 0 0 * ((TileCentroid V).1 - (TileCentroid U).1) +
        CircleMatrix C 0 1 * ((TileCentroid V).2 - (TileCentroid U).2) ∧
      t.2 - s.2 = CircleMatrix C 1 0 * ((TileCentroid V).1 - (TileCentroid U).1) +
        CircleMatrix C 1 1 * ((TileCentroid V).2 - (TileCentroid U).2) := by
  obtain ⟨s, _, hsg, _⟩ := P4250T1DefinedHalfIntegralSlope C.1.1 U g C.2
    (List.forall₂_zip hf.2.1 hU)
  obtain ⟨t, _, htk, _⟩ := P4250T1DefinedHalfIntegralSlope C.1.1 V k C.2
    (List.forall₂_zip hr.2.1 hV)
  let invariant := fun X : ProtoTile × PartialOdometer =>
    let p := (PartialOdometerSlope X.2).getD (0, 0)
    (p.1 - CircleMatrix C 0 0 * (TileCentroid X.1).1 -
        CircleMatrix C 0 1 * (TileCentroid X.1).2,
      p.2 - CircleMatrix C 1 0 * (TileCentroid X.1).1 -
        CircleMatrix C 1 1 * (TileCentroid X.1).2)
  let invRel := fun X Y : ProtoTile × PartialOdometer => invariant X = invariant Y
  have invStep : ∀ A B : ProtoTile × PartialOdometer,
      LeftLatticeAdjacent C A.1 B.1 A.2 B.2 → invRel A B := by
    intro A B hadj
    obtain ⟨p, r, hp, hr, h0, h1⟩ := P4261T2AdjacentMatrixSlope C _ _ _ _ hadj
    change invariant A = invariant B
    apply Prod.ext <;> simp only [invariant, hp, hr, Option.getD_some]
    · linear_combination -h0
    · linear_combination -h1
  have hInvUV := zippedChainInvariant invariant tiles reverseTiles hs reverseHs R hendpoint
    hf.1.2.1 hh hr.1.2.2.1 hh' (List.Forall₂.length_eq hr.2.1)
    (hf.2.2.imp invStep) (hr.2.2.imp invStep) U V g k hU hV
  refine ⟨s, t, hsg, htk, ?_, ?_⟩
  · have heq := congrArg Prod.fst hInvUV
    simp only [invariant, hsg, htk, Option.getD_some] at heq
    linear_combination -heq
  · have heq := congrArg Prod.snd hInvUV
    simp only [invariant, hsg, htk, Option.getD_some] at heq
    linear_combination -heq

end ApollonianSuperharmonic

end
