/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandModifiedUnionEquality
public import LeanPool.ApollonianSuperharmonic.BandUnmodifiedCoverage

-- [TABLET NODE: BandModifiedCoverage]

/-!
# BandModifiedCoverage

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandModifiedCoverage (P : Fin 3 -> Bool -> ProtoTile)
    (O : ProtoTile) (u v : GaussianInt) (L : AddSubgroup GaussianInt)
    (K : BandUnmodifiedCoreCertificate P u v L)
    (hOB : O.cells ⊆ (P 0 false).cells) :
    forall x : LatticeCell, exists o : PeriodicSubtileIndex,
      x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells := by
-- BODY
  intro x
  have covered := BandUnmodifiedCoverage P u v L K x
  exact (BandModifiedUnionEquality P O u v hOB x).mp covered

end ApollonianSuperharmonic

end
