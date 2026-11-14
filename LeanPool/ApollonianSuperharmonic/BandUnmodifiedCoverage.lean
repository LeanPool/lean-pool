/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandUnmodifiedCoreCertificate
public import LeanPool.ApollonianSuperharmonic.PeriodicTileCoverage

-- [TABLET NODE: BandUnmodifiedCoverage]

/-!
# BandUnmodifiedCoverage

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandUnmodifiedCoverage (P : Fin 3 -> Bool -> ProtoTile)
    (u v : GaussianInt) (L : AddSubgroup GaussianInt)
    (K : BandUnmodifiedCoreCertificate P u v L) :
    forall x : LatticeCell, exists o : PeriodicSubtileIndex,
      x ∈ (SubtileOccurrenceInterpretation P u v o).cells := by
-- BODY
  intro x
  obtain ⟨o, ho⟩ := PeriodicTileCoverage K.core x
  refine ⟨o, ?_⟩
  rw [← K.tile_eq o]
  exact ho

end ApollonianSuperharmonic

end
