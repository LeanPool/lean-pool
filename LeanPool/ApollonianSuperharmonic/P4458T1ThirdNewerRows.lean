/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AncestorOdometerInnerSupportNormalization
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.BandRegularTileTouchingClassification
public import LeanPool.ApollonianSuperharmonic.BandVectorOrientationDichotomy
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.P4458T1BoundaryFrame
public import LeanPool.ApollonianSuperharmonic.P4458T1BoundaryPlacement
public import LeanPool.ApollonianSuperharmonic.P4458T1BoundarySide
public import LeanPool.ApollonianSuperharmonic.P4458T1RestrictionFamily
public import LeanPool.ApollonianSuperharmonic.ParentVectorsInTilingLattice
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerSupportTransport
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.TileString
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.VectorNonvanishing
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.P4536T1AFrameB
public import LeanPool.ApollonianSuperharmonic.P4536T1AFrameD
public import LeanPool.ApollonianSuperharmonic.P4536T1EndpointDifferences
public import LeanPool.ApollonianSuperharmonic.P4536T1RegularJoin
public import LeanPool.ApollonianSuperharmonic.P4549T1DeeperFrameB
public import LeanPool.ApollonianSuperharmonic.P4549T1NegativeIncomingSide

-- [TABLET NODE: P4458T1ThirdNewerRows]

/-!
# P4458T1ThirdNewerRows

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4458T1ThirdNewerRows :
    ∀ {C : BandCircle}, ∀ {orientation : Bool}, ∀ {base : ProtoTile}, ∀ {Rminus : ProtoTile}, ∀
        {Rplus : ProtoTile}, ∀ {hminus : PartialOdometer}, ∀ {hplus : PartialOdometer}, ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3), ∀ (p : Fin 4 → CircleCoordinates),
        (ProperBandQuadruple p) → ((![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] =
      ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
        p 0, p 2, p 3]) → ((F.slot = a + 1 → C.1.1.1 = 1 →
      UnitOccurrenceOrientation p 1 orientation) → ((F.slot = a + 2 → C.1.1.1 = 1 →
      UnitOccurrenceOrientation p 2 orientation) → ((F.slot ≠ a) → (∀ (t : Fin 4 →
          CircleCoordinates), (ProperBandQuadruple t) → ((t 0 = p 3) → ((t 1 = p 2) → (((p 2).1 <
          (p 3).1) → ((F.slot = a + 1 → C.1.1.1 = 1 →
      UnitOccurrenceOrientation t 0 orientation) → (Nonempty (P4458T1BoundaryPlacement F
          D))))))))))) := by
  intro C orientation base Rminus Rplus hminus hplus F D a p hp hstep hB hD selected t ht ht0 ht1
      newer olderChart
-- BODY
  obtain ⟨s, hs, hcenter, hright, _, hrightSlope⟩ := P4536T1EndpointDifferences F D
  obtain ⟨J, hfamily, hcent, hcells, hodo, hanc, hocc⟩ :=
    P4536T1RegularJoin F D hcenter
  have hqA : F.q a.succ = p 0 := by simpa using congrFun hstep 1
  have hposA : 0 < (F.q a.succ).1 := by
    rw [hqA]
    exact (ProperBandCurvatureStructure p hp).1
  have hancA := D.ancestors a true hposA
  have hslots : F.slot = a + 1 ∨ F.slot = a + 2 := by
    have hne : F.slot.val ≠ a.val := fun he => selected (Fin.ext he)
    have hi := F.slot.isLt
    have ha := a.isLt
    have hv : F.slot.val = (a.val + 1) % 3 ∨
        F.slot.val = (a.val + 2) % 3 := by omega
    rcases hv with h | h
    · exact Or.inl (Fin.ext (by simpa [Fin.val_add] using h))
    · exact Or.inr (Fin.ext (by simpa [Fin.val_add] using h))
  rcases hslots with hslot | hslot
  · obtain ⟨G, _, _, houter, htile, hfunction⟩ :=
      P4549T1DeeperFrameB F D a p hp hstep hslot t ht ht0 ht1
        (olderChart hslot) J hfamily hodo hcent
    have hqE : F.q (a + 2).succ = p 3 := by simpa using congrFun hstep 3
    have hposE : 0 < (F.q (a + 2).succ).1 := by
      rw [hqE, ← ht0]
      exact (ProperBandCurvatureStructure t ht).1
    have hancestorG : AncestorOdometer G.outer.1.1 F.outer.1.1
        G.tile F.tile G.odometer F.odometer := by
      rw [houter, htile, hfunction]
      exact D.ancestors (a + 2) true hposE
    obtain ⟨H, _, _, houterH, htileH, hfunctionH⟩ :=
      P4536T1AFrameB F D a p hp hstep hslot (hB hslot) J hfamily hodo hcent
    have hancestorH : AncestorOdometer H.outer.1.1 F.outer.1.1
        H.tile F.tile H.odometer F.odometer := by
      rw [houterH, htileH, hfunctionH]
      exact hancA
    exact ⟨⟨J, hcells, hodo, hanc, hocc,
      .recursive G (a + 2) houter hancestorG,
      .recursive H a houterH hancestorH⟩⟩
  · obtain ⟨G, _, _, houter, htile, hfunction⟩ :=
      P4536T1AFrameD F D a p hp hstep hslot (hD hslot) J hfamily hodo hcent
    have hancestor : AncestorOdometer G.outer.1.1 F.outer.1.1
        G.tile F.tile G.odometer F.odometer := by
      rw [houter, htile, hfunction]
      exact hancA
    have hqB : F.q (a + 1).succ = p 2 := by simpa using congrFun hstep 2
    have hqE : F.q (a + 2).succ = p 3 := by simpa using congrFun hstep 3
    have htC : t 0 = C.1.1 := by
      rw [ht0, ← hqE, ← hslot]
      exact F.parent
    have idx : a + 2 + 2 = a + 1 := by fin_cases a <;> rfl
    have hrightCent : TileCentroid Rplus - TileCentroid J =
        GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (t 0) (t 1)) := by
      rw [hcent]
      simpa only [hslot, idx, hqE, hqB, ht0, ht1] using hright
    have hrightDiff : F.plus_slope - s =
        GaussianRealPoint (-(⟨0, 1⟩ : GaussianInt) * BandVectors.2 (t 0) (t 1)) := by
      simpa only [hslot, idx, hqE, hqB, ht0, ht1] using hrightSlope
    obtain ⟨hstring, hlink⟩ := P4549T1NegativeIncomingSide t ht htC
      base J Rplus (D.functions F.slot false) hplus F.base_band hfamily F.plus_family
      hodo F.plus_odo s F.plus_slope hs F.slope_plus hrightCent hrightDiff
    exact ⟨⟨J, hcells, hodo, hanc, hocc,
      .recursive G a houter hancestor, .direct hstring hlink⟩⟩

end ApollonianSuperharmonic

end
