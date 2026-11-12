/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralOdometerRowData
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralConfiguration
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryAffineVectorAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryAffineVectorCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCircleAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryGlobalOdometerTransport
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerActionFormulas
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryQuadrupleAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetrySlopeAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryScopedPhaseUnique
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileOdometerCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryVectorAction
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.FordCellDomain
public import LeanPool.ApollonianSuperharmonic.FordCoordinateConfiguration
public import LeanPool.ApollonianSuperharmonic.FordDoubledBoundary
public import LeanPool.ApollonianSuperharmonic.FordFareyParameter
public import LeanPool.ApollonianSuperharmonic.FordOdometer
public import LeanPool.ApollonianSuperharmonic.FordOdometerFamilyExistsUnique
public import LeanPool.ApollonianSuperharmonic.FordRegimeConverse
public import LeanPool.ApollonianSuperharmonic.FordTile
public import LeanPool.ApollonianSuperharmonic.FordTileOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.FordVertexDomain
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import LeanPool.ApollonianSuperharmonic.GlobalOdometerExtends
public import LeanPool.ApollonianSuperharmonic.IntegerCeilDiv
public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslateFormulas
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TileCentroid
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileReflectionFormulas
public import LeanPool.ApollonianSuperharmonic.TileOdometerAffineTranslation
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.P5448T1CenteredFordGeometry
public import LeanPool.ApollonianSuperharmonic.P5448T1CommonAffineFordPair
public import LeanPool.ApollonianSuperharmonic.P5448T1CanonicalFordBoundary
public import Mathlib.Tactic.Ring

-- [TABLET NODE: FordCenteredInteriorOdometerStencil]

/-!
# FordCenteredInteriorOdometerStencil

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FordCenteredInteriorOdometerStencil :
    ∀ (q : Fin 4 -> CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C0 :
        BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C0
        T), ∀ (h : PartialOdometer), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (r : Fin 3 -> Bool ->
        PartialOdometer), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S : Fin 3 -> Bool -> ProtoTile),
        ∀ (u : Fin 3 -> Bool -> PartialOdometer), ∀ (v : Fin 3 -> Bool -> PartialOdometer), ∀ (g
        : IntegerLatticeFunction), ∀ (x : GaussianInt), (BandOrderedGeneralOdometerRowData
      q cfg C0 T cert h P r Q S u v g) → ((GlobalOdometerExtends g h) → ((Nat.card {is : Fin 3 ×
          Bool //
      x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2) → ((GaussianRealPoint x =
          TileCentroid T) → (((cfg.firstPredecessor 1).1 = 0) → (FourNeighborLaplacian g x =
          0))))) := by
  intro q cfg C0 T cert h P r Q S u v g x data hext hk hcenter hzero
-- BODY
  obtain ⟨F, s, delta, f, hq, _, _, _, _, _, htP, htM, hdP, hdM,
    ⟨sp, sm, hsp, hsm, hsx, hsy⟩, hresP, hresM, hextF, hlap⟩ :=
    P5448T1CenteredFordGeometry q cfg C0 T cert h P r Q S u v g x
      data hext hcenter hzero
  have bounds := P5130T5ParentArithmetic F hq
  have hsum : (F.q : Int) = F.q₁ + F.q₂ := by exact_mod_cast F.sum_q
  have hp0 := (hdP 0).mpr (by simp)
  have hm0 := (hdM 0).mpr (by simp)
  have hshared := (hresP 0 hp0).2.symm.trans (hresM 0 hm0).2
  obtain ⟨a, b, hvP, hvM⟩ := P5448T1CommonAffineFordPair F hq _ _ _ _
    htP htM hdP hdM sp sm hsp hsm hsx hsy hshared
  obtain ⟨c, hc⟩ := hextF
  have extP (z : GaussianInt) (hz : z ∈ _) :=
    (hc z (hresP z hz).1).trans (congrArg (fun t : Int => t + c) (hresP z hz).2)
  have extM (z : GaussianInt) (hz : z ∈ _) :=
    (hc z (hresM z hz).1).trans (congrArg (fun t : Int => t + c) (hresM z hz).2)
  obtain ⟨hedge, hup, hdown⟩ := P5448T1CanonicalFordBoundary F hq
  have f0 : f 0 = b + c := by
    rw [extP 0 hp0, hvP 0 hp0]
    simpa using congrArg (fun t : Int => t + b + c)
      (hedge (F.q₁ : Int) (by omega) (by omega)).1
  have fp : f 1 = a.re + b + c := by
    have hz := (hdP 1).mpr (by simp; omega)
    rw [extP 1 hz, hvP 1 hz]
    have hb := (hedge (1 + (F.q₁ : Int)) (by omega) (by omega)).1
    have he : (1 : GaussianInt) + ⟨(F.q₁ : Int), 0⟩ = ⟨1 + (F.q₁ : Int), 0⟩ := by
      ext <;> simp
    rw [he, hb]
    simp
  have fm : f (-1) = -a.re + b + c := by
    have hz := (hdP (-1)).mpr (by simp; omega)
    rw [extP (-1) hz, hvP (-1) hz]
    have hb := (hedge (-1 + (F.q₁ : Int)) (by omega) (by omega)).1
    have he : (-1 : GaussianInt) + ⟨(F.q₁ : Int), 0⟩ = ⟨-1 + (F.q₁ : Int), 0⟩ := by
      ext <;> simp
    rw [he, hb]
    simp
  have fu : f ⟨0, 1⟩ = a.im + b + c := by
    have hz := (hdP ⟨0, 1⟩).mpr (by dsimp; omega)
    rw [extP _ hz, hvP _ hz]
    have he : (⟨0, 1⟩ : GaussianInt) + ⟨(F.q₁ : Int), 0⟩ = ⟨(F.q₁ : Int), 1⟩ := by
      ext <;> simp
    rw [he, hup]
    simp
  have fd : f (-⟨0, 1⟩) = -a.im + b + c := by
    have hz := (hdM (-⟨0, 1⟩)).mpr (by simp; omega)
    rw [extM _ hz, hvM _ hz]
    have he : -(⟨0, 1⟩ : GaussianInt) + ⟨(F.q₂ : Int), (F.q : Int)⟩ =
        ⟨(F.q₂ : Int), (F.q : Int) - 1⟩ := by
      ext <;> simp; ring
    rw [he, hdown]
    simp
  rw [← hlap]
  simp only [FourNeighborLaplacian, zero_add, zero_sub, f0, fp, fm, fu, fd]
  ring

end ApollonianSuperharmonic

end
