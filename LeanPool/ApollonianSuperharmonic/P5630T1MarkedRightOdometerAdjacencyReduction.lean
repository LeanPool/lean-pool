/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCurvature

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightNormalizedBundleExists
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRoutedSelectedContact
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightSelectedAdjacency
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightOuterMarkingCriterion
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralMarkedSectorTransport
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryMarkedDataCovariance
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacentPackingSymmetryTransport

-- [TABLET NODE: P5630T1MarkedRightOdometerAdjacencyReduction]

/-!
# P5630T1MarkedRightOdometerAdjacencyReduction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace MarkedRightAdjacencyGeometry

private theorem hnorm :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x),
            bundle.normalizedCircle.1.1 = BandPackingSymmetryCircleAction bundle.symmetry C.1.1 )
            := by
  classical
  intro C T T₀ h h₀ x bundle
  calc
    bundle.normalizedCircle.1.1 = bundle.normalizedPresentation 0 :=
      bundle.normalized_circle_eq.symm
    _ = BandPackingSymmetryCircleAction bundle.symmetry C.1.1 := by
      rw [bundle.normalized_presentation_eq, bundle.rotated_presentation_eq]
      simp [BandPackingSymmetryQuadrupleAction,
        bundle.presentation_child]

private theorem hfixedCircleEq :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x),
            (bundle.normalizedCircle.1.1 = BandPackingSymmetryCircleAction bundle.symmetry C.1.1)
            → (bundle.normalizedFixedCircle.1.1 = bundle.normalizedCircle.1.1) ) := by
  classical
  intro C T T₀ h h₀ x bundle hnorm
  rw [bundle.normalized_fixed_circle_eq]
  exact hnorm.symm

private theorem hfixedOdometer :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x),
            (bundle.normalizedFixedCircle.1.1 = bundle.normalizedCircle.1.1) → (TileOdometer
            (bundle.normalizedPresentation 0) bundle.normalizedFixed
            bundle.normalizedFixedFunction) ) := by
  classical
  intro C T T₀ h h₀ x bundle hfixedCircleEq
  rw [bundle.normalized_circle_eq, ← hfixedCircleEq]
  exact bundle.normalized_fixed_odometer

private theorem hparentPositive :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x), ∀ (C' : BandCircle),
            (bundle.normalizedPresentation bundle.selectedSlot.succ = C'.1.1) → (0 <
            (bundle.normalizedPresentation bundle.selectedSlot.succ).1) ) := by
  classical
  intro C T T₀ h h₀ x bundle C' hq'
  rw [hq']
  exact C'.property

private theorem hinverseCoordinate :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x), ∀ (C' : BandCircle),
            (C'.1.1 = bundle.normalizedPresentation bundle.selectedSlot.succ) → (∀ (ginv :
            BandPackingSymmetry),
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        inversePresentation inverseSlot.succ = BandPackingSymmetryCircleAction ginv C'.1.1) ) := by
  classical
  intro C T T₀ h h₀ x bundle C' hC' ginv inversePresentation inverseSlot
  unfold inversePresentation inverseSlot
  rw [hC']
  generalize hidx : bundle.selectedSlot = j
  have neg1 : -(1 : Fin 3) = 2 := rfl
  have neg2 : -(2 : Fin 3) = 1 := rfl
  by_cases hrev : BandPackingSymmetryReversesOrientation ginv <;>
    fin_cases j <;>
    simp [BandPackingSymmetryQuadrupleAction,
      hrev, neg1, neg2];

private theorem hinversePositive :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x), ∀ (C' : BandCircle), ∀
            (ginv : BandPackingSymmetry), (∀ (g : BandPackingSymmetry), ∀ (c :
            CircleCoordinates), (BandPackingSymmetryCircleAction g c).1 = c.1) → (
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        (inversePresentation inverseSlot.succ = BandPackingSymmetryCircleAction ginv C'.1.1) → (0
            < (inversePresentation inverseSlot.succ).1)) ) := by
  classical
  intro C T T₀ h h₀ x bundle C' ginv actionCurvature inversePresentation inverseSlot
      hinverseCoordinate
  rw [hinverseCoordinate, actionCurvature]
  exact C'.property

private theorem hsubNormalized :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x), ∀ (C' : BandCircle),
            (TileSubodometer bundle.normalizedCircle.1.1 C'.1.1 bundle.normalizedRoot
                (bundle.pieces bundle.selectedSlot
            bundle.selectedSign) bundle.normalizedRootFunction (bundle.functions
            bundle.selectedSlot bundle.selectedSign)) → ((bundle.normalizedCircle.1.1 =
                BandPackingSymmetryCircleAction
            bundle.symmetry C.1.1) → (
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        TileSubodometer (BandPackingSymmetryCircleAction bundle.symmetry C.1.1) C'.1.1
            (BandPackingSymmetryTileAction bundle.symmetry T) selectedSupport
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h) selectedFunction)) ) := by
  classical
  intro C T T₀ h h₀ x bundle C' hsub hnorm selectedSupport selectedFunction
  simpa [hnorm, bundle.normalized_root_eq,
    bundle.normalized_root_function_eq] using hsub

private theorem hsubInverse :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ((∀ (g : BandPackingSymmetry), ∀ (C :
            CircleCoordinates), ∀ (C' : CircleCoordinates), ∀ (T : ProtoTile), ∀ (T' :
            ProtoTile), ∀ (h : PartialOdometer), ∀ (h' : PartialOdometer), TileSubodometer C C' T
            T' h h' ↔ TileSubodometer (BandPackingSymmetryCircleAction g C)
            (BandPackingSymmetryCircleAction g C') (BandPackingSymmetryTileAction g T)
            (BandPackingSymmetryTileAction g T') (BandPackingSymmetryPartialOdometerAction g h)
            (BandPackingSymmetryPartialOdometerAction g h')) ∧ (∀ (g : BandPackingSymmetry), ∀ (x
            : GaussianInt), ∀ (T : ProtoTile), ∀ (U : ProtoTile), (∀ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ T.cells ∨ LatticeVertexIncidentCell x j ∈ U.cells) ↔
            ∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell (BandPackingSymmetryVectorAction g x)
            j ∈ (BandPackingSymmetryTileAction g T).cells ∨ LatticeVertexIncidentCell
            (BandPackingSymmetryVectorAction g x) j ∈ (BandPackingSymmetryTileAction g U).cells)
            ∧ ∀ (g : BandPackingSymmetry), ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
            ProperBandQuadruple q → ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (delta : Bool),
            BandPackingSymmetryScopedPhase g q delta → ∀ (T : ProtoTile), ∀ (x : GaussianInt),
        let q' := BandPackingSymmetryQuadrupleAction g q;
        let sigma := fun (j : Fin (3 : ℕ)) => if BandPackingSymmetryReversesOrientation g = true
            then -j else j;
        let s' := if BandPackingSymmetryReversesOrientation g = true then -s - (1 : Fin (4 : ℕ))
            + if delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ)) else s + if delta =
            true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ));
        let oldRight := TileTranslation T ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if
            Even (↑s : ℕ) then BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) else BandVectors.1
            (q i.succ) (q (0 : Fin (4 : ℕ))));
        let newRight := TileTranslation (BandPackingSymmetryTileAction g T) ((⟨(0 : ℤ), (1 : ℤ)⟩
            : GaussianInt) ^ (↑s' : ℕ) * if Even (↑s' : ℕ) then BandVectors.1 (q' (0 : Fin (4 :
            ℕ))) (q' (sigma i).succ) else BandVectors.1 (q' (sigma i).succ) (q' (0 : Fin (4 :
            ℕ)))); BandPackingSymmetryTileAction g oldRight = newRight ∧ (x ∈ FootprintVertices
            oldRight ↔ BandPackingSymmetryVectorAction g x ∈ FootprintVertices newRight)) → (∀
            (bundle : BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x), ∀ (C' :
            BandCircle), ∀ (ginv : BandPackingSymmetry), (∀ (C_1 : CircleCoordinates),
            BandPackingSymmetryCircleAction ginv (BandPackingSymmetryCircleAction bundle.symmetry
            C_1) = C_1) → ((∀ (T_1 : ProtoTile), BandPackingSymmetryTileAction ginv
            (BandPackingSymmetryTileAction bundle.symmetry T_1) = T_1) → ((∀ (h_1 :
            PartialOdometer), BandPackingSymmetryPartialOdometerAction ginv
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h_1) = h_1) → (
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        ∀ (hinverseProper : ProperBandQuadruple inversePresentation), ∀ (hinversePositive : 0 <
            (inversePresentation inverseSlot.succ).1),
        let inverseCircle : BandCircle :=
          ⟨⟨inversePresentation inverseSlot.succ,
            ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
              ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
        (inverseCircle.1.1 = BandPackingSymmetryCircleAction ginv C'.1.1) → (
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        let T' := BandPackingSymmetryTileAction ginv selectedSupport
        let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
        (TileSubodometer (BandPackingSymmetryCircleAction bundle.symmetry C.1.1) C'.1.1
            (BandPackingSymmetryTileAction bundle.symmetry T) selectedSupport
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h) selectedFunction) →
            (TileSubodometer C.1.1 inverseCircle.1.1 T T' h h')))))) ) := by
  classical
  intro C T T₀ h h₀ x markedData bundle C' ginv hcircleL htileL hfunL inversePresentation
      inverseSlot hinverseProper hinversePositive inverseCircle hinverseCircle selectedSupport
      selectedFunction T' h' hsubNormalized
  have htransport :=
    (markedData.1 ginv (BandPackingSymmetryCircleAction bundle.symmetry C.1.1)
      C'.1.1 (BandPackingSymmetryTileAction bundle.symmetry T) selectedSupport
      (BandPackingSymmetryPartialOdometerAction bundle.symmetry h)
      selectedFunction).mp hsubNormalized
  simpa [hcircleL, htileL, hfunL, hinverseCircle, T', h'] using htransport

private theorem inverseDomain :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (v : GaussianInt), BandPackingSymmetryVectorAction ginv
            (BandPackingSymmetryVectorAction bundle.symmetry v) = v) → (∀ (f : PartialOdometer),
            ∀ (y : GaussianInt), (BandPackingSymmetryVectorAction bundle.symmetry y ∈ f.domain) →
            (y ∈ (BandPackingSymmetryPartialOdometerAction ginv f).domain)) ) := by
  classical
  intro C T T₀ h h₀ x bundle ginv hvecL f y hy
  change y ∈ ((BandPackingSymmetryPartialOdometerAction ginv f).domain : Set GaussianInt)
  rw [(BandPackingSymmetryPartialOdometerActionFormulas ginv f f).1]
  exact ⟨BandPackingSymmetryVectorAction bundle.symmetry y, hy, hvecL y⟩

private theorem hxFixedOriginal :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x),
            (bundle.normalizedPoint ∈ bundle.normalizedFixedFunction.domain) → (∀ (ginv :
            BandPackingSymmetry), (∀ (h_1 : PartialOdometer),
            BandPackingSymmetryPartialOdometerAction ginv
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h_1) = h_1) → ((∀ (f :
            PartialOdometer), ∀ (y : GaussianInt), (BandPackingSymmetryVectorAction
            bundle.symmetry y ∈ f.domain) → (y ∈ (BandPackingSymmetryPartialOdometerAction ginv
            f).domain)) → ((BandPackingSymmetryVectorAction bundle.symmetry x =
            bundle.normalizedPoint) → (x ∈ h₀.domain)))) ) := by
  classical
  intro C T T₀ h h₀ x bundle hxFixed ginv hfunL inverseDomain hpoint
  have hback := inverseDomain
    (BandPackingSymmetryPartialOdometerAction bundle.symmetry h₀) x (by
      simpa [hpoint, bundle.normalized_fixed_function_eq] using hxFixed)
  simpa [bundle.normalized_fixed_function_eq, hfunL] using hback

private theorem hxSelectedOriginal :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x),
            (bundle.normalizedPoint ∈ (bundle.functions bundle.selectedSlot
            bundle.selectedSign).domain) → (∀ (ginv : BandPackingSymmetry),
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
        (∀ (f : PartialOdometer), ∀ (y : GaussianInt), (BandPackingSymmetryVectorAction
            bundle.symmetry y ∈ f.domain) → (y ∈ (BandPackingSymmetryPartialOdometerAction ginv
            f).domain)) → ((BandPackingSymmetryVectorAction bundle.symmetry x =
            bundle.normalizedPoint) → (x ∈ h'.domain))) ) := by
  classical
  intro C T T₀ h h₀ x bundle hxSelected ginv selectedFunction h' inverseDomain hpoint
  have hback := inverseDomain selectedFunction x (by simpa [hpoint] using hxSelected)
  simpa [h'] using hback

private theorem hstarOriginal :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x), (∀ (y : GaussianInt),
            y = bundle.normalizedPoint ∨ y = bundle.normalizedPoint + (1 : GaussianInt) ∨ y =
            bundle.normalizedPoint - (1 : GaussianInt) ∨ y = bundle.normalizedPoint + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt) ∨ y = bundle.normalizedPoint - (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) → y ∈ bundle.normalizedFixedFunction.domain ∨ y ∈ (bundle.functions
            bundle.selectedSlot bundle.selectedSign).domain) → (∀ (ginv : BandPackingSymmetry),
            (∀ (h_1 : PartialOdometer), BandPackingSymmetryPartialOdometerAction ginv
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h_1) = h_1) → (
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
        (∀ (f : PartialOdometer), ∀ (y : GaussianInt), (BandPackingSymmetryVectorAction
            bundle.symmetry y ∈ f.domain) → (y ∈ (BandPackingSymmetryPartialOdometerAction ginv
            f).domain)) → ((BandPackingSymmetryVectorAction bundle.symmetry x =
            bundle.normalizedPoint) → ((∀ (g : BandPackingSymmetry), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), (b = a ∨ b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) →
            (BandPackingSymmetryVectorAction g b = BandPackingSymmetryVectorAction g a ∨
            BandPackingSymmetryVectorAction g b = BandPackingSymmetryVectorAction g a + 1 ∨
            BandPackingSymmetryVectorAction g b = BandPackingSymmetryVectorAction g a - 1 ∨
            BandPackingSymmetryVectorAction g b = BandPackingSymmetryVectorAction g a + ⟨0, 1⟩ ∨
            BandPackingSymmetryVectorAction g b = BandPackingSymmetryVectorAction g a - ⟨0, 1⟩))
            → (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ → y ∈
            h₀.domain ∨ y ∈ h'.domain))))) ) := by
  classical
  intro C T T₀ h h₀ x bundle hstar' ginv hfunL selectedFunction h' inverseDomain hpoint mapStar y hy
  have hnormalizedStar := mapStar bundle.symmetry x y hy
  rw [hpoint] at hnormalizedStar
  have hmem := hstar' (BandPackingSymmetryVectorAction bundle.symmetry y)
      hnormalizedStar
  rcases hmem with hfixed | hselected
  · left
    have hback := inverseDomain
      (BandPackingSymmetryPartialOdometerAction bundle.symmetry h₀) y (by
        simpa [bundle.normalized_fixed_function_eq] using hfixed)
    simpa [hfunL] using hback
  · right
    have hback := inverseDomain selectedFunction y hselected
    simpa [h'] using hback

private theorem hselectedCoord :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x), ∀ (C' : BandCircle),
            (bundle.normalizedPresentation bundle.selectedSlot.succ = C'.1.1) → (∀ (ginv :
            BandPackingSymmetry),
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        ∀ (hinverseProper : ProperBandQuadruple inversePresentation), ∀ (hinversePositive : 0 <
            (inversePresentation inverseSlot.succ).1),
        let inverseCircle : BandCircle :=
          ⟨⟨inversePresentation inverseSlot.succ,
            ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
              ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
        (inverseCircle.1.1 = BandPackingSymmetryCircleAction ginv C'.1.1) →
            ((BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation) (if
            BandPackingSymmetryReversesOrientation ginv then -bundle.selectedSlot else
            bundle.selectedSlot).succ = inverseCircle.1.1)) ) := by
  classical
  intro C T T₀ h h₀ x bundle C' hq' ginv inversePresentation inverseSlot hinverseProper
      hinversePositive inverseCircle hinverseCircle
  have neg1 : -(1 : Fin 3) = 2 := rfl
  have neg2 : -(2 : Fin 3) = 1 := rfl
  calc
    (BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation)
        (if BandPackingSymmetryReversesOrientation ginv then
          -bundle.selectedSlot else bundle.selectedSlot).succ =
        BandPackingSymmetryCircleAction ginv
          (bundle.normalizedPresentation bundle.selectedSlot.succ) := by
            generalize hidx : bundle.selectedSlot = j
            by_cases hrev : BandPackingSymmetryReversesOrientation ginv <;>
              fin_cases j <;>
              simp [BandPackingSymmetryQuadrupleAction,
                hrev, neg1, neg2]
    _ = BandPackingSymmetryCircleAction ginv C'.1.1 :=
      congrArg (BandPackingSymmetryCircleAction ginv) hq'
    _ = inverseCircle.1.1 := hinverseCircle.symm

private theorem hrootAction :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (C_1 : CircleCoordinates), BandPackingSymmetryCircleAction
            ginv (BandPackingSymmetryCircleAction bundle.symmetry C_1) = C_1) →
            ((bundle.normalizedCircle.1.1 =
            BandPackingSymmetryCircleAction bundle.symmetry C.1.1) →
            (BandPackingSymmetryCircleAction ginv (bundle.normalizedPresentation 0) = C.1.1)) )
            := by
  classical
  intro C T T₀ h h₀ x bundle ginv hcircleL hnorm
  calc
    BandPackingSymmetryCircleAction ginv (bundle.normalizedPresentation 0) =
        BandPackingSymmetryCircleAction ginv bundle.normalizedCircle.1.1 :=
          congrArg (BandPackingSymmetryCircleAction ginv)
            bundle.normalized_circle_eq
    _ = BandPackingSymmetryCircleAction ginv
        (BandPackingSymmetryCircleAction bundle.symmetry C.1.1) :=
          congrArg (BandPackingSymmetryCircleAction ginv) hnorm
    _ = C.1.1 := hcircleL C.1.1

private theorem hOFixedOriginal :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (T_1 : ProtoTile), BandPackingSymmetryTileAction ginv
            (BandPackingSymmetryTileAction bundle.symmetry T_1) = T_1) → ((∀ (h_1 :
            PartialOdometer), BandPackingSymmetryPartialOdometerAction ginv
            (BandPackingSymmetryPartialOdometerAction bundle.symmetry h_1) = h_1) →
            ((TileOdometer (BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
            (0 : Fin (4 : ℕ))) (BandPackingSymmetryTileAction ginv bundle.normalizedFixed)
            (BandPackingSymmetryPartialOdometerAction ginv bundle.normalizedFixedFunction)) →
            ((BandPackingSymmetryCircleAction ginv (bundle.normalizedPresentation 0) = C.1.1) →
            (TileOdometer C.1.1 T₀ h₀)))) ) := by
  classical
  intro C T T₀ h h₀ x bundle ginv htileL hfunL hOFixedInv hrootAction
  have h := hOFixedInv
  change TileOdometer
    (BandPackingSymmetryCircleAction ginv (bundle.normalizedPresentation 0))
    (BandPackingSymmetryTileAction ginv bundle.normalizedFixed)
    (BandPackingSymmetryPartialOdometerAction ginv
      bundle.normalizedFixedFunction) at h
  rw [hrootAction] at h
  rw [bundle.normalized_fixed_eq, htileL,
    bundle.normalized_fixed_function_eq, hfunL] at h
  exact h

private theorem hrootCoord :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (C_1 : CircleCoordinates), BandPackingSymmetryCircleAction
            ginv (BandPackingSymmetryCircleAction bundle.symmetry C_1) = C_1) →
            ((bundle.normalizedCircle.1.1 =
            BandPackingSymmetryCircleAction bundle.symmetry C.1.1) →
            ((BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation) 0 = C.1.1))
            ) := by
  classical
  intro C T T₀ h h₀ x bundle ginv hcircleL hnorm
  calc
    (BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation) 0 =
        BandPackingSymmetryCircleAction ginv
          (bundle.normalizedPresentation 0) := by
            simp [BandPackingSymmetryQuadrupleAction]
    _ = C.1.1 := by
        rw [bundle.normalized_circle_eq, hnorm]
        exact hcircleL C.1.1

private theorem hnewAdj :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x), (ProperBandQuadruple
            bundle.normalizedPresentation) → (∀ (ginv : BandPackingSymmetry), ∀ (pFixed : ℝ × ℝ),
            ∀ (pSelected : ℝ × ℝ), ∀ (t' : Fin (4 : ℕ)), (PartialOdometerSlope
            (BandPackingSymmetryPartialOdometerAction ginv (bundle.functions bundle.selectedSlot
            bundle.selectedSign)) = some pSelected) → ((pSelected.1 - pFixed.1 = (1 / 2 : ℝ) *
            (GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑t' : ℕ) *
            (BandVectors.2 (BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
            (if BandPackingSymmetryReversesOrientation ginv = true then -bundle.selectedSlot else
            bundle.selectedSlot).succ) (BandPackingSymmetryQuadrupleAction ginv
            bundle.normalizedPresentation (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation (0 : Fin (4 :
            ℕ))) (BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation (if
            BandPackingSymmetryReversesOrientation ginv = true then -bundle.selectedSlot else
            bundle.selectedSlot).succ)))).1) → ((pSelected.2 - pFixed.2 = (1 / 2 : ℝ) *
            (GaussianRealPoint ((-(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ^ (↑t' : ℕ) *
            (BandVectors.2 (BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
            (if BandPackingSymmetryReversesOrientation ginv = true then -bundle.selectedSlot else
            bundle.selectedSlot).succ) (BandPackingSymmetryQuadrupleAction ginv
            bundle.normalizedPresentation (0 : Fin (4 : ℕ))) + BandVectors.2
            (BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation (0 : Fin (4 :
            ℕ))) (BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation (if
            BandPackingSymmetryReversesOrientation ginv = true then -bundle.selectedSlot else
            bundle.selectedSlot).succ)))).2) → (
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        ∀ (hinverseProper : ProperBandQuadruple inversePresentation), ∀ (hinversePositive : 0 <
            (inversePresentation inverseSlot.succ).1),
        let inverseCircle : BandCircle :=
          ⟨⟨inversePresentation inverseSlot.succ,
            ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
              ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
        let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
        let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
        let T' := BandPackingSymmetryTileAction ginv selectedSupport
        let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
        ((BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation) (if
            BandPackingSymmetryReversesOrientation ginv then -bundle.selectedSlot else
            bundle.selectedSlot).succ = inverseCircle.1.1) → ((TileOdometer C.1.1 T₀ h₀) →
            ((TileOdometer inverseCircle.1.1 T' h') → ((PartialOdometerSlope h₀ = some pFixed) →
            ((TileCentroid T' - TileCentroid T₀ = (1 / 2 : ℝ) • GaussianRealPoint ((⟨0, 1⟩ :
            GaussianInt) ^ t'.val * (BandVectors.1 ((BandPackingSymmetryQuadrupleAction ginv
            bundle.normalizedPresentation) (if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot).succ)
            ((BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation) 0) +
            BandVectors.1 ((BandPackingSymmetryQuadrupleAction ginv
            bundle.normalizedPresentation) 0) ((BandPackingSymmetryQuadrupleAction ginv
            bundle.normalizedPresentation) (if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot).succ)))) →
            (((BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation) 0 = C.1.1)
            → (SubtileLatticeAdjacent C inverseCircle T₀ T' h₀ h')))))))))) ) := by
  classical
  intro C T T₀ h h₀ x bundle hq ginv pFixed pSelected t' hslopeSelectedInv hslopeReInv
      hslopeImInv inversePresentation inverseSlot hinverseProper hinversePositive inverseCircle
      selectedSupport selectedFunction T' h' hselectedCoord hOFixedOriginal hOSelectedOriginal
      hslopeFixedOriginal hcentOriginal hrootCoord
  refine ⟨hOFixedOriginal, hOSelectedOriginal, pFixed, pSelected,
    hslopeFixedOriginal, hslopeSelectedInv, ?_⟩
  exact ⟨BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation,
    (if BandPackingSymmetryReversesOrientation ginv then
      -bundle.selectedSlot else bundle.selectedSlot),
    t', BandPackingSymmetryProperCovariance ginv bundle.normalizedPresentation hq,
    hrootCoord, hselectedCoord, hcentOriginal, hslopeReInv, hslopeImInv⟩

private theorem hsizeOriginal :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x), ∀ (C' : BandCircle),
            (bundle.normalizedCircle.1.1.1.toNat +
            C'.1.1.1.toNat < bundle.normalizedCircle.1.1.1.toNat +
                bundle.normalizedCircle.1.1.1.toNat) → (∀ (ginv : BandPackingSymmetry),
            (bundle.normalizedCircle.1.1 =
            BandPackingSymmetryCircleAction bundle.symmetry C.1.1) → ((∀ (g :
            BandPackingSymmetry), ∀ (c : CircleCoordinates), (BandPackingSymmetryCircleAction g
            c).1 = c.1) → (
        let inversePresentation :=
          BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
        let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot
        ∀ (hinverseProper : ProperBandQuadruple inversePresentation), ∀ (hinversePositive : 0 <
            (inversePresentation inverseSlot.succ).1),
        let inverseCircle : BandCircle :=
          ⟨⟨inversePresentation inverseSlot.succ,
            ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
              ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
        (inverseCircle.1.1 = BandPackingSymmetryCircleAction ginv C'.1.1) → (Int.toNat C.1.1.1 +
            Int.toNat inverseCircle.1.1.1 < Int.toNat C.1.1.1 + Int.toNat C.1.1.1)))) ) := by
  classical
  intro C T T₀ h h₀ x bundle C' hsize ginv hnorm actionCurvature inversePresentation inverseSlot
      hinverseProper hinversePositive inverseCircle hinverseCircle
  have hrootCurv : C.1.1.1 = bundle.normalizedCircle.1.1.1 := by
    rw [hnorm]
    exact (actionCurvature bundle.symmetry C.1.1).symm
  have hchildCurv : inverseCircle.1.1.1 = C'.1.1.1 := by
    rw [hinverseCircle]
    exact actionCurvature ginv C'.1.1
  rw [hrootCurv, hchildCurv]
  exact hsize

private theorem coverShape :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ∀ (A : ProtoTile), ∀ (B : ProtoTile), (∀ z, z = a ∨ z = a - 1 ∨ z =
            a - ⟨0, 1⟩ ∨ z = a - 1 - ⟨0, 1⟩ → z ∈ A.cells ∨ z ∈ B.cells) ↔ (∀ j : Fin 4,
            LatticeVertexIncidentCell a j ∈ A.cells ∨ LatticeVertexIncidentCell a j ∈ B.cells) )
            := by
  classical
  intro a A B
  constructor
  · intro h j
    fin_cases j <;> simp only [LatticeVertexIncidentCell, Int.reduceNeg, Fin.mk_one,
        Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.reduceFinMk,
        Matrix.cons_val, Fin.zero_eta] <;>
      first | exact h _ (by simp)
  · intro h z hz
    rcases hz with hz | hz | hz | hz
    · subst z; simpa [LatticeVertexIncidentCell] using h 0
    · subst z; simpa [LatticeVertexIncidentCell] using h 1
    · subst z; simpa [LatticeVertexIncidentCell] using h 3
    · subst z; simpa [LatticeVertexIncidentCell] using h 2

private theorem hpointInverse :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x), ∀ (ginv :
            BandPackingSymmetry), (∀ (v : GaussianInt), BandPackingSymmetryVectorAction ginv
            (BandPackingSymmetryVectorAction bundle.symmetry v) = v) →
            ((BandPackingSymmetryVectorAction bundle.symmetry x = bundle.normalizedPoint) →
            (BandPackingSymmetryVectorAction ginv bundle.normalizedPoint = x)) ) := by
  classical
  intro C T T₀ h h₀ x bundle ginv hvecL hpoint
  rw [← hpoint]
  exact hvecL x

private theorem hmarkTransport :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (T₀ : ProtoTile), ∀ (h : PartialOdometer), ∀ (h₀
            : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C C T T₀ h h₀ x), ∀ (rightPlacement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), ∀ (s : Fin (4 : ℕ)), (TileTranslation bundle.normalizedFixed
            ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1
            (bundle.normalizedPresentation (0 : Fin (4 : ℕ))) (bundle.normalizedPresentation
            bundle.selectedSlot.succ) else BandVectors.1 (bundle.normalizedPresentation
            bundle.selectedSlot.succ) (bundle.normalizedPresentation (0 : Fin (4 : ℕ)))) =
            TileTranslation bundle.normalizedFixed ((if rightPlacement.rightNeighborPositive =
            true then (-1 : GaussianInt) else (1 : GaussianInt)) * BandVectors.1
            (bundle.normalizedPresentation (0 : Fin (4 : ℕ))) (bundle.normalizedPresentation
            bundle.selectedSlot.succ))) → (∀ (ginv : BandPackingSymmetry), (∀ (T_1 : ProtoTile),
            BandPackingSymmetryTileAction ginv (BandPackingSymmetryTileAction bundle.symmetry
            T_1) = T_1) → (∀ (delta : Bool), ∀ (t' : Fin (4 : ℕ)), (t' = if
            BandPackingSymmetryReversesOrientation ginv = true then -s - (1 : Fin (4 : ℕ)) + if
            delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ)) else s + if delta = true
            then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ))) → (
        let oldRight := TileTranslation bundle.normalizedFixed
          ((if rightPlacement.rightNeighborPositive = true then (-1 : GaussianInt)
            else 1) *
            BandVectors.1 (bundle.normalizedPresentation 0)
              (bundle.normalizedPresentation bundle.selectedSlot.succ))
        (bundle.normalizedPoint ∈ FootprintVertices (TileTranslation bundle.normalizedFixed ((⟨(0
            : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1
            (bundle.normalizedPresentation (0 : Fin (4 : ℕ))) (bundle.normalizedPresentation
            bundle.selectedSlot.succ) else BandVectors.1 (bundle.normalizedPresentation
            bundle.selectedSlot.succ) (bundle.normalizedPresentation (0 : Fin (4 : ℕ))))) ↔
            BandPackingSymmetryVectorAction ginv bundle.normalizedPoint ∈ FootprintVertices
            (TileTranslation (BandPackingSymmetryTileAction ginv bundle.normalizedFixed) ((⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑(if BandPackingSymmetryReversesOrientation ginv =
            true then -s - (1 : Fin (4 : ℕ)) + if delta = true then (2 : Fin (4 : ℕ)) else (0 :
            Fin (4 : ℕ)) else s + if delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ)))
            : ℕ) * if Even (↑(if BandPackingSymmetryReversesOrientation ginv = true then -s - (1
            : Fin (4 : ℕ)) + if delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ)) else s
            + if delta = true then (2 : Fin (4 : ℕ)) else (0 : Fin (4 : ℕ))) : ℕ) then
            BandVectors.1 (BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
            (0 : Fin (4 : ℕ))) (BandPackingSymmetryQuadrupleAction ginv
            bundle.normalizedPresentation (if BandPackingSymmetryReversesOrientation ginv = true
            then -bundle.selectedSlot else bundle.selectedSlot).succ) else BandVectors.1
            (BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation (if
            BandPackingSymmetryReversesOrientation ginv = true then -bundle.selectedSlot else
            bundle.selectedSlot).succ) (BandPackingSymmetryQuadrupleAction ginv
            bundle.normalizedPresentation (0 : Fin (4 : ℕ)))))) →
            ((BandPackingSymmetryVectorAction ginv bundle.normalizedPoint = x) →
            (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔ x ∈ FootprintVertices
            (TileTranslation T₀ ((⟨0, 1⟩ : GaussianInt) ^ t'.val * (if Even t'.val then
            BandVectors.1 ((BandPackingSymmetryQuadrupleAction ginv
            bundle.normalizedPresentation) 0) ((BandPackingSymmetryQuadrupleAction ginv
            bundle.normalizedPresentation) (if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot).succ) else BandVectors.1
            ((BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation) (if
            BandPackingSymmetryReversesOrientation ginv then -bundle.selectedSlot else
            bundle.selectedSlot).succ) ((BandPackingSymmetryQuadrupleAction ginv
            bundle.normalizedPresentation) 0))))))))) ) := by
  classical
  intro C T T₀ h h₀ x bundle rightPlacement s hcompanion ginv htileL delta t' ht' oldRight
      hcompanionFootprint hpointInverse
  unfold oldRight
  rw [← hcompanion]
  rw [hpointInverse] at hcompanionFootprint
  simpa [bundle.normalized_fixed_eq, htileL, ht'] using hcompanionFootprint

end MarkedRightAdjacencyGeometry

theorem P5630T1MarkedRightOdometerAdjacencyReduction :
    (∀ (C : BandCircle) (T T₀ : ProtoTile) (h h₀ : PartialOdometer)
        (x : GaussianInt),
      ¬ ((∃ (g : BandPackingSymmetry) (P : FordFareyParameter),
            BandPackingSymmetryCircleAction g
              (FordCircleCoordinate P.p P.q) = C.1.1) ∨
          (∃ (g : BandPackingSymmetry) (K : DiamondParameter),
            BandPackingSymmetryCircleAction g
              (DiamondRecursiveQuadruple K 0) = C.1.1)) →
      RightLatticeAdjacent C T T₀ h h₀ →
      x ∈ h.domain → x ∈ h₀.domain →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ h.domain ∨ y ∈ h₀.domain) →
      ∃ (C' : BandCircle) (T' : ProtoTile) (h' : PartialOdometer)
          (p₀ p' : ℝ × ℝ) (q : Fin 4 → CircleCoordinates)
          (i : Fin 3) (s : Fin 4),
        TileSubodometer C.1.1 C'.1.1 T T' h h' ∧
        PartialOdometerSlope h₀ = some p₀ ∧
        PartialOdometerSlope h' = some p' ∧
        ProperBandQuadruple q ∧ q 0 = C.1.1 ∧ q i.succ = C'.1.1 ∧
        TileCentroid T' - TileCentroid T₀ =
          (1 / 2 : ℝ) • GaussianRealPoint
            ((⟨0, 1⟩ : GaussianInt) ^ s.val *
              (BandVectors.1 (q i.succ) (q 0) +
               BandVectors.1 (q 0) (q i.succ))) ∧
        p'.1 - p₀.1 = ((1 / 2 : ℝ) • GaussianRealPoint
          ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.2 (q i.succ) (q 0) +
             BandVectors.2 (q 0) (q i.succ)))).1 ∧
        p'.2 - p₀.2 = ((1 / 2 : ℝ) • GaussianRealPoint
          ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.2 (q i.succ) (q 0) +
             BandVectors.2 (q 0) (q i.succ)))).2 ∧
        SubtileLatticeAdjacent C C' T₀ T' h₀ h' ∧
        x ∈ h₀.domain ∧ x ∈ h'.domain ∧
        (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
            y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
          y ∈ h₀.domain ∨ y ∈ h'.domain) ∧
        Int.toNat C.1.1.1 + Int.toNat C'.1.1.1 <
          Int.toNat C.1.1.1 + Int.toNat C.1.1.1 ∧
        (¬ (∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
              z = x - 1 - ⟨0, 1⟩ → z ∈ T.cells ∨ z ∈ T₀.cells) ↔
          x ∈ FootprintVertices
            (TileTranslation T₀
              ((⟨0, 1⟩ : GaussianInt) ^ s.val *
                (if Even s.val then BandVectors.1 (q 0) (q i.succ)
                  else BandVectors.1 (q i.succ) (q 0)))))) := by
-- BODY
  intro C T T₀ h h₀ x horbit hadj hx hx₀ hstar
  have markedData := BandPackingSymmetryMarkedDataCovariance
  obtain ⟨bundle, rightPlacement, hrightPlacement⟩ :=
    BandOrderedGeneralRightNormalizedBundleExists
      C T T₀ h h₀ x horbit hadj hx hx₀ hstar
  obtain ⟨selectedEdge, hxSelectedEdge, hselectedEdge, selectedRow⟩ :=
    BandOrderedGeneralRoutedSelectedContact
      bundle.normalizedPresentation bundle.configuration
      bundle.normalizedCircle bundle.normalizedFixed rightPlacement.layout
      rightPlacement.exteriorIndex rightPlacement.centralIndex
      bundle.normalizedPoint bundle.routedDirection
      rightPlacement.exterior_index rightPlacement.central_index
      rightPlacement.exterior_routed_cell rightPlacement.central_routed_cell
      rightPlacement.selected_star
  obtain ⟨row⟩ := selectedRow
  have selectedAdjacency := BandOrderedGeneralRightSelectedAdjacency
    C C T T₀ h h₀ x bundle rightPlacement selectedEdge
    hxSelectedEdge hselectedEdge row
  have outerMarkingCriterion :=
    BandOrderedGeneralRightOuterMarkingCriterion
      C C T T₀ h h₀ x bundle rightPlacement selectedEdge
      hxSelectedEdge hselectedEdge row
  have markedSectorTransport := BandOrderedGeneralMarkedSectorTransport
    C C T T₀ h h₀ x bundle rightPlacement selectedEdge
    hxSelectedEdge hselectedEdge row
  dsimp at selectedAdjacency outerMarkingCriterion markedSectorTransport
  rcases selectedAdjacency with
    ⟨C', p₀, p', s, hC', hsub, hslope₀, hslope', hq, hq₀, hq',
      hcentroid, hslopeRe, hslopeIm, hadj', hxFixed, hxSelected,
      hstar', hsize, hcompanion⟩
  obtain ⟨ginv, hcircleL, hcircleR, hquadL, hquadR, htileL,
    htileR, hvecL, hvecR, hfunL, hfunR, hphase⟩ :=
    (BandPackingSymmetryInversePhaseCancellation.2 bundle.symmetry)
  have hnorm := MarkedRightAdjacencyGeometry.hnorm C T T₀ h h₀ x bundle
  have hfixedSlope : p₀ = bundle.normalizedFixedSlope :=
    Option.some.inj (hslope₀.symm.trans bundle.normalized_fixed_slope)
  rw [hfixedSlope] at hslopeRe hslopeIm
  have inverseAdjacency :=
    SubtileLatticeAdjacentPackingSymmetryTransport ginv
      bundle.normalizedPresentation hq bundle.selectedSlot s
          (MarkedRightAdjacencyGeometry.hparentPositive C T T₀ h h₀ x bundle C' hq')
      bundle.normalizedFixed (bundle.pieces bundle.selectedSlot bundle.selectedSign)
      bundle.normalizedFixedFunction
      (bundle.functions bundle.selectedSlot bundle.selectedSign)
      bundle.normalizedFixedSlope p'
      (MarkedRightAdjacencyGeometry.hfixedOdometer C T T₀ h h₀ x bundle
          (MarkedRightAdjacencyGeometry.hfixedCircleEq C T T₀ h h₀ x bundle hnorm))
      (bundle.piece_odometer bundle.selectedSlot bundle.selectedSign)
      bundle.normalized_fixed_slope hslope'
      hcentroid hslopeRe hslopeIm
  dsimp at inverseAdjacency
  rcases inverseAdjacency with
    ⟨delta, pFixed, pSelected, t', hphaseInv, ht',
      hOFixedInv, hOSelectedInv, hslopeFixedInv, hslopeSelectedInv,
      hcentInv, hslopeReInv, hslopeImInv, hcompat⟩
  have actionCurvature := BandPackingSymmetryCurvature.preserved
  let inversePresentation :=
    BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation
  let inverseSlot := if BandPackingSymmetryReversesOrientation ginv then
      -bundle.selectedSlot else bundle.selectedSlot
  have hinverseProper : ProperBandQuadruple inversePresentation :=
    BandPackingSymmetryProperCovariance ginv bundle.normalizedPresentation hq
  have hinverseCoordinate := MarkedRightAdjacencyGeometry.hinverseCoordinate C T T₀ h h₀ x bundle
      C' hC' ginv
  have hinversePositive := MarkedRightAdjacencyGeometry.hinversePositive C T T₀ h h₀ x bundle C'
      ginv actionCurvature hinverseCoordinate
  let inverseCircle : BandCircle :=
    ⟨⟨inversePresentation inverseSlot.succ,
      ⟨Or.inl hinversePositive, inversePresentation, hinverseProper.1,
        ⟨inverseSlot.succ, rfl⟩⟩⟩, hinversePositive⟩
  have hinverseCircle : inverseCircle.1.1 =
      BandPackingSymmetryCircleAction ginv C'.1.1 := hinverseCoordinate
  let selectedSupport := bundle.pieces bundle.selectedSlot bundle.selectedSign
  let selectedFunction := bundle.functions bundle.selectedSlot bundle.selectedSign
  let T' := BandPackingSymmetryTileAction ginv selectedSupport
  let h' := BandPackingSymmetryPartialOdometerAction ginv selectedFunction
  have hsubInverse := MarkedRightAdjacencyGeometry.hsubInverse C T T₀ h h₀ x markedData bundle C'
      ginv hcircleL htileL hfunL hinverseProper hinversePositive hinverseCircle
      (MarkedRightAdjacencyGeometry.hsubNormalized C T T₀ h h₀ x bundle C' hsub hnorm)
  have inverseDomain := MarkedRightAdjacencyGeometry.inverseDomain C T T₀ h h₀ x bundle ginv hvecL
  have hpoint : BandPackingSymmetryVectorAction bundle.symmetry x =
      bundle.normalizedPoint := bundle.normalized_point_eq.symm
  have hxFixedOriginal := MarkedRightAdjacencyGeometry.hxFixedOriginal C T T₀ h h₀ x bundle
      hxFixed ginv hfunL inverseDomain hpoint
  have hxSelectedOriginal := MarkedRightAdjacencyGeometry.hxSelectedOriginal C T T₀ h h₀ x bundle
      hxSelected ginv inverseDomain hpoint
  have hstarOriginal := MarkedRightAdjacencyGeometry.hstarOriginal C T T₀ h h₀ x bundle hstar'
      ginv hfunL inverseDomain hpoint (BandPackingSymmetryVectorAction.neighborStar)
  have hselectedCoord :
      (BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation)
          (if BandPackingSymmetryReversesOrientation ginv then
            -bundle.selectedSlot else bundle.selectedSlot).succ =
        inverseCircle.1.1 := MarkedRightAdjacencyGeometry.hselectedCoord C T T₀ h h₀ x bundle C'
            hq' ginv hinverseProper hinversePositive hinverseCircle
  have hOSelectedOriginal : TileOdometer inverseCircle.1.1 T' h' := by
    simpa [hselectedCoord, T', h'] using hOSelectedInv
  have hslopeFixedOriginal : PartialOdometerSlope h₀ = some pFixed := by
    simpa [bundle.normalized_fixed_function_eq, hfunL] using hslopeFixedInv
  have hcentOriginal := hcentInv
  rw [bundle.normalized_fixed_eq, htileL] at hcentOriginal
  have hrootCoord := MarkedRightAdjacencyGeometry.hrootCoord C T T₀ h h₀ x bundle ginv hcircleL
      hnorm
  have hnewAdj := MarkedRightAdjacencyGeometry.hnewAdj C T T₀ h h₀ x bundle hq ginv pFixed
      pSelected t' hslopeSelectedInv hslopeReInv hslopeImInv hinverseProper hinversePositive
      hselectedCoord (MarkedRightAdjacencyGeometry.hOFixedOriginal C T T₀ h h₀ x bundle ginv
      htileL hfunL hOFixedInv (MarkedRightAdjacencyGeometry.hrootAction C T T₀ h h₀ x bundle ginv
      hcircleL hnorm)) hOSelectedOriginal hslopeFixedOriginal hcentOriginal hrootCoord
  have actionCurvature := BandPackingSymmetryCurvature.preserved
  have hsizeOriginal := MarkedRightAdjacencyGeometry.hsizeOriginal C T T₀ h h₀ x bundle C' hsize
      ginv hnorm actionCurvature hinverseProper hinversePositive hinverseCircle
  have hcoverOriginal :
      (∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨ z = x - 1 - ⟨0, 1⟩ →
        z ∈ T.cells ∨ z ∈ T₀.cells) ↔
      (∀ z, z = bundle.normalizedPoint ∨ z = bundle.normalizedPoint - 1 ∨
        z = bundle.normalizedPoint - ⟨0, 1⟩ ∨ z = bundle.normalizedPoint - 1 - ⟨0, 1⟩ →
        z ∈ bundle.normalizedRoot.cells ∨ z ∈ bundle.normalizedFixed.cells) := by
    rw [MarkedRightAdjacencyGeometry.coverShape, MarkedRightAdjacencyGeometry.coverShape]
    simpa [bundle.normalized_point_eq, bundle.normalized_root_eq,
      bundle.normalized_fixed_eq] using markedData.2.1 bundle.symmetry x T T₀
  have hcompanionCov :=
    markedData.2.2 ginv bundle.normalizedPresentation hq
      bundle.selectedSlot s delta hphaseInv bundle.normalizedFixed
      bundle.normalizedPoint
  dsimp at hcompanionCov
  rcases hcompanionCov with ⟨hcompanionTile, hcompanionFootprint⟩
  refine ⟨inverseCircle, T', h', pFixed, pSelected,
    BandPackingSymmetryQuadrupleAction ginv bundle.normalizedPresentation,
    (if BandPackingSymmetryReversesOrientation ginv then
      -bundle.selectedSlot else bundle.selectedSlot), t', ?_⟩
  refine ⟨hsubInverse, hslopeFixedOriginal, hslopeSelectedInv,
    BandPackingSymmetryProperCovariance ginv bundle.normalizedPresentation hq,
    hrootCoord, hselectedCoord, hcentOriginal, hslopeReInv, hslopeImInv,
    hnewAdj, hxFixedOriginal, hxSelectedOriginal, hstarOriginal,
    hsizeOriginal, (not_congr hcoverOriginal).trans (outerMarkingCriterion.trans
        (MarkedRightAdjacencyGeometry.hmarkTransport C T T₀ h h₀ x bundle rightPlacement s
        hcompanion ginv htileL delta t' ht' hcompanionFootprint
        (MarkedRightAdjacencyGeometry.hpointInverse C T T₀ h h₀ x bundle ginv hvecL hpoint)))⟩

end ApollonianSuperharmonic

end
