/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.PartialOdometerEquality
public import LeanPool.ApollonianSuperharmonic.BandLayoutParentNonempty
public import LeanPool.ApollonianSuperharmonic.BandParentCentroidComparison

public import LeanPool.ApollonianSuperharmonic.P4261T1PlacedOdometer
public import LeanPool.ApollonianSuperharmonic.TileSubodometerLiteralDecompositionPiece
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile

-- [TABLET NODE: P4261T1CentralCoordinates]

/-!
# P4261T1CentralCoordinates

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CentralCoordinateGeometry

private theorem hcurv₀ :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), (BandOrderedGeneralLayoutCertificate q cfg C₀ T₀) →
            (1 < C₀.1.1.1) ) := by
  classical
  intro q cfg C₀ T₀ cert
  have h := cfg.childLarge
  rw [cert.child_eq] at h
  omega

private theorem hvector :
    (by
      classical
      exact
        ∀ (q q' : Fin (4 : ℕ) → CircleCoordinates)
          (i' r : Fin (3 : ℕ)),
          (∀ (j : Fin (3 : ℕ)), q' j.succ = q (j + r).succ) →
            let j := i' + r;
            BandVectors.1 (q' (i' + (2 : Fin (3 : ℕ))).succ)
                (q' (i' + (1 : Fin (3 : ℕ))).succ) =
              BandVectors.1 (q (j + (2 : Fin (3 : ℕ))).succ)
                (q (j + (1 : Fin (3 : ℕ))).succ)) := by
  classical
  intro q q' i' r hrotate j
  rw [hrotate (i' + 2), hrotate (i' + 1)]; dsimp [j]; fin_cases r <;> fin_cases i' <;> rfl

private abbrev hsCent :=
  BandParentCentroidComparison.centroidEquality

private theorem hbandSelected :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (q' : Fin (4 : ℕ) → CircleCoordinates), ∀ (i' : Fin
            (3 : ℕ)), ∀ (hs : Bool), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hs' : Fin (3 :
            ℕ) → Bool → PartialOdometer), (∀ (j : Fin (3 : ℕ)), ∀ (t : Bool), TileOdometer (q'
            j.succ) (S' j t) (hs' j t)) → (∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        (q' i'.succ = q j.succ) → (BandPrototile (q j.succ) (S' i' hs))) ) := by
  classical
  intro q q' i' hs S' hs' hchild' r j hparent
  rw [← hparent]
  exact TileOdometerBandPrototile _ _ _ (hchild' i' hs)

private theorem hlayoutCent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (i' : Fin (3 : ℕ)), ∀ (hs : Bool), ∀ (R : Fin (3 : ℕ) → Bool → ProtoTile),
            (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (R i s) - TileCentroid T₀ = (if s =
            true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q
            (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)) -
            (-(GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin
            (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ))).1))) → (∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        (BandSubtileOccurrence q T₀ j hs (cert.P j hs)) → (TileCentroid (R j hs) = TileCentroid
            (cert.P j hs))) ) := by
  classical
  intro q cfg C₀ T₀ cert i' hs R hrootCent r j hlayoutOcc
  calc
    TileCentroid (R j hs) =
        (TileCentroid (R j hs) - TileCentroid T₀) + TileCentroid T₀ := by abel
    _ = (TileCentroid (cert.P j hs) - TileCentroid T₀) + TileCentroid T₀ := by
      rw [hrootCent j hs, hlayoutOcc.2.2]
    _ = TileCentroid (cert.P j hs) := by abel

private theorem hselectedNonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (T : ProtoTile), ∀ (i' : Fin (3 : ℕ)), ∀ (hs : Bool), ∀ (S' : Fin (3 : ℕ) →
            Bool → ProtoTile), (T.cells = (S' i' hs).cells) → (∀ (R : Fin (3 : ℕ) → Bool →
            ProtoTile), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        ((S' i' hs).cells = (R j hs).cells) → (((R j hs).cells = (cert.P j hs).cells) → (((cert.P
            j hs).cells.Nonempty) → (T.cells.Nonempty)))) ) := by
  classical
  intro q cfg C₀ T₀ cert T i' hs S' hselectedCells R r j hselectedCellsFresh hlayoutCells
      hparentNonempty
  rw [hselectedCells, hselectedCellsFresh, hlayoutCells]
  exact hparentNonempty

private theorem hcellsT :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (T : ProtoTile), ∀ (i' : Fin (3 : ℕ)), ∀ (hs : Bool), ∀ (S' : Fin (3 : ℕ) →
            Bool → ProtoTile), (T.cells = (S' i' hs).cells) → (∀ (R : Fin (3 : ℕ) → Bool →
            ProtoTile), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        ((S' i' hs).cells = (R j hs).cells) → (((R j hs).cells = (cert.P j hs).cells) → (T.cells
            = (cert.P j hs).cells))) ) := by
  classical
  intro q cfg C₀ T₀ cert T i' hs S' hselectedCells R r j hselectedCellsFresh hlayoutCells
  calc
    T.cells = (S' i' hs).cells := hselectedCells
    _ = (R j hs).cells := hselectedCellsFresh
    _ = (cert.P j hs).cells := hlayoutCells

private theorem hfootT :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (T : ProtoTile), ∀ (i' : Fin (3 : ℕ)), ∀ (hs : Bool), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        ((cert.P j hs).cells.Nonempty) → ((T.cells.Nonempty) → ((T.cells = (cert.P j hs).cells) →
            (FootprintVertices T = FootprintVertices (cert.P j hs)))) ) := by
  classical
  intro q cfg C₀ T₀ cert T i' hs r j hparentNonempty hselectedNonempty hcellsT
  simp only [FootprintVertices, ite_eq_left hselectedNonempty, ite_eq_left hparentNonempty]
  rw [hcellsT]

private theorem hchildPositive :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → ((BandCircle) →
            (∀ (i' : Fin (3 : ℕ)), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        0 < (q j.succ).1)) ) := by
  classical
  intro q cfg C₀ i' r j
  have hnonneg := (ProperBandCurvatureStructure q cfg.proper).2.1 j
  have hne := cfg.noLine j.succ
  omega

private theorem hdomainT :
    (by
      classical
      exact
        ∀ (C₀ : BandCircle), ∀ (T₀ : ProtoTile), ∀ (h₀ : PartialOdometer), ∀ (C : BandCircle), ∀
            (T : ProtoTile), ∀ (h : PartialOdometer), (TileSubodometer C₀.1.1 C.1.1 T₀ T h₀ h) →
            ((h.domain : Set GaussianInt) = FootprintVertices T) ) := by
  classical
  intro C₀ T₀ h₀ C T h hsub
  exact PositiveCurvatureTileOdometerDomain C.1.1 T h C.property
      hsub.2.1

private theorem hdomainFresh :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i' : Fin (3 : ℕ)), ∀ (hs : Bool), ∀ (R : Fin (3 :
            ℕ) → Bool → ProtoTile), ∀ (rH : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3
            : ℕ)), ∀ (s : Bool), TileOdometer (q i.succ) (R i s) (rH i s)) → (∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        (0 < (q j.succ).1) → (((rH j hs).domain : Set GaussianInt) = FootprintVertices (R j hs)))
            ) := by
  classical
  intro q i' hs R rH hrootChildren r j hchildPositive
  exact PositiveCurvatureTileOdometerDomain (q j.succ) (R j hs) (rH j hs)
      hchildPositive (hrootChildren j hs)

private theorem hdomainSelected :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (q' : Fin (4 : ℕ) → CircleCoordinates), ∀ (i' : Fin
            (3 : ℕ)), ∀ (hs : Bool), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (hs' : Fin (3 :
            ℕ) → Bool → PartialOdometer), (∀ (j : Fin (3 : ℕ)), ∀ (t : Bool), TileOdometer (q'
            j.succ) (S' j t) (hs' j t)) → (∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        (q' i'.succ = q j.succ) → ((0 < (q j.succ).1) → (((hs' i' hs).domain : Set GaussianInt) =
            FootprintVertices (S' i' hs)))) ) := by
  classical
  intro q q' i' hs S' hs' hchild' r j hparent hchildPositive
  exact PositiveCurvatureTileOdometerDomain (q j.succ) (S' i' hs) (hs' i' hs)
      hchildPositive (by rw [← hparent]; exact hchild' i' hs)

private theorem hdomainSelFresh :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (i' : Fin (3 : ℕ)), ∀ (hs : Bool), ∀ (S' : Fin (3 : ℕ) → Bool →
            ProtoTile), ∀ (hs' : Fin (3 : ℕ) → Bool → PartialOdometer), (T.cells = (S' i'
            hs).cells) → (∀ (R : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (rH : Fin (3 : ℕ) → Bool →
            PartialOdometer), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        ((S' i' hs).cells = (R j hs).cells) → ((T.cells.Nonempty) → ((((rH j hs).domain : Set
            GaussianInt) = FootprintVertices (R j hs)) → ((((hs' i' hs).domain : Set GaussianInt)
            = FootprintVertices (S' i' hs)) → (((hs' i' hs).domain : Set GaussianInt) = (rH j
            hs).domain))))) ) := by
  classical
  intro T i' hs S' hs' hselectedCells R rH r j hselectedCellsFresh hselectedNonempty hdomainFresh
      hdomainSelected
  have hneSelected : (S' i' hs).cells.Nonempty := by
    rw [← hselectedCells]
    exact hselectedNonempty
  have hneFresh : (R j hs).cells.Nonempty := by
    rw [← hselectedCellsFresh]
    exact hneSelected
  rw [hdomainSelected, hdomainFresh]
  simp only [FootprintVertices, ite_eq_left hneSelected, ite_eq_left hneFresh]
  rw [hselectedCellsFresh]

private theorem hdomainSuppliedFresh :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (i' : Fin (3 : ℕ)), ∀ (hs : Bool), ∀ (hs' : Fin (3 : ℕ) → Bool
            → PartialOdometer), ((↑h.domain : Set GaussianInt) = (↑(hs' i' hs).domain : Set
            GaussianInt)) → (∀ (rH : Fin (3 : ℕ) → Bool → PartialOdometer), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        (((hs' i' hs).domain : Set GaussianInt) = (rH j hs).domain) → ((h.domain : Set
            GaussianInt) = (rH j hs).domain)) ) := by
  classical
  intro h i' hs hs' hselectedDomain rH r j hdomainSelFresh
  calc
    (h.domain : Set GaussianInt) = (hs' i' hs).domain := hselectedDomain
    _ = (rH j hs).domain := hdomainSelFresh

private theorem hvalueSuppliedFresh :
    (by
      classical
      exact
        ∀ (h₀ : PartialOdometer), ∀ (h : PartialOdometer), ∀ (i' : Fin (3 : ℕ)), ∀ (hs : Bool), ∀
            (hs' : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (j : Fin (3 : ℕ)), ∀ (t : Bool), ∀ x
            ∈ (hs' j t).domain, h₀.value x = (hs' j t).value x) → (((↑h.domain : Set GaussianInt)
            = (↑(hs' i' hs).domain : Set GaussianInt)) → ((∀ x ∈ h.domain, h.value x = (hs' i'
            hs).value x) → (∀ (rH : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)),
            ∀ (s : Bool), ∀ x ∈ (rH i s).domain, h₀.value x = (rH i s).value x) → (∀ (r : Fin (3
            : ℕ)),
        let j : Fin 3 := i' + r
        ((h.domain : Set GaussianInt) = (rH j hs).domain) → (∀ x, h.value x = (rH j hs).value
            x))))) ) := by
  classical
  intro h₀ h i' hs hs' hvalue' hselectedDomain hselectedValue rH hrootValue r j
      hdomainSuppliedFresh x
  by_cases hx : x ∈ h.domain
  · have hx' : x ∈ (hs' i' hs).domain := by
      have hselDomFin : h.domain = (hs' i' hs).domain :=
        Finset.coe_injective hselectedDomain
      rw [hselDomFin] at hx
      exact hx
    have hv₁ := hselectedValue x hx
    have hv₂ := hvalue' i' hs x hx'
    have hxFresh : x ∈ (rH j hs).domain := by
      have hdomFin : h.domain = (rH j hs).domain :=
        Finset.coe_injective hdomainSuppliedFresh
      rw [hdomFin] at hx
      exact hx
    have hv₃ := hrootValue j hs x hxFresh
    exact hv₁.trans (hv₂.symm.trans hv₃)
  · have hxFresh : x ∉ (rH j hs).domain := by
      intro hxFresh
      exact hx ((Set.ext_iff.mp hdomainSuppliedFresh x).mpr hxFresh)
    rw [h.value_outside x hx, (rH j hs).value_outside x hxFresh]

private theorem centralLabel :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀),
        let slot : SixSubtileLabel → Fin 3 × Bool := fun l => match l with
          | .A => (0, true)
          | .B => (0, false)
          | .C => (1, true)
          | .D => (1, false)
          | .E => (2, true)
          | .F => (2, false)
        ∀ (k : Fin 3), ∀ (t : Bool), ∃ l : SixSubtileLabel, slot l = (k, t) ∧
            SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨l, 0, 0⟩ = TileTranslation
            (cert.P k t) 0 ) := by
  classical
  intro q cfg C₀ T₀ cert slot k t
  fin_cases k <;> cases t
  all_goals first
    | refine ⟨.A, And.intro rfl ?_⟩
    | refine ⟨.B, And.intro rfl ?_⟩
    | refine ⟨.C, And.intro rfl ?_⟩
    | refine ⟨.D, And.intro rfl ?_⟩
    | refine ⟨.E, And.intro rfl ?_⟩
    | refine ⟨.F, And.intro rfl ?_⟩
  all_goals simp [SubtileOccurrenceInterpretation]

private theorem hoccTile :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (i' : Fin (3 : ℕ)), ∀ (hs : Bool), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        ∀ (l : SixSubtileLabel), (SubtileOccurrenceInterpretation cert.P cert.u cert.v ⟨l, (0 :
            ℤ), (0 : ℤ)⟩ = TileTranslation (cert.P j hs) (0 : GaussianInt)) → (
        let b : PeriodicSubtileIndex := ⟨l, 0, 0⟩
        SubtileOccurrenceInterpretation cert.P cert.u cert.v b = cert.P j hs) ) := by
  classical
  intro q cfg C₀ T₀ cert i' hs r j l hocc b
  rw [hocc]
  cases cert.P j hs with
  | mk cells anchor =>
    change ProtoTile.mk (cells.image (GaussianTranslation 0))
        (GaussianTranslation 0 anchor) = ProtoTile.mk cells anchor
    congr 1
    · ext x
      simp [GaussianTranslation]
    · simp [GaussianTranslation]

private theorem hoccCells :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (i' : Fin (3 : ℕ)), ∀ (hs : Bool), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        ∀ (l : SixSubtileLabel),
        let b : PeriodicSubtileIndex := ⟨l, 0, 0⟩
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v b = cert.P j hs) →
            ((SubtileOccurrenceInterpretation cert.P cert.u cert.v b).cells = (cert.P j
            hs).cells) ) := by
  classical
  intro q cfg C₀ T₀ cert i' hs r j l b hoccTile
  rw [hoccTile]

private theorem hoccCent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (i' : Fin (3 : ℕ)), ∀ (hs : Bool), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        ∀ (l : SixSubtileLabel),
        let b : PeriodicSubtileIndex := ⟨l, 0, 0⟩
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v b = cert.P j hs) → (TileCentroid
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v b) = TileCentroid (cert.P j
            hs)) ) := by
  classical
  intro q cfg C₀ T₀ cert i' hs r j l b hoccTile
  rw [hoccTile]

private theorem hoccFoot :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T₀ : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T₀), ∀ (i' : Fin (3 : ℕ)), ∀ (hs : Bool), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        ∀ (l : SixSubtileLabel),
        let b : PeriodicSubtileIndex := ⟨l, 0, 0⟩
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v b = cert.P j hs) →
            (FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v b) =
            FootprintVertices (cert.P j hs)) ) := by
  classical
  intro q cfg C₀ T₀ cert i' hs r j l b hoccTile
  rw [hoccTile]

private theorem hslopeOffset :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i' : Fin (3 : ℕ)), ∀ (hs : Bool), ∀ (r : Fin (3 : ℕ)),
        let j : Fin 3 := i' + r
        ∀ (p : ℝ × ℝ), ∀ (ps : ℝ × ℝ), (ps.1 - p.1 = (if hs = true then (1 : ℝ) else (-1 : ℝ)) *
            (1 / 2 : ℝ) * ((↑(BandVectors.2 (q (j + (2 : Fin (3 : ℕ))).succ) (q (j + (1 : Fin (3
            : ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (q (j + (2 : Fin (3 : ℕ))).succ) (q (j + (1
            : Fin (3 : ℕ))).succ)).im : ℝ))) → ((ps.2 - p.2 = (if hs = true then (1 : ℝ) else (-1
            : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (q (j + (2 : Fin (3 : ℕ))).succ) (q (j + (1 :
            Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (q (j + (2 : Fin (3 : ℕ))).succ) (q
            (j + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (ps - p = (if hs = true then (1 : ℝ) else
            -1) • P4250T1SlopeOffset (BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))))) )
            := by
  classical
  intro q i' hs r j p ps hpx hpy
  apply Prod.ext
  · change ps.1 - p.1 = (if hs = true then (1 : ℝ) else -1) *
      ((((BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))).re : ℝ) -
        ((BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))).im : ℝ)) / 2)
    rw [hpx]
    ring
  · change ps.2 - p.2 = (if hs = true then (1 : ℝ) else -1) *
      ((((BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))).im : ℝ) +
        ((BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))).re : ℝ)) / 2)
    rw [hpy]
    ring

end CentralCoordinateGeometry

theorem P4261T1CentralCoordinates
    {q : Fin 4 → CircleCoordinates} {cfg : BandOrderedGeneralConfiguration q}
    {C₀ : BandCircle} {T₀ : ProtoTile}
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T₀)
    (h₀ : PartialOdometer) (C : BandCircle) (T : ProtoTile) (h : PartialOdometer)
    (hsub : TileSubodometer C₀.1.1 C.1.1 T₀ T h₀ h) :
    ∃ b : PeriodicSubtileIndex, b.first = 0 ∧ b.second = 0 ∧
      Nonempty (P4261T1PlacedOdometer cert h₀ C T h b) := by
-- BODY
  classical
  have hroot : TileOdometer C₀.1.1 T₀ h₀ := hsub.1
  have hcurv₀ : 1 < C₀.1.1.1 := CentralCoordinateGeometry.hcurv₀ q cfg C₀ T₀ cert
  obtain ⟨q', i', hs, S', hs', hq', hq'₀, hq'i', hband₀,
    hchild', hcells', hfoot', hcent', hdom', hvalue', hcompat', hslope',
    hselectedCells, hselectedDomain, hselectedValue⟩ :=
    TileSubodometerLiteralDecompositionPiece C₀ C T₀ T h₀ h
      hcurv₀ hsub
  obtain ⟨R, rH, hbandRoot, hrootChildren, hrootCells, hrootFoot,
    hrootCent, hrootDomain, hrootValue, hrootCompat, hrootSlope⟩ :=
    TileOdometerReindexedDecomposition q cfg.proper T₀ h₀
      (by simpa [cert.child_eq] using hcurv₀) (by simpa [cert.child_eq] using hroot)
  obtain ⟨r, hrotate, _⟩ :=
    BandPredecessorNoCollision q q' cfg.proper hq'
      (by rw [cert.child_eq, hq'₀])
  let j : Fin 3 := i' + r
  have hparent : q' i'.succ = q j.succ := by
    simpa [j] using hrotate i'
  have hvector := CentralCoordinateGeometry.hvector q q' i' r hrotate
  have hsCent := CentralCoordinateGeometry.hsCent q T₀ q' i' hs S' hcent' R hrootCent r hvector
  have hbandSelected := CentralCoordinateGeometry.hbandSelected q q' i' hs S' hs' hchild' r hparent
  have hbandFresh : BandPrototile (q j.succ) (R j hs) :=
    TileOdometerBandPrototile _ _ _ (hrootChildren j hs)
  have hselectedCellsFresh : (S' i' hs).cells = (R j hs).cells :=
    (BandPrototileCentroidUnique (q j.succ) _ _ hbandSelected hbandFresh hsCent).1
  have hlayoutOcc := cert.outer_occurrence j hs
  have hbandLayout : BandPrototile (q j.succ) (cert.P j hs) := hlayoutOcc.1
  have hlayoutCent := CentralCoordinateGeometry.hlayoutCent q cfg C₀ T₀ cert i' hs R hrootCent r
      hlayoutOcc
  have hlayoutCells : (R j hs).cells = (cert.P j hs).cells :=
    (BandPrototileCentroidUnique (q j.succ) _ _ hbandFresh hbandLayout hlayoutCent).1
  have hparentNonempty : (cert.P j hs).cells.Nonempty :=
      BandLayoutParentNonempty.cells q cfg C₀ T₀ cert (i' + r) hs
  have hselectedNonempty := CentralCoordinateGeometry.hselectedNonempty q cfg C₀ T₀ cert T i' hs
      S' hselectedCells R r hselectedCellsFresh hlayoutCells hparentNonempty
  have hcellsT : T.cells = (cert.P j hs).cells := CentralCoordinateGeometry.hcellsT q cfg C₀ T₀
      cert T i' hs S' hselectedCells R r hselectedCellsFresh hlayoutCells
  have hfootT : FootprintVertices T = FootprintVertices (cert.P j hs) :=
      CentralCoordinateGeometry.hfootT q cfg C₀ T₀ cert T i' hs r hparentNonempty
      hselectedNonempty hcellsT
  have hchildPositive := CentralCoordinateGeometry.hchildPositive q cfg C₀ i' r
  have hdomainT : (h.domain : Set GaussianInt) = FootprintVertices T :=
      CentralCoordinateGeometry.hdomainT C₀ T₀ h₀ C T h hsub
  have hdomainFresh := CentralCoordinateGeometry.hdomainFresh q i' hs R rH hrootChildren r
      hchildPositive
  have hdomainSelected := CentralCoordinateGeometry.hdomainSelected q q' i' hs S' hs' hchild' r
      hparent hchildPositive
  have hdomainSelFresh := CentralCoordinateGeometry.hdomainSelFresh T i' hs S' hs' hselectedCells
      R rH r hselectedCellsFresh hselectedNonempty hdomainFresh hdomainSelected
  have hdomainSuppliedFresh := CentralCoordinateGeometry.hdomainSuppliedFresh h i' hs hs'
      hselectedDomain rH r hdomainSelFresh
  have hvalueSuppliedFresh := CentralCoordinateGeometry.hvalueSuppliedFresh h₀ h i' hs hs'
      hvalue' hselectedDomain hselectedValue rH hrootValue r hdomainSuppliedFresh
  have hfunEq : h = rH j hs := PartialOdometerEquality.extensionality h (rH (i' + r) hs)
      hdomainSuppliedFresh hvalueSuppliedFresh
  let slot : SixSubtileLabel → Fin 3 × Bool := fun l => match l with
    | .A => (0, true)
    | .B => (0, false)
    | .C => (1, true)
    | .D => (1, false)
    | .E => (2, true)
    | .F => (2, false)
  have centralLabel := CentralCoordinateGeometry.centralLabel q cfg C₀ T₀ cert
  obtain ⟨l, hl, hocc⟩ := centralLabel j hs
  let b : PeriodicSubtileIndex := ⟨l, 0, 0⟩
  have hoccTile := CentralCoordinateGeometry.hoccTile q cfg C₀ T₀ cert i' hs r l hocc
  have hoccCells : (SubtileOccurrenceInterpretation cert.P cert.u cert.v b).cells =
      (cert.P j hs).cells := CentralCoordinateGeometry.hoccCells q cfg C₀ T₀ cert i' hs r l hoccTile
  have hoccCent : TileCentroid (SubtileOccurrenceInterpretation cert.P cert.u cert.v b) =
      TileCentroid (cert.P j hs) := CentralCoordinateGeometry.hoccCent q cfg C₀ T₀ cert i' hs r l
          hoccTile
  have hoccFoot : FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v b) =
      FootprintVertices (cert.P j hs) := CentralCoordinateGeometry.hoccFoot q cfg C₀ T₀ cert i'
          hs r l hoccTile
  have hrootSlopeData := hrootSlope j hs
  have hrootParentPositive : 0 < (q j.succ).1 := hchildPositive
  rcases hrootSlopeData with hzero | ⟨p, ps, hp, hps, hpx, hpy⟩
  · omega
  have hslopeOffset : ps - p =
      (if hs = true then (1 : ℝ) else -1) •
        P4250T1SlopeOffset (BandVectors.2 (q ((j + 2).succ)) (q ((j + 1).succ))) :=
            CentralCoordinateGeometry.hslopeOffset q i' hs r p ps hpx hpy
  have hcentroidT : TileCentroid T = TileCentroid (cert.P j hs) := by
    simp [TileCentroid, hparentNonempty, hcellsT]
  have hlIndex : (slot l).1 = j := congrArg Prod.fst hl
  have hlSign : (slot l).2 = hs := congrArg Prod.snd hl
  have hCeq : C.1.1 = q j.succ := hq'i'.symm.trans hparent
  refine ⟨b, ?_, ?_, ⟨?_⟩⟩
  · simp [b]
  · simp [b]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change C.1.1 = q (slot l).1.succ
      simpa only [hlIndex] using hCeq
    · exact hsub.2.1
    · rw [hcellsT, hoccCells]
    · rw [hcentroidT, hoccCent]
    · rw [hdomainT, hfootT, hoccFoot]
    · exact p
    · exact ps
    · exact hp
    · simpa [hfunEq] using hps
    · change ps - p =
        (if (slot l).2 then (1 : ℝ) else -1) •
          P4250T1SlopeOffset
            (BandVectors.2 (q (((slot l).1 + 2).succ))
              (q (((slot l).1 + 1).succ))) +
        GaussianRealPoint
          ((b.first : GaussianInt) * BandVectors.2 (q 0) (q 1) +
            (b.second : GaussianInt) * BandVectors.2 (q 0) (q 2))
      simp [b, hlIndex, hlSign, hslopeOffset, GaussianRealPoint]

end ApollonianSuperharmonic

end
