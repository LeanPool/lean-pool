/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileArea
public import LeanPool.ApollonianSuperharmonic.TileCellComplement
public import LeanPool.ApollonianSuperharmonic.FordTileGeometry
public import LeanPool.ApollonianSuperharmonic.P4638T1AntipodalContactArcs
public import LeanPool.ApollonianSuperharmonic.P4638T1ContactStarCoverage
public import LeanPool.ApollonianSuperharmonic.P4638T1EmptyCurvature
public import LeanPool.ApollonianSuperharmonic.P4638T1EmptyFordLocalization
public import LeanPool.ApollonianSuperharmonic.P4638T1FordIncidentCells
public import LeanPool.ApollonianSuperharmonic.P4638T1MidpointReflection

-- [TABLET NODE: IsolatedPrecursorCoverage]

/-!
# IsolatedPrecursorCoverage

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem IsolatedPrecursorCoverage :
    ∀ (q : Fin 4 -> CircleCoordinates), ∀ (r : Fin 4 -> CircleCoordinates), (ProperBandQuadruple
        q) → ((ProperBandQuadruple r) → ((r 0 = q 1) → ((r 2 = q 2) → ((r 3 = q 3) → (∀ (x : Real
        × Real), ∀ (P : Fin 3 -> Bool -> ProtoTile), ∀ (Q : Fin 3 -> Bool -> ProtoTile), ∀ (S :
        Fin 3 -> Bool -> ProtoTile), (forall i s, BandPrototile (q i.succ) (P i s)) → ((forall i
        s, BandPrototile (r i.succ) (Q i s)) → ((forall i s, BandPrototile (r i.succ) (S i s)) →
        ((forall i s,
      TileCentroid (P i s) - x =
        (if s = true then (1 : Real) else -1) •
          ((1 / 2 : Real) •
            (GaussianRealPoint
                (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
              (-((GaussianRealPoint
                  (BandVectors.1 (q ((i + 2).succ))
                    (q ((i + 1).succ)))).2),
                (GaussianRealPoint
                  (BandVectors.1 (q ((i + 2).succ))
                    (q ((i + 1).succ)))).1)))) → ((forall i s,
      TileCentroid (Q i s) - TileCentroid (P 0 true) =
        (if s = true then (1 : Real) else -1) •
          ((1 / 2 : Real) •
            (GaussianRealPoint
                (BandVectors.1 (r ((i + 2).succ)) (r ((i + 1).succ))) -
              (-((GaussianRealPoint
                  (BandVectors.1 (r ((i + 2).succ))
                    (r ((i + 1).succ)))).2),
                (GaussianRealPoint
                  (BandVectors.1 (r ((i + 2).succ))
                    (r ((i + 1).succ)))).1)))) → ((forall i s,
      TileCentroid (S i s) - TileCentroid (P 0 false) =
        (if s = true then (1 : Real) else -1) •
          ((1 / 2 : Real) •
            (GaussianRealPoint
                (BandVectors.1 (r ((i + 2).succ)) (r ((i + 1).succ))) -
              (-((GaussianRealPoint
                  (BandVectors.1 (r ((i + 2).succ))
                    (r ((i + 1).succ)))).2),
                (GaussianRealPoint
                  (BandVectors.1 (r ((i + 2).succ))
                    (r ((i + 1).succ)))).1)))) → ((forall i s, (Q i s).cells ⊆ (P 0 true).cells)
                        → ((forall i s, (S i s).cells ⊆ (P 0 false).cells) → ((forall i s,
      FootprintVertices (Q i s) ⊆ FootprintVertices (P 0 true)) → ((forall i s,
      FootprintVertices (S i s) ⊆ FootprintVertices (P 0 false)) → (((Q 0 false).cells = (S 0
          true).cells) → (((Q 0 false).cells = ∅ ->
      (Q 0 false).anchor = (S 0 true).anchor) → ((LatticeTile (TileCellComplement (P 0 true) (Q 0
          false)) ∧
      TileTouching (TileCellComplement (P 0 true) (Q 0 false)) (Q 0 false)) → ((LatticeTile
          (TileCellComplement (P 0 false) (S 0 true)) ∧
      TileTouching (TileCellComplement (P 0 false) (S 0 true)) (S 0 true)) →
          ((CentrallyReflectedAt (TileCentroid (Q 0 false))
      (TileCellComplement (P 0 true) (Q 0 false))
      (TileCellComplement (P 0 false) (S 0 true))) → ((QuarterTurnSymmetric (Q 0 false)) → (((Q 0
          false).cells ≠ ∅ -> LatticeTile (Q 0 false)) → (((Q 1 true).cells ≠ ∅) → (((S 2
          false).cells ≠ ∅) → (((Q 2 true).cells ≠ ∅) → (((S 1 false).cells ≠ ∅) →
          ((TouchingTriple (Q 1 true) (S 2 false) (Q 0 false)) → ((TouchingTriple (Q 2 true) (S 1
          false) (Q 0 false)) → ((TouchingTriple (Q 1 true) (S 2 false) (P 1 true)) →
          ((TouchingTriple (Q 1 true) (P 1 true) (P 2 false)) → ((¬ (TileArea (P 2 false) = 1 ∧
          TileArea (P 1 true) = 1)) → ((Disjoint
      (TileCellComplement (P 0 true) (Q 0 false)).cells
      (TileCellComplement (P 0 false) (S 0 true)).cells) → ((∀ y ∈ FootprintVertices (Q 0 false),
          ∀ a : GaussianInt,
      y ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) ->
        a ∈ (P 0 true).cells ∨ a ∈ (P 0 false).cells) ∧
    Nonempty (PrecursorBoundaryArcData
      (TileCellComplement (P 0 true) (Q 0 false))
      (TileCellComplement (P 0 false) (S 0 true))
      (Q 0 false) (S 0 true) (Q 1 true) (S 2 false)
      (Q 2 true) (S 1 false)) ∧
    ((Q 0 false).cells = ∅ -> (r 1).1 = 0))))))))))))))))))))))))))))))))) := by
  intro q r hq hr hr0 hr2 hr3 x P Q S hP hQ hS hPcent hQcent hScent hQcells hScells hQfoot hSfoot
      hcommon hcommonAnchor hcomplementPlus hcomplementMinus hcentral hOsym hOlattice hQnonempty
      hSnonempty hQnonemptySecond hSnonemptySecond hcross hcrossSecond houterCross houterChain
      hnotExceptional hcomplementDisjoint
-- BODY
  classical
  have commonCent : TileCentroid (Q 0 false) = TileCentroid (S 0 true) := by
    by_cases hn : (Q 0 false).cells.Nonempty
    · have hs : (S 0 true).cells.Nonempty := hcommon ▸ hn
      simp only [TileCentroid, ite_eq_left hn, ← hcommon]
    · have he : (Q 0 false).cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have hs : (S 0 true).cells = ∅ := hcommon.symm.trans he
      simp [TileCentroid, he, hs, hcommonAnchor he]
  have childComplement (A O U : ProtoTile) (hn : U.cells ≠ ∅)
      (hsub : U.cells ⊆ A.cells)
      (ht : TileTouching U O ∨ TileTouching O U) :
      U.cells ⊆ (TileCellComplement A O).cells := by
    by_cases he : O.cells = ∅
    · simpa [TileCellComplement, he] using hsub
    have hd : Disjoint U.cells O.cells := by
      rcases ht with ht | ht
      · rcases ht with ht | ht | ht
        · exact ht.2.2.1
        · exact (hn ht.1).elim
        · exact (he ht.1).elim
      · rcases ht with ht | ht | ht
        · exact ht.2.2.1.symm
        · exact (he ht.1).elim
        · exact (hn ht.1).elim
    intro a ha
    exact Finset.mem_sdiff.mpr ⟨hsub ha, Finset.disjoint_left.mp hd ha⟩
  have subX := childComplement (P 0 true) (Q 0 false) (Q 1 true)
    hQnonempty (hQcells 1 true) (Or.inr hcross.2.2.1)
  have sameBoundary : BoundaryFootprintVertices (Q 0 false) =
      BoundaryFootprintVertices (S 0 true) := by
    by_cases he : (Q 0 false).cells = ∅
    · simp [BoundaryFootprintVertices, he, ← hcommon, hcommonAnchor he]
    · have hn := Finset.nonempty_iff_ne_empty.mpr he
      have hs : (S 0 true).cells.Nonempty := hcommon ▸ hn
      simp only [BoundaryFootprintVertices, ite_eq_left hn,
        BoundaryFootprintEdges, ← hcommon]
  have sameTouching (T : ProtoTile) :
      TileTouching T (Q 0 false) ↔ TileTouching T (S 0 true) := by
    have sameEdges : BoundaryFootprintEdges (Q 0 false) =
        BoundaryFootprintEdges (S 0 true) := by
      simp only [BoundaryFootprintEdges, ← hcommon]
    unfold TileTouching
    rw [← hcommon, ← sameBoundary, ← sameEdges]
    by_cases he : (Q 0 false).cells = ∅
    · rw [hcommonAnchor he]
    · simp [he]
  have subY' : (S 2 false).cells ⊆
      (TileCellComplement (P 0 false) (S 0 true)).cells :=
    childComplement _ _ _ hSnonempty (hScells 2 false)
      (Or.inl ((sameTouching (S 2 false)).mp hcross.2.1))
  have subU := childComplement (P 0 true) (Q 0 false) (Q 2 true)
    hQnonemptySecond (hQcells 2 true) (Or.inr hcrossSecond.2.2.1)
  have subV := childComplement (P 0 false) (S 0 true) (S 1 false)
    hSnonemptySecond (hScells 1 false)
      (Or.inl ((sameTouching (S 1 false)).mp hcrossSecond.2.1))
  have zero := fun he => P4638T1EmptyCurvature (r 1) (Q 0 false)
    (hQ 0 false) he
  by_cases he : (Q 0 false).cells = ∅
  · have se : (S 0 true).cells = ∅ := hcommon.symm.trans he
    have ha : BandPrototile (r 0) (P 0 true) := by
      simpa [hr0] using hP 0 true
    have hb : BandPrototile (r 0) (P 0 false) := by
      simpa [hr0] using hP 0 false
    have hAc : TileCentroid (Q 0 false) - TileCentroid (P 0 true) =
        -((1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 (r 3) (r 2)) -
            (-(GaussianRealPoint (BandVectors.1 (r 3) (r 2))).2,
              (GaussianRealPoint (BandVectors.1 (r 3) (r 2))).1))) := by
      simpa using hQcent 0 false
    have hBc : TileCentroid (Q 0 false) - TileCentroid (P 0 false) =
        (1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 (r 3) (r 2)) -
            (-(GaussianRealPoint (BandVectors.1 (r 3) (r 2))).2,
              (GaussianRealPoint (BandVectors.1 (r 3) (r 2))).1)) := by
      have hc := hScent 0 true
      rw [← commonCent] at hc
      simpa using hc
    obtain ⟨F, g, e, h1, h2, hgrid, hincident, hupper, hlower⟩ :=
      P4638T1EmptyFordLocalization r hr (P 0 true) (P 0 false) (Q 0 false)
        ha hb he (zero he) hAc hBc
    have cover : ∀ y ∈ FootprintVertices (Q 0 false), ∀ a : GaussianInt,
        y ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) →
          a ∈ (P 0 true).cells ∨ a ∈ (P 0 false).cells := by
      intro y hy a hya
      have hy' : y = (Q 0 false).anchor := by
        simpa [FootprintVertices, he] using hy
      subst y
      have hrect := P4638T1FordIncidentCells F.q₁ F.q₂ h1 h2
        (e a - (BandPackingSymmetryTileAction g (Q 0 false)).anchor)
        (hincident a hya)
      have pull (T : ProtoTile)
          (ht : e a ∈ (BandPackingSymmetryTileAction g T).cells) : a ∈ T.cells := by
        rw [hgrid T] at ht
        obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ht
        exact e.injective hba ▸ hb
      rcases hrect with hu | hl
      · exact Or.inl (pull _ ((hupper (e a)).mpr hu))
      · exact Or.inr (pull _ ((hlower (e a)).mpr hl))
    have transition (X Y : ProtoTile) (ht : TouchingTriple X Y (Q 0 false)) :
        ∀ z : GaussianInt,
          z ∈ BoundaryFootprintVertices X ∧ z ∈ BoundaryFootprintVertices Y ∧
            z ∈ BoundaryFootprintVertices (Q 0 false) ↔ z = (Q 0 false).anchor := by
      obtain ⟨a, ha, _⟩ := ht.2.2.2
      have hae : a = (Q 0 false).anchor := by
        simpa [BoundaryFootprintVertices, he] using ha.2.2
      intro z
      constructor
      · intro hz
        simpa [BoundaryFootprintVertices, he] using hz.2.2
      · intro hz
        simpa only [hz, ← hae] using ha
    refine ⟨cover, ⟨?_⟩, zero⟩
    exact {
      precursor_cells := hcommon
      precursor_anchor := hcommonAnchor
      first_touching := hcross
      second_touching := hcrossSecond
      first_plus_child := subX
      first_minus_child := subY'
      second_plus_child := subU
      second_minus_child := subV
      a := (Q 0 false).anchor
      b := (Q 0 false).anchor
      first_transition := transition _ _ hcross
      second_transition := transition _ _ hcrossSecond
      branch := Or.inr ⟨he, rfl, rfl, hcommonAnchor he,
        by simp [BoundaryFootprintVertices, he],
        by simp [BoundaryFootprintVertices, se, hcommonAnchor he]⟩ }
  · have hn := Finset.nonempty_iff_ne_empty.mpr he
    have pairedCent (i : Fin 3) :
        (TileCentroid (Q i true)).1 + (TileCentroid (S i false)).1 =
            2 * (TileCentroid (Q 0 false)).1 ∧
        (TileCentroid (Q i true)).2 + (TileCentroid (S i false)).2 =
            2 * (TileCentroid (Q 0 false)).2 := by
      have ho := hQcent 0 false
      have ho' := hScent 0 true
      rw [← commonCent] at ho'
      have hp := hQcent i true
      have hm := hScent i false
      have ho1 := congrArg Prod.fst ho
      have ho2 := congrArg Prod.snd ho
      have ho1' := congrArg Prod.fst ho'
      have ho2' := congrArg Prod.snd ho'
      have hp1 := congrArg Prod.fst hp
      have hp2 := congrArg Prod.snd hp
      have hm1 := congrArg Prod.fst hm
      have hm2 := congrArg Prod.snd hm
      dsimp at ho1 ho2 ho1' ho2' hp1 hp2 hm1 hm2
      constructor <;> linarith
    have hXV := P4638T1MidpointReflection (r 2) (Q 1 true) (S 1 false)
      (hQ 1 true) (hS 1 false) (Finset.nonempty_iff_ne_empty.mpr hQnonempty)
      (TileCentroid (Q 0 false)) (by
        apply Prod.ext
        · dsimp; linarith [(pairedCent 1).1]
        · dsimp; linarith [(pairedCent 1).2])
    have hYU := P4638T1MidpointReflection (r 3) (S 2 false) (Q 2 true)
      (hS 2 false) (hQ 2 true) (Finset.nonempty_iff_ne_empty.mpr hSnonempty)
      (TileCentroid (Q 0 false)) (by
        apply Prod.ext
        · dsimp; linarith [(pairedCent 2).1]
        · dsimp; linarith [(pairedCent 2).2])
    obtain ⟨⟨data⟩, hedges⟩ := P4638T1AntipodalContactArcs
      (TileCellComplement (P 0 true) (Q 0 false))
      (TileCellComplement (P 0 false) (S 0 true))
      (Q 0 false) (S 0 true) (Q 1 true) (S 2 false) (Q 2 true) (S 1 false)
      hn (hOlattice he) hcomplementPlus.1 hcomplementMinus.1
      hcomplementPlus.2 ((sameTouching _).mpr hcomplementMinus.2)
      hcomplementDisjoint hcentral hOsym hcommon hcommonAnchor
      (Finset.nonempty_iff_ne_empty.mpr hQnonempty)
      (Finset.nonempty_iff_ne_empty.mpr hSnonempty)
      (Finset.nonempty_iff_ne_empty.mpr hQnonemptySecond)
      (Finset.nonempty_iff_ne_empty.mpr hSnonemptySecond)
      hcross hcrossSecond subX subY' subU subV hXV hYU
    have cover := P4638T1ContactStarCoverage
      (TileCellComplement (P 0 true) (Q 0 false))
      (TileCellComplement (P 0 false) (S 0 true))
      (Q 0 false) (S 0 true) (Q 1 true) (S 2 false) (Q 2 true) (S 1 false)
      hn (hOlattice he) hcomplementPlus.1 hcomplementMinus.1
      hcomplementPlus.2 ((sameTouching _).mpr hcomplementMinus.2)
      hcomplementDisjoint
      (Finset.nonempty_iff_ne_empty.mpr hQnonempty)
      (Finset.nonempty_iff_ne_empty.mpr hSnonempty)
      (Finset.nonempty_iff_ne_empty.mpr hQnonemptySecond)
      (Finset.nonempty_iff_ne_empty.mpr hSnonemptySecond) data hedges
    refine ⟨?_, ⟨data⟩, zero⟩
    intro y hy a hya
    rcases cover y hy a hya with ha | ha | ha
    · exact Or.inl (hQcells 0 false ha)
    · exact Or.inl (Finset.mem_sdiff.mp ha).1
    · exact Or.inr (Finset.mem_sdiff.mp ha).1

end ApollonianSuperharmonic

end
