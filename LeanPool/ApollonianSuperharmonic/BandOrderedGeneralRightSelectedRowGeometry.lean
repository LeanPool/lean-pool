/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnTranslation
public import LeanPool.ApollonianSuperharmonic.ObservableTileRetargeting

public import LeanPool.ApollonianSuperharmonic.P5640T1NonpairedOccurrenceIntersections
public import LeanPool.ApollonianSuperharmonic.P5635T1RightBoundaryInterfaceRecords
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightInterfaceCertificateExists
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSelectedContactRow

-- [TABLET NODE: BandOrderedGeneralRightSelectedRowGeometry]

/-!
# BandOrderedGeneralRightSelectedRowGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SelectedRowGeometry

private theorem edgeVertex :
    (by
      classical
      exact
        ∀ (tile : ProtoTile), (tile.cells.Nonempty) → (∀ (edge : Finset GaussianInt), (edge ∈
            FootprintEdges tile) → (∀ (point : GaussianInt), (point ∈ edge) → (point ∈
            FootprintVertices tile))) ) := by
  classical
  intro tile hnon edge hedge point hpoint
  rcases hedge with ⟨a, ha, hshape⟩
  rcases hshape with hshape | hshape | hshape | hshape
  all_goals rw [hshape] at hpoint
  all_goals simp only [Finset.mem_insert, Finset.mem_singleton] at hpoint
  all_goals simp only [FootprintVertices, ite_eq_left hnon, Set.mem_ofPred_eq]
  all_goals rcases hpoint with hpoint | hpoint
  all_goals rw [hpoint]
  all_goals refine ⟨a, ha, ?_⟩; simp

private theorem turnOutgoing :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        (∀ (j : Fin (3 : ℕ)), BandVectors.1 (q (0 : Fin (4 : ℕ))) (q j.succ) = (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ))) ∧ BandVectors.2
            (q (0 : Fin (4 : ℕ))) (q j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ)))) → (∀ (s : Fin 3), GaussianQuarterTurn
            (BandVectors.1 (q s.succ) (q 0)) = BandVectors.1 (q 0) (q s.succ)) ) := by
  classical
  intro C D T N h k x bundle q turnFlip s
  rw [(turnFlip s).1]
  rcases BandVectors.1 (q s.succ) (q 0) with ⟨a, b⟩
  apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]



private theorem turnThrice :
    (by
      classical
      exact
        (∀ (z : GaussianInt), GaussianQuarterTurn (-z) = -GaussianQuarterTurn z) → ((∀ (z :
            GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn z) = -z) → (∀ (z :
            GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn z)) =
            -GaussianQuarterTurn z)) ) := by
  classical
  intro turnNeg turnTwice z
  calc
    GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn z)) =
        GaussianQuarterTurn (-z) := congrArg GaussianQuarterTurn (turnTwice z)
    _ = -GaussianQuarterTurn z := turnNeg z

private theorem centeredExactTurn :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
            (BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection) → (
        let F := bundle.normalizedFixed
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), (ExactTileInterfaceTriple F (TileTranslation F a)
            (TileTranslation F b)) → (Nonempty (ExactTileInterfaceTriple F (TileTranslation F
                (GaussianQuarterTurn a)) (TileTranslation F (GaussianQuarterTurn b))))) ) := by
  classical
  intro C D T N h k x bundle placement F a b E
  let q := bundle.normalizedPresentation
  let cfg := bundle.configuration
  obtain ⟨_, _, E', _, _, _, _⟩ :=
    QuarterTurnSymmetricExactInterfaceTransport F a b E
      (TileT2QuarterTurn q cfg bundle.normalizedCircle F placement.layout)
  exact ⟨E'⟩

private theorem twiceExactTurn :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let F := bundle.normalizedFixed
        (∀ (a : GaussianInt), ∀ (b : GaussianInt), (ExactTileInterfaceTriple F (TileTranslation F
            a) (TileTranslation F b)) → (Nonempty (ExactTileInterfaceTriple F (TileTranslation F
            (GaussianQuarterTurn a)) (TileTranslation F (GaussianQuarterTurn b))))) → (∀ (a :
            GaussianInt), ∀ (b : GaussianInt), (ExactTileInterfaceTriple F (TileTranslation F a)
            (TileTranslation F b)) → (Nonempty (ExactTileInterfaceTriple F (TileTranslation F
                (GaussianQuarterTurn (GaussianQuarterTurn a))) (TileTranslation F
                (GaussianQuarterTurn (GaussianQuarterTurn b)))))) ) := by
  classical
  intro C D T N h k x bundle F centeredExactTurn a b E
  obtain ⟨E1⟩ := centeredExactTurn a b E
  exact centeredExactTurn (GaussianQuarterTurn a) (GaussianQuarterTurn b) E1

private theorem thriceExactTurn :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let F := bundle.normalizedFixed
        (∀ (a : GaussianInt), ∀ (b : GaussianInt), (ExactTileInterfaceTriple F (TileTranslation F
            a) (TileTranslation F b)) → (Nonempty (ExactTileInterfaceTriple F (TileTranslation F
            (GaussianQuarterTurn a)) (TileTranslation F (GaussianQuarterTurn b))))) → (∀ (a :
            GaussianInt), ∀ (b : GaussianInt), (ExactTileInterfaceTriple F (TileTranslation F a)
            (TileTranslation F b)) → (Nonempty (ExactTileInterfaceTriple F (TileTranslation F
                (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn a))))
                (TileTranslation F (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn
                b))))))) ) := by
  classical
  intro C D T N h k x bundle F centeredExactTurn a b E
  obtain ⟨E1⟩ := centeredExactTurn a b E
  obtain ⟨E2⟩ := centeredExactTurn (GaussianQuarterTurn a)
    (GaussianQuarterTurn b) E1
  exact centeredExactTurn (GaussianQuarterTurn (GaussianQuarterTurn a))
    (GaussianQuarterTurn (GaussianQuarterTurn b)) E2

private theorem tripleTurnOutgoing :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        (∀ (s : Fin 3), GaussianQuarterTurn (BandVectors.1 (q s.succ) (q 0)) = BandVectors.1 (q
            0) (q s.succ)) → ((∀ (z : GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianQuarterTurn z)) = -GaussianQuarterTurn z) → (∀ (ell : Fin 3),
            GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q
            ell.succ) (q 0)))) = -BandVectors.1 (q 0) (q ell.succ))) ) := by
  classical
  intro C D T N h k x bundle q turnOutgoing turnThrice ell
  calc
    _ = -GaussianQuarterTurn (BandVectors.1 (q ell.succ) (q 0)) :=
      turnThrice _
    _ = _ := by rw [turnOutgoing]

private theorem tripleTurnNegativeNext :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        (∀ (s : Fin 3), GaussianQuarterTurn (BandVectors.1 (q s.succ) (q 0)) = BandVectors.1 (q
            0) (q s.succ)) → ((∀ (z : GaussianInt), GaussianQuarterTurn (-z) =
            -GaussianQuarterTurn z) → ((∀ (z : GaussianInt), GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianQuarterTurn z)) = -GaussianQuarterTurn z) → (∀ (ell :
            Fin 3), GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (-BandVectors.1
            (q (ell + 1).succ) (q 0)))) = BandVectors.1 (q 0) (q (ell + 1).succ)))) ) := by
  classical
  intro C D T N h k x bundle q turnOutgoing turnNeg turnThrice ell
  calc
    _ = -GaussianQuarterTurn (-BandVectors.1 (q (ell + 1).succ) (q 0)) :=
      turnThrice _
    _ = GaussianQuarterTurn (BandVectors.1 (q (ell + 1).succ) (q 0)) := by
      rw [turnNeg]
      simp
    _ = _ := by rw [turnOutgoing]

private theorem hedge :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (A' : ProtoTile), (A.cells = A'.cells) → (FootprintEdges A =
            FootprintEdges A') ) := by
  classical
  intro A A' hcell
  simp only [FootprintEdges]
  rw [hcell]

private theorem translateObs :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (d : GaussianInt), (A.cells = A'.cells) →
            ((A.cells = ∅ → A.anchor = A'.anchor) → ((TileTranslation A d).cells =
            (TileTranslation A' d).cells ∧ ((TileTranslation A d).cells = ∅ → (TileTranslation A
            d).anchor = (TileTranslation A' d).anchor))) ) := by
  classical
  intro A A' d hc ha
  constructor
  · simp [TileTranslation, hc]
  · intro he
    have he' : A.cells = ∅ := (TileTranslationFormulas A d).2.2.1.mp he
    simp [TileTranslation, ha he']

private theorem centeredTurnTouching :
    (by
      classical
      exact
        (∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), ∀ (B' : ProtoTile), ∀ (D :
            ProtoTile), ∀ (D' : ProtoTile), (A.cells = A'.cells) → ((A.cells = ∅ → A.anchor =
            A'.anchor) → ((B.cells = B'.cells) → ((B.cells = ∅ → B.anchor = B'.anchor) →
            ((D.cells = D'.cells) → ((D.cells = ∅ → D.anchor = D'.anchor) → ((TouchingTriple A B
            D) → (TouchingTriple A' B' D')))))))) → ((∀ (A : ProtoTile), ∀ (a : GaussianInt), ∀
            (u₀ : GaussianInt), TileTranslation (TileQuarterTurn (TileTranslation A a)) u₀ =
            TileTranslation (TileTranslation (TileQuarterTurn A) u₀) (GaussianQuarterTurn a)) →
            ((∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (d : GaussianInt), (A.cells = A'.cells) →
            ((A.cells = ∅ → A.anchor = A'.anchor) → ((TileTranslation A d).cells =
            (TileTranslation A' d).cells ∧ ((TileTranslation A d).cells = ∅ → (TileTranslation A
            d).anchor = (TileTranslation A' d).anchor)))) → (∀ (A : ProtoTile), ∀ (a :
            GaussianInt), ∀ (b : GaussianInt), (QuarterTurnSymmetric A) → ((TouchingTriple A
            (TileTranslation A a) (TileTranslation A b)) → (TouchingTriple A (TileTranslation A
            (GaussianQuarterTurn a)) (TileTranslation A (GaussianQuarterTurn b))))))) ) := by
  classical
  intro touchingRetarget quarterTranslate translateObs A a b hsym ht
  obtain ⟨u₀, hu₀, hcell, hanchor, _, _⟩ :=
    QuarterTurnSymmetricCenteredTransport A hsym
  have hanchor' : (TileTranslation (TileQuarterTurn A) u₀).cells = ∅ →
      (TileTranslation (TileQuarterTurn A) u₀).anchor = A.anchor := by
    intro he
    apply hanchor
    rw [← hcell]
    exact he
  have hq := (TouchingTripleCovariance A (TileTranslation A a)
    (TileTranslation A b) u₀).2.1.mp ht
  have hqt := (TouchingTripleCovariance (TileQuarterTurn A)
    (TileQuarterTurn (TileTranslation A a))
    (TileQuarterTurn (TileTranslation A b)) u₀).1.mp hq
  rw [quarterTranslate A a u₀, quarterTranslate A b u₀] at hqt
  have ha := translateObs (TileTranslation (TileQuarterTurn A) u₀) A
    (GaussianQuarterTurn a) hcell hanchor'
  have hb := translateObs (TileTranslation (TileQuarterTurn A) u₀) A
    (GaussianQuarterTurn b) hcell hanchor'
  exact touchingRetarget
    (TileTranslation (TileQuarterTurn A) u₀) A
    (TileTranslation (TileTranslation (TileQuarterTurn A) u₀)
      (GaussianQuarterTurn a)) (TileTranslation A (GaussianQuarterTurn a)
    )
    (TileTranslation (TileTranslation (TileQuarterTurn A) u₀)
      (GaussianQuarterTurn b)) (TileTranslation A (GaussianQuarterTurn b))
    hcell hanchor' ha.1 ha.2 hb.1 hb.2 hqt

private theorem twiceTouching :
    (by
      classical
      exact
        (∀ (A : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (QuarterTurnSymmetric A) →
            ((TouchingTriple A (TileTranslation A a) (TileTranslation A b)) → (TouchingTriple A
            (TileTranslation A (GaussianQuarterTurn a)) (TileTranslation A (GaussianQuarterTurn
            b))))) → (∀ (A : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
            (QuarterTurnSymmetric A) → ((TouchingTriple A (TileTranslation A a) (TileTranslation
            A b)) → (TouchingTriple A (TileTranslation A (GaussianQuarterTurn
            (GaussianQuarterTurn a))) (TileTranslation A (GaussianQuarterTurn
            (GaussianQuarterTurn b)))))) ) := by
  classical
  intro centeredTurnTouching A a b hsym ht
  have ht' := centeredTurnTouching A a b hsym ht
  exact centeredTurnTouching A (GaussianQuarterTurn a) (GaussianQuarterTurn b)
    hsym ht'

private theorem thriceTouching :
    (by
      classical
      exact
        (∀ (A : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (QuarterTurnSymmetric A) →
            ((TouchingTriple A (TileTranslation A a) (TileTranslation A b)) → (TouchingTriple A
            (TileTranslation A (GaussianQuarterTurn a)) (TileTranslation A (GaussianQuarterTurn
            b))))) → ((∀ (A : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
            (QuarterTurnSymmetric A) → ((TouchingTriple A (TileTranslation A a) (TileTranslation
            A b)) → (TouchingTriple A (TileTranslation A (GaussianQuarterTurn
            (GaussianQuarterTurn a))) (TileTranslation A (GaussianQuarterTurn
            (GaussianQuarterTurn b)))))) → (∀ (A : ProtoTile), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), (QuarterTurnSymmetric A) → ((TouchingTriple A (TileTranslation A a)
            (TileTranslation A b)) → (TouchingTriple A (TileTranslation A (GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianQuarterTurn a)))) (TileTranslation A
            (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn b)))))))) ) := by
  classical
  intro centeredTurnTouching twiceTouching A a b hsym ht
  exact centeredTurnTouching A _ _ hsym
    (twiceTouching A a b hsym ht)

private theorem touchingPlus :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
            (BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection) → (
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (i : Fin (3 : ℕ)), TouchingTriple F (TileTranslation F (BandVectors.1 (q i.succ) (q (0
            : Fin (4 : ℕ))))) (TileTranslation F (-BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ)
            (q (0 : Fin (4 : ℕ)))))) → ((∀ (s : Fin 3), GaussianQuarterTurn (BandVectors.1 (q
            s.succ) (q 0)) = BandVectors.1 (q 0) (q s.succ)) → ((∀ (z : GaussianInt),
            GaussianQuarterTurn (-z) = -GaussianQuarterTurn z) → ((∀ (A : ProtoTile), ∀ (a :
            GaussianInt), ∀ (b : GaussianInt), (QuarterTurnSymmetric A) → ((TouchingTriple A
            (TileTranslation A a) (TileTranslation A b)) → (TouchingTriple A (TileTranslation A
            (GaussianQuarterTurn a)) (TileTranslation A (GaussianQuarterTurn b))))) → (∀ (ell :
            Fin 3), TouchingTriple F (TileTranslation F (BandVectors.1 (q 0) (q ell.succ)))
            (TileTranslation F (-BandVectors.1 (q 0) (q (ell + 1).succ)))))))) ) := by
  classical
  intro C D T N h k x bundle placement q F translatedTouching turnOutgoing turnNeg
      centeredTurnTouching ell
  let cfg := bundle.configuration
  have ht := centeredTurnTouching F
    (BandVectors.1 (q ell.succ) (q 0))
    (-BandVectors.1 (q (ell + 1).succ) (q 0))
    (TileT2QuarterTurn q cfg bundle.normalizedCircle F placement.layout)
    (translatedTouching ell)
  simpa [turnOutgoing, turnNeg] using ht

private theorem touchingMinus :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
            (BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection) → (
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (i : Fin (3 : ℕ)), TouchingTriple F (TileTranslation F (BandVectors.1 (q i.succ) (q (0
            : Fin (4 : ℕ))))) (TileTranslation F (-BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ)
            (q (0 : Fin (4 : ℕ)))))) → ((∀ (ell : Fin 3), GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianQuarterTurn (BandVectors.1 (q ell.succ) (q 0)))) =
            -BandVectors.1 (q 0) (q ell.succ)) → ((∀ (ell : Fin 3), GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianQuarterTurn (-BandVectors.1 (q (ell + 1).succ) (q 0))))
            = BandVectors.1 (q 0) (q (ell + 1).succ)) → ((∀ (A : ProtoTile), ∀ (a : GaussianInt),
            ∀ (b : GaussianInt), (QuarterTurnSymmetric A) → ((TouchingTriple A (TileTranslation A
            a) (TileTranslation A b)) → (TouchingTriple A (TileTranslation A (GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianQuarterTurn a)))) (TileTranslation A
            (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn b))))))) → (∀ (ell :
            Fin 3), TouchingTriple F (TileTranslation F (-BandVectors.1 (q 0) (q ell.succ)))
            (TileTranslation F (BandVectors.1 (q 0) (q (ell + 1).succ)))))))) ) := by
  classical
  intro C D T N h k x bundle placement q F translatedTouching tripleTurnOutgoing
      tripleTurnNegativeNext thriceTouching ell
  let cfg := bundle.configuration
  have ht := thriceTouching F
    (BandVectors.1 (q ell.succ) (q 0))
    (-BandVectors.1 (q (ell + 1).succ) (q 0))
    (TileT2QuarterTurn q cfg bundle.normalizedCircle F placement.layout)
    (translatedTouching ell)
  simpa only [tripleTurnOutgoing, tripleTurnNegativeNext] using ht

private theorem indexNe :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), (BandOrderedGeneralSelectedContactRow
            bundle.normalizedPresentation bundle.configuration bundle.normalizedCircle
            bundle.normalizedFixed placement.layout placement.exteriorIndex
            placement.centralIndex) → (
        placement.exteriorIndex ≠ placement.centralIndex) ) := by
  classical
  intro C D T N h k x bundle placement row
  let q := bundle.normalizedPresentation
  let cfg := bundle.configuration
  let F := bundle.normalizedFixed
  have labels : ∀ a b, BandOrderedGeneralSelectedContactRow q cfg
      bundle.normalizedCircle F placement.layout a b → a.label ≠ b.label := by
    intro a b r
    cases r <;> decide +kernel
  intro heq
  exact labels _ _ row (congrArg PeriodicSubtileIndex.label heq)

private theorem originalAllowed :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), ∀ (selectedEdge : Finset GaussianInt), (selectedEdge ∈
            FootprintEdges (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.exteriorIndex) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.centralIndex)) → (
        (placement.exteriorIndex ≠ placement.centralIndex) → (AllowedSubtileIncidence
            placement.exteriorIndex placement.centralIndex)) ) := by
  classical
  intro C D T N h k x bundle placement selectedEdge hedge indexNe
  let q := bundle.normalizedPresentation
  let cfg := bundle.configuration
  let F := bundle.normalizedFixed
  have hclass := BandOriginalOccurrenceIntersectionClassification q cfg
    bundle.normalizedCircle F placement.layout
  apply (hclass placement.exteriorIndex placement.centralIndex indexNe).1
  exact ⟨selectedEdge, hedge⟩

private theorem modifiedEdgesNonempty :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), (placement.exteriorIndex ≠ placement.centralIndex) →
            ((placement.layout.modified.plane.adjacent placement.exteriorIndex
            placement.centralIndex) → ((FootprintEdges (placement.layout.modified.tile
            placement.exteriorIndex) ∩ FootprintEdges (placement.layout.modified.tile
            placement.centralIndex)).Nonempty)) ) := by
  classical
  intro C D T N h k x bundle placement indexNe modifiedAdjacent
  have hclass := PeriodicTileIntersectionClassification
    placement.layout.modified
  have hadj := (hclass.1 placement.exteriorIndex placement.centralIndex indexNe).1
  exact hadj.mpr modifiedAdjacent

private theorem modifiedPath :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), (placement.exteriorIndex ≠ placement.centralIndex) →
            (((FootprintEdges (placement.layout.modified.tile placement.exteriorIndex) ∩
            FootprintEdges (placement.layout.modified.tile placement.centralIndex)).Nonempty) →
            (∃ s t : GaussianInt, SimpleGridPathBetween (FootprintVertices
            (placement.layout.modified.tile placement.exteriorIndex) ∩ FootprintVertices
            (placement.layout.modified.tile placement.centralIndex)) (FootprintEdges
            (placement.layout.modified.tile placement.exteriorIndex) ∩ FootprintEdges
            (placement.layout.modified.tile placement.centralIndex)) s t)) ) := by
  classical
  intro C D T N h k x bundle placement indexNe modifiedEdgesNonempty
  have hclassification := PeriodicTileIntersectionClassification
    placement.layout.modified
  have hpaths := PeriodicTileIntersectionPaths placement.layout.modified
    hclassification.2 placement.exteriorIndex placement.centralIndex indexNe
  rcases hpaths.1.mpr modifiedEdgesNonempty with
    ⟨_, f, g, _, _, _, _, hpath⟩
  have hvertices := (hclassification.1 placement.exteriorIndex
    placement.centralIndex indexNe).2.1 modifiedEdgesNonempty
  rw [← hvertices.2] at hpath
  exact ⟨_, _, hpath⟩

private theorem noPairedOccurrence :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), (BandOrderedGeneralSelectedContactRow
            bundle.normalizedPresentation bundle.configuration bundle.normalizedCircle
            bundle.normalizedFixed placement.layout placement.exteriorIndex
            placement.centralIndex) → (
        ¬ ((placement.exteriorIndex.label = .A ∧ placement.centralIndex.label = .B ∨
            placement.exteriorIndex.label = .B ∧ placement.centralIndex.label = .A) ∧
            placement.exteriorIndex.first = placement.centralIndex.first ∧
            placement.exteriorIndex.second = placement.centralIndex.second)) ) := by
  classical
  intro C D T N h k x bundle placement row
  let q := bundle.normalizedPresentation
  let cfg := bundle.configuration
  let F := bundle.normalizedFixed
  have coordinates : ∀ a b, BandOrderedGeneralSelectedContactRow q cfg
      bundle.normalizedCircle F placement.layout a b →
      ¬ (a.first = b.first ∧ a.second = b.second) := by
    intro a b r
    cases r <;> decide +kernel
  intro hp
  exact coordinates _ _ row hp.2

private theorem originalSelectedPath :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), ∀ (selectedEdge : Finset GaussianInt),
            (bundle.normalizedPoint ∈ selectedEdge) → ((selectedEdge ∈ FootprintEdges
            (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.exteriorIndex) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.centralIndex)) → (
        (∃ s t : GaussianInt, SimpleGridPathBetween (FootprintVertices
            (placement.layout.modified.tile placement.exteriorIndex) ∩ FootprintVertices
            (placement.layout.modified.tile placement.centralIndex)) (FootprintEdges
            (placement.layout.modified.tile placement.exteriorIndex) ∩ FootprintEdges
            (placement.layout.modified.tile placement.centralIndex)) s t) → (
        let P := placement.layout.P
        let u := placement.layout.u
        let v := placement.layout.v
        (FootprintEdges (ModifiedSubtileOccurrenceInterpretation placement.layout.P
            placement.layout.O placement.layout.u placement.layout.v placement.exteriorIndex) ∩
            FootprintEdges (ModifiedSubtileOccurrenceInterpretation placement.layout.P
            placement.layout.O placement.layout.u placement.layout.v placement.centralIndex) =
            FootprintEdges (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.exteriorIndex) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.centralIndex) ∧ FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation placement.layout.P placement.layout.O
            placement.layout.u placement.layout.v placement.exteriorIndex) ∩ FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation placement.layout.P placement.layout.O
            placement.layout.u placement.layout.v placement.centralIndex) = FootprintVertices
            (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.exteriorIndex) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.centralIndex)) → (
        let selectedPath : Prop :=
            (∃ selectedStart selectedEnd : GaussianInt,
              SimpleGridPathBetween
                (FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                (FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                selectedStart selectedEnd ∧
              selectedEdge ∈
                FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex) ∧
              bundle.normalizedPoint ∈ selectedEdge)
        selectedPath)))) ) := by
  classical
  intro C D T N h k x bundle placement selectedEdge hx hedge modifiedPath P u v
      selectedOccurrenceRetarget selectedPath
  let q := bundle.normalizedPresentation
  let cfg := bundle.configuration
  let F := bundle.normalizedFixed
  rcases modifiedPath with ⟨selectedStart, selectedEnd, hpath⟩
  have hpath' := hpath
  rw [placement.layout.modified_tile placement.exteriorIndex,
    placement.layout.modified_tile placement.centralIndex] at hpath'
  rw [selectedOccurrenceRetarget.2,
    selectedOccurrenceRetarget.1] at hpath'
  exact ⟨selectedStart, selectedEnd, hpath', hedge, hx⟩

private theorem canonicalFinish :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), ∀ (selectedEdge : Finset GaussianInt), (selectedEdge ∈
                FootprintEdges (SubtileOccurrenceInterpretation placement.layout.P
            placement.layout.u placement.layout.v placement.exteriorIndex) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.centralIndex)) → (
        let q := bundle.normalizedPresentation
        let cfg := bundle.configuration
        let F := bundle.normalizedFixed
        let root := bundle.normalizedRoot
        ∀ (edgeVertex : ∀ (tile : ProtoTile), (tile.cells.Nonempty) → (∀ (edge : Finset
            GaussianInt), (edge ∈ FootprintEdges tile) → (∀ (point : GaussianInt), (point ∈ edge)
            → (point ∈ FootprintVertices tile)))),
        let norm : BandOrderedGeneralRightNormalizationCertificate C T N h k x := {
          presentation := bundle.presentation
          presentation_proper := bundle.presentation_proper
          presentation_child := bundle.presentation_child
          parentRotation := bundle.parentRotation
          symmetry := bundle.symmetry
          rotatedPresentation := bundle.rotatedPresentation
          rotated_presentation_eq := bundle.rotated_presentation_eq
          normalizedPresentation := q
          normalized_presentation_eq := bundle.normalized_presentation_eq
          configuration := cfg
          normalizedCircle := bundle.normalizedCircle
          normalized_circle_eq := bundle.normalized_circle_eq
          normalizedFixedCircle := bundle.normalizedCircle
          normalized_fixed_circle_eq := by
            calc
              bundle.normalizedCircle.1.1 = q 0 := bundle.normalized_circle_eq.symm
              _ = BandPackingSymmetryCircleAction bundle.symmetry C.1.1 := by
                have hq0 := congrFun bundle.normalized_presentation_eq 0
                calc
                  q 0 = BandPackingSymmetryCircleAction bundle.symmetry
                      (bundle.rotatedPresentation 0) := by
                        simpa [BandPackingSymmetryQuadrupleAction] using hq0
                  _ = BandPackingSymmetryCircleAction bundle.symmetry C.1.1 := by
                        rw [bundle.rotated_presentation_eq]
                        simp [bundle.presentation_child]
          normalizedRoot := root
          normalizedFixed := F
          normalizedRootFunction := bundle.normalizedRootFunction
          normalizedFixedFunction := bundle.normalizedFixedFunction
          normalizedPoint := bundle.normalizedPoint
          normalized_root_eq := bundle.normalized_root_eq
          normalized_fixed_eq := bundle.normalized_fixed_eq
          normalized_root_function_eq := bundle.normalized_root_function_eq
          normalized_fixed_function_eq := bundle.normalized_fixed_function_eq
          normalized_point_eq := bundle.normalized_point_eq
          normalized_point_root_domain := by
            obtain ⟨edge, hp, he⟩ := bundle.edgeAtPoint
            have hne := (LatticeTileGridStructure root bundle.root_lattice).1.1
            have hvert := edgeVertex root hne edge he.1 bundle.normalizedPoint hp
            have hdom := PositiveCurvatureTileOdometerDomain (q 0) root
              bundle.normalizedRootFunction (ProperBandCurvatureStructure q cfg.proper).1
              bundle.normalized_root_odometer
            exact (Set.ext_iff.mp hdom bundle.normalizedPoint).mpr hvert
          normalized_point_fixed_domain := by
            obtain ⟨edge, hp, he⟩ := bundle.edgeAtPoint
            have hne := (LatticeTileGridStructure F bundle.fixed_lattice).1.1
            have hvert := edgeVertex F hne edge he.2 bundle.normalizedPoint hp
            have hdom := PositiveCurvatureTileOdometerDomain
              bundle.normalizedCircle.1.1 F bundle.normalizedFixedFunction
              bundle.normalizedCircle.property placement.adjacency.2.1
            exact (Set.ext_iff.mp hdom bundle.normalizedPoint).mpr hvert
          normalized_root_odometer := bundle.normalized_root_odometer
          normalized_fixed_odometer := placement.adjacency.2.1
          normalized_root_lattice := bundle.root_lattice
          normalized_fixed_lattice := bundle.fixed_lattice
          normalizedRootSlope := bundle.normalizedRootSlope
          normalizedFixedSlope := bundle.normalizedFixedSlope
          normalized_root_slope := bundle.normalized_root_slope
          normalized_fixed_slope := bundle.normalized_fixed_slope
          pieces := bundle.pieces
          functions := bundle.functions
          root_band := bundle.root_band
          piece_odometer := bundle.piece_odometer
          piece_cell_cover := bundle.piece_cell_cover
          piece_footprint := bundle.piece_footprint
          piece_centroid := bundle.piece_centroid
          function_domain_cover := bundle.function_domain_cover
          function_restriction := bundle.function_restriction
          function_compatibility := bundle.function_compatibility
          piece_slope := bundle.piece_slope
          adjacency := placement.adjacency
          layout := placement.layout
          fixed_quarter_turn := TileT2QuarterTurn q cfg bundle.normalizedCircle F placement.layout
          rightFirstSlot := placement.rightFirstSlot
          rightSecondSlot := placement.rightSecondSlot
          rightDirectionSlot := placement.rightDirectionSlot
          right_slots_cyclic := placement.right_slots_cyclic
          rightNeighborPositive := placement.rightNeighborPositive
          right_adjacency_centroid := placement.right_adjacency_centroid
          right_adjacency_slope_real := by
            have hroot : placement.rightRootSlope = bundle.normalizedRootSlope :=
              Option.some.inj (placement.right_root_slope.symm.trans
                bundle.normalized_root_slope)
            have hf : placement.rightFixedSlope = bundle.normalizedFixedSlope :=
              Option.some.inj (placement.right_fixed_slope.symm.trans
                bundle.normalized_fixed_slope)
            simpa [hroot, hf, q] using placement.right_adjacency_slope_real
          right_adjacency_slope_imag := by
            have hroot : placement.rightRootSlope = bundle.normalizedRootSlope :=
              Option.some.inj (placement.right_root_slope.symm.trans
                bundle.normalized_root_slope)
            have hf : placement.rightFixedSlope = bundle.normalizedFixedSlope :=
              Option.some.inj (placement.right_fixed_slope.symm.trans
                bundle.normalized_fixed_slope)
            simpa [hroot, hf, q] using placement.right_adjacency_slope_imag
          rightNeighborDisplacement := placement.rightNeighborDisplacement
          right_neighbor_displacement := placement.right_neighbor_displacement
          right_neighbor_cells := placement.right_neighbor_cells
          right_neighbor_empty_anchor := placement.right_neighbor_empty_anchor
          firstBoundarySign := placement.firstBoundarySign
          secondBoundarySign := placement.secondBoundarySign
          boundary_signs := placement.boundary_signs
          first_boundary_cells := placement.first_boundary_cells
          first_boundary_empty_anchor := placement.first_boundary_empty_anchor
          first_boundary_footprint := placement.first_boundary_footprint
          first_boundary_domain := placement.first_boundary_domain
          second_boundary_cells := placement.second_boundary_cells
          second_boundary_empty_anchor := placement.second_boundary_empty_anchor
          second_boundary_footprint := placement.second_boundary_footprint
          second_boundary_domain := placement.second_boundary_domain
          normalized_star := bundle.normalized_star }
        ((∀ (m : ℤ), ∀ (n : ℤ), ∀ (x_1 : LatticeCell), x_1 ∈ (TileTranslation F
            ((↑m : GaussianInt) * placement.layout.u + (↑n : GaussianInt) *
            placement.layout.v)).cells ↔ ∃ (label : SixSubtileLabel), x_1 ∈
            (ModifiedSubtileOccurrenceInterpretation placement.layout.P placement.layout.O
            placement.layout.u placement.layout.v ⟨label, m, n⟩).cells) ∧ ∀ (m : ℤ), ∀ (n : ℤ), ∀
                (r : ℤ), ∀ (s : ℤ), (m, n) ≠ (r, s) → Disjoint (TileTranslation F ((↑m :
                GaussianInt)
            * placement.layout.u + (↑n : GaussianInt) * placement.layout.v)).cells
            (TileTranslation F ((↑r : GaussianInt) * placement.layout.u + (↑s : GaussianInt) *
            placement.layout.v)).cells) → ((0 < (q 0).1) → ((∀ (A : ProtoTile), ∀ (A' :
                ProtoTile), ∀ (B : ProtoTile), ∀ (B' : ProtoTile), ∀ (D : ProtoTile), ∀ (D' :
                ProtoTile), (A.cells = A'.cells) → ((A.cells = ∅ → A.anchor =
            A'.anchor) → ((B.cells = B'.cells) → ((B.cells = ∅ → B.anchor = B'.anchor) →
            ((D.cells = D'.cells) → ((D.cells = ∅ → D.anchor = D'.anchor) → ((TouchingTriple A B
            D) → (TouchingTriple A' B' D')))))))) → (∀ (uStart : GaussianInt), ∀ (uEnd :
                GaussianInt), ∀ (mR : Int), ∀ (nR : Int), ∀ (mS : Int), ∀ (nS : Int), ∀ (mE :
                Int), ∀ (nE : Int), (placement.rightNeighborDisplacement =
            (mR : GaussianInt) * placement.layout.u +
              (nR : GaussianInt) * placement.layout.v) → ((uStart = (mS : GaussianInt) *
                  placement.layout.u +
            (nS : GaussianInt) * placement.layout.v) → ((uEnd = (mE : GaussianInt) *
                placement.layout.u +
            (nE : GaussianInt) * placement.layout.v) → (((0, 0) ≠ (mR, nR)) → (((0, 0) ≠ (mS,
                nS)) → (((0, 0) ≠ (mE, nE)) → (((mR, nR) ≠ (mS, nS)) → (((mR, nR) ≠ (mE, nE)) →
                (((mS, nS) ≠ (mE, nE)) → ((ExactTileInterfaceTriple F
            (TileTranslation F placement.rightNeighborDisplacement)
            (TileTranslation F uStart)) → ((ExactTileInterfaceTriple F (TileTranslation F uEnd)
            (TileTranslation F placement.rightNeighborDisplacement)) → ((TouchingTriple F
            (TileTranslation F placement.rightNeighborDisplacement)
            (TileTranslation F uStart)) → ((TouchingTriple F (TileTranslation F uEnd)
            (TileTranslation F placement.rightNeighborDisplacement)) → (∃ g :
                BandOrderedGeneralRightInterfaceCertificate norm, g.startCompanion =
                TileTranslation F uStart ∧ g.endCompanion = TileTranslation F uEnd ∧
                g.startData.point ≠ g.endData.point)))))))))))))))))) := by
  classical
  intro C D T N h k x bundle placement selectedEdge hedge q cfg F root edgeVertex norm blockCells
      fixedPositive touchingRetarget uStart uEnd mR nR mS nS mE nE hR hS hE hFR hFS hFE hRS hRE
      hSE eStart eEnd tStart tEnd
  let swapExact (A B D : ProtoTile) (E : ExactTileInterfaceTriple A B D) :
      ExactTileInterfaceTriple B A D :=
    { point := E.point
      otherAB := E.otherAB
      otherBC := E.otherCA
      otherCA := E.otherBC
      pathAB := by simpa [Set.inter_comm] using E.pathAB
      pathBC := by simpa [Set.inter_comm] using E.pathCA
      pathCA := by simpa [Set.inter_comm] using E.pathBC
      unique_common := by
        intro y
        simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
          E.unique_common y }
  have cycleExact (A B D : ProtoTile) (E : ExactTileInterfaceTriple A B D) :
      ExactTileInterfaceTriple D A B :=
    { point := E.point
      otherAB := E.otherCA
      otherBC := E.otherAB
      otherCA := E.otherBC
      pathAB := E.pathCA
      pathBC := E.pathAB
      pathCA := E.pathBC
      unique_common := by
        intro y
        simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
          E.unique_common y }
  have retargetExactFirst (A A' B D : ProtoTile)
      (hcell : A.cells = A'.cells)
      (hanchor : A.cells = ∅ → A.anchor = A'.anchor)
      (E : ExactTileInterfaceTriple A B D) : ExactTileInterfaceTriple A' B D := by
    have hobs := ProtoTileObservableExtensionality A A' hcell hanchor
    have hedge : FootprintEdges A = FootprintEdges A' := by
      simp only [FootprintEdges]
      rw [hcell]
    exact
      { point := E.point
        otherAB := E.otherAB
        otherBC := E.otherBC
        otherCA := E.otherCA
        pathAB := by simpa [hobs.1, hedge] using E.pathAB
        pathBC := E.pathBC
        pathCA := by simpa [hobs.1, hedge] using E.pathCA
        unique_common := by intro y; simpa [hobs.1] using E.unique_common y }
  let oldRoot := TileTranslation F placement.rightNeighborDisplacement
  let startCompanion := TileTranslation F uStart
  let endCompanion := TileTranslation F uEnd
  have oldCells : oldRoot.cells = root.cells := placement.right_neighbor_cells.symm
  have oldAnchor : oldRoot.cells = ∅ → oldRoot.anchor = root.anchor := by
    intro he
    have hr : root.cells = ∅ := by rw [← oldCells]; exact he
    exact (placement.right_neighbor_empty_anchor hr).symm
  let start0 := swapExact F oldRoot startCompanion eStart
  let end0 := cycleExact F endCompanion oldRoot eEnd
  let startData := retargetExactFirst oldRoot root F startCompanion
    oldCells oldAnchor start0
  let endData := retargetExactFirst oldRoot root F endCompanion
    oldCells oldAnchor end0
  have startTouch0 : TouchingTriple oldRoot F startCompanion :=
    ((TouchingTriplePermutations F oldRoot startCompanion).mp tStart).2.1
  have startTouching : TouchingTriple root F startCompanion :=
    touchingRetarget oldRoot root F F startCompanion startCompanion
      oldCells oldAnchor rfl (by simp) rfl (by simp) startTouch0
  have endTouch0 : TouchingTriple oldRoot F endCompanion := by
    have h := (TouchingTriplePermutations F endCompanion oldRoot).mp tEnd
    exact h.2.2.2.1
  have endTouching : TouchingTriple root F endCompanion :=
    touchingRetarget oldRoot root F F endCompanion endCompanion
      oldCells oldAnchor rfl (by simp) rfl (by simp) endTouch0
  have latticeStart : LatticeTile startCompanion :=
    (TileDiskAreaCovariance F uStart).1.mp norm.normalized_fixed_lattice
  have latticeEnd : LatticeTile endCompanion :=
    (TileDiskAreaCovariance F uEnd).1.mp norm.normalized_fixed_lattice
  have zeroCells : (TileTranslation F (0 : GaussianInt)).cells = F.cells := by
    ext z
    simp [TileTranslation, GaussianTranslation]
  have disjFR : Disjoint F.cells oldRoot.cells := by
    rw [← zeroCells]
    simpa [oldRoot, hR] using blockCells.2 0 0 mR nR hFR
  have disjFS : Disjoint F.cells startCompanion.cells := by
    rw [← zeroCells]
    simpa [startCompanion, hS] using blockCells.2 0 0 mS nS hFS
  have disjFE : Disjoint F.cells endCompanion.cells := by
    rw [← zeroCells]
    simpa [endCompanion, hE] using blockCells.2 0 0 mE nE hFE
  have disjRS : Disjoint oldRoot.cells startCompanion.cells := by
    simpa [oldRoot, startCompanion, hR, hS] using
      blockCells.2 mR nR mS nS hRS
  have disjRE : Disjoint oldRoot.cells endCompanion.cells := by
    simpa [oldRoot, endCompanion, hR, hE] using
      blockCells.2 mR nR mE nE hRE
  have disjSE : Disjoint startCompanion.cells endCompanion.cells := by
    simpa [startCompanion, endCompanion, hS, hE] using
      blockCells.2 mS nS mE nE hSE
  have rootFixed : Disjoint root.cells F.cells := by
    rw [← oldCells]
    exact disjFR.symm
  have rootStart : Disjoint root.cells startCompanion.cells := by
    rw [← oldCells]
    exact disjRS
  have rootEnd : Disjoint root.cells endCompanion.cells := by
    rw [← oldCells]
    exact disjRE
  have pointRoot : bundle.normalizedPoint ∈ FootprintVertices root := by
    rw [← PositiveCurvatureTileOdometerDomain _ _ _ fixedPositive
      norm.normalized_root_odometer]
    exact norm.normalized_point_root_domain
  have pointFixed : bundle.normalizedPoint ∈ FootprintVertices F := by
    rw [← PositiveCurvatureTileOdometerDomain _ _ _
      norm.normalizedFixedCircle.property norm.normalized_fixed_odometer]
    exact norm.normalized_point_fixed_domain
  have crossed := ExactTileInterfaceDisjointCompanionEndpoints
    root F startCompanion endCompanion startData endData
    norm.normalized_root_lattice norm.normalized_fixed_lattice
    latticeStart latticeEnd startTouching endTouching rootStart disjFS disjSE
  exact ⟨{
    startCompanion := startCompanion
    endCompanion := endCompanion
    startData := startData
    endData := endData
    normalized_point_on_start_path := ⟨pointRoot, pointFixed⟩
    interface_endpoints := crossed.2
    root_lattice := norm.normalized_root_lattice
    fixed_lattice := norm.normalized_fixed_lattice
    start_lattice := latticeStart
    end_lattice := latticeEnd
    root_fixed_disjoint := rootFixed
    root_start_disjoint := rootStart
    fixed_start_disjoint := disjFS
    root_end_disjoint := rootEnd
    fixed_end_disjoint := disjFE
    start_end_disjoint := disjSE
    start_touching := startTouching
    end_touching := endTouching }, rfl, rfl, crossed.1⟩

private theorem coordinateFactsApos :
    (by
      classical
      exact
        ((0, 0) : Int × Int) ≠ (1, 1) ∧ ((0, 0) : Int × Int) ≠ (1, 0) ∧ ((0, 0) : Int × Int) ≠
            (0, 1) ∧ ((1, 1) : Int × Int) ≠ (1, 0) ∧ ((1, 1) : Int × Int) ≠ (0, 1) ∧ ((1, 0) :
            Int × Int) ≠ (0, 1) ) := by
  classical
  decide +kernel

private theorem coordinateFactsAneg :
    (by
      classical
      exact
        ((0, 0) : Int × Int) ≠ (-1, -1) ∧ ((0, 0) : Int × Int) ≠ (-1, 0) ∧ ((0, 0) : Int × Int) ≠
            (0, -1) ∧ ((-1, -1) : Int × Int) ≠ (-1, 0) ∧ ((-1, -1) : Int × Int) ≠ (0, -1) ∧ ((-1,
            0) : Int × Int) ≠ (0, -1) ) := by
  classical
  decide +kernel

private theorem coordinateFactsBpos :
    (by
      classical
      exact
        ((0, 0) : Int × Int) ≠ (-1, 0) ∧ ((0, 0) : Int × Int) ≠ (0, 1) ∧ ((0, 0) : Int × Int) ≠
            (-1, -1) ∧ ((-1, 0) : Int × Int) ≠ (0, 1) ∧ ((-1, 0) : Int × Int) ≠ (-1, -1) ∧ ((0,
            1) : Int × Int) ≠ (-1, -1) ) := by
  classical
  decide +kernel

private theorem coordinateFactsBneg :
    (by
      classical
      exact
        ((0, 0) : Int × Int) ≠ (1, 0) ∧ ((0, 0) : Int × Int) ≠ (0, -1) ∧ ((0, 0) : Int × Int) ≠
            (1, 1) ∧ ((1, 0) : Int × Int) ≠ (0, -1) ∧ ((1, 0) : Int × Int) ≠ (1, 1) ∧ ((0, -1) :
            Int × Int) ≠ (1, 1) ) := by
  classical
  decide +kernel

private theorem coordinateFactsCpos :
    (by
      classical
      exact
        ((0, 0) : Int × Int) ≠ (0, -1) ∧ ((0, 0) : Int × Int) ≠ (-1, -1) ∧ ((0, 0) : Int × Int) ≠
            (1, 0) ∧ ((0, -1) : Int × Int) ≠ (-1, -1) ∧ ((0, -1) : Int × Int) ≠ (1, 0) ∧ ((-1,
            -1) : Int × Int) ≠ (1, 0) ) := by
  classical
  decide +kernel

private theorem coordinateFactsCneg :
    (by
      classical
      exact
        ((0, 0) : Int × Int) ≠ (0, 1) ∧ ((0, 0) : Int × Int) ≠ (1, 1) ∧ ((0, 0) : Int × Int) ≠
            (-1, 0) ∧ ((0, 1) : Int × Int) ≠ (1, 1) ∧ ((0, 1) : Int × Int) ≠ (-1, 0) ∧ ((1, 1) :
            Int × Int) ≠ (-1, 0) ) := by
  classical
  decide +kernel

private theorem turnAdd :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), GaussianQuarterTurn (a + b) =
            GaussianQuarterTurn a + GaussianQuarterTurn b ) := by
  classical
  intro a b
  rcases a with ⟨ar, ai⟩
  rcases b with ⟨br, bi⟩
  apply Zsqrtd.ext <;> simp [GaussianQuarterTurn]; ring

private theorem incomingSum :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0) + BandVectors.1 (q 3) (q 0) = 0 )
 := by
  classical
  intro C D T N h k x bundle q
  let cfg := bundle.configuration
  simpa [Fin.sum_univ_succ, add_assoc] using
    (IncomingSuperbasisRelation q cfg.proper).1

private theorem outgoingSum :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        (∀ (s : Fin 3), GaussianQuarterTurn (BandVectors.1 (q s.succ) (q 0)) = BandVectors.1 (q
            0) (q s.succ)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), GaussianQuarterTurn (a +
            b) = GaussianQuarterTurn a + GaussianQuarterTurn b) → ((BandVectors.1 (q 1) (q 0) +
            BandVectors.1 (q 2) (q 0) + BandVectors.1 (q 3) (q 0) = 0) → (BandVectors.1 (q 0) (q
            1) + BandVectors.1 (q 0) (q 2) + BandVectors.1 (q 0) (q 3) = 0))) ) := by
  classical
  intro C D T N h k x bundle q turnOutgoing turnAdd incomingSum
  have h0 : GaussianQuarterTurn (BandVectors.1 (q 1) (q 0)) =
      BandVectors.1 (q 0) (q 1) := by simpa using turnOutgoing 0
  have h1 : GaussianQuarterTurn (BandVectors.1 (q 2) (q 0)) =
      BandVectors.1 (q 0) (q 2) := by simpa using turnOutgoing 1
  have h2 : GaussianQuarterTurn (BandVectors.1 (q 3) (q 0)) =
      BandVectors.1 (q 0) (q 3) := by simpa using turnOutgoing 2
  rw [← h0, ← h1, ← h2]
  calc
    _ = GaussianQuarterTurn
        (BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0) +
          BandVectors.1 (q 3) (q 0)) := by rw [turnAdd, turnAdd]
    _ = 0 := by rw [incomingSum]; rfl

private theorem period2 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        (BandVectors.1 (q 0) (q 1) + BandVectors.1 (q 0) (q 2) + BandVectors.1 (q 0) (q 3) = 0) →
            ((BandVectors.1 (q 0) (q 1) = placement.layout.u) → ((BandVectors.1 (q 0) (q 2) =
            placement.layout.v) → (BandVectors.1 (q 0) (q 3) = -placement.layout.u -
            placement.layout.v))) ) := by
  classical
  intro C D T N h k x bundle placement q outgoingSum period0 period1
  rw [← period0, ← period1]
  have hthird : BandVectors.1 (q 0) (q 3) =
      -(BandVectors.1 (q 0) (q 1) + BandVectors.1 (q 0) (q 2)) := by
    linear_combination outgoingSum
  rw [hthird]
  abel

private theorem geometryFields :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), ∀ (selectedEdge : Finset GaussianInt),
        let q := bundle.normalizedPresentation
        let cfg := bundle.configuration
        let F := bundle.normalizedFixed
        let root := bundle.normalizedRoot
        ∀ (edgeVertex : ∀ (tile : ProtoTile), (tile.cells.Nonempty) → (∀ (edge : Finset
            GaussianInt), (edge ∈ FootprintEdges tile) → (∀ (point : GaussianInt), (point ∈ edge)
            → (point ∈ FootprintVertices tile)))),
        let norm : BandOrderedGeneralRightNormalizationCertificate C T N h k x := {
          presentation := bundle.presentation
          presentation_proper := bundle.presentation_proper
          presentation_child := bundle.presentation_child
          parentRotation := bundle.parentRotation
          symmetry := bundle.symmetry
          rotatedPresentation := bundle.rotatedPresentation
          rotated_presentation_eq := bundle.rotated_presentation_eq
          normalizedPresentation := q
          normalized_presentation_eq := bundle.normalized_presentation_eq
          configuration := cfg
          normalizedCircle := bundle.normalizedCircle
          normalized_circle_eq := bundle.normalized_circle_eq
          normalizedFixedCircle := bundle.normalizedCircle
          normalized_fixed_circle_eq := by
            calc
              bundle.normalizedCircle.1.1 = q 0 := bundle.normalized_circle_eq.symm
              _ = BandPackingSymmetryCircleAction bundle.symmetry C.1.1 := by
                have hq0 := congrFun bundle.normalized_presentation_eq 0
                calc
                  q 0 = BandPackingSymmetryCircleAction bundle.symmetry
                      (bundle.rotatedPresentation 0) := by
                        simpa [BandPackingSymmetryQuadrupleAction] using hq0
                  _ = BandPackingSymmetryCircleAction bundle.symmetry C.1.1 := by
                        rw [bundle.rotated_presentation_eq]
                        simp [bundle.presentation_child]
          normalizedRoot := root
          normalizedFixed := F
          normalizedRootFunction := bundle.normalizedRootFunction
          normalizedFixedFunction := bundle.normalizedFixedFunction
          normalizedPoint := bundle.normalizedPoint
          normalized_root_eq := bundle.normalized_root_eq
          normalized_fixed_eq := bundle.normalized_fixed_eq
          normalized_root_function_eq := bundle.normalized_root_function_eq
          normalized_fixed_function_eq := bundle.normalized_fixed_function_eq
          normalized_point_eq := bundle.normalized_point_eq
          normalized_point_root_domain := by
            obtain ⟨edge, hp, he⟩ := bundle.edgeAtPoint
            have hne := (LatticeTileGridStructure root bundle.root_lattice).1.1
            have hvert := edgeVertex root hne edge he.1 bundle.normalizedPoint hp
            have hdom := PositiveCurvatureTileOdometerDomain (q 0) root
              bundle.normalizedRootFunction (ProperBandCurvatureStructure q cfg.proper).1
              bundle.normalized_root_odometer
            exact (Set.ext_iff.mp hdom bundle.normalizedPoint).mpr hvert
          normalized_point_fixed_domain := by
            obtain ⟨edge, hp, he⟩ := bundle.edgeAtPoint
            have hne := (LatticeTileGridStructure F bundle.fixed_lattice).1.1
            have hvert := edgeVertex F hne edge he.2 bundle.normalizedPoint hp
            have hdom := PositiveCurvatureTileOdometerDomain
              bundle.normalizedCircle.1.1 F bundle.normalizedFixedFunction
              bundle.normalizedCircle.property placement.adjacency.2.1
            exact (Set.ext_iff.mp hdom bundle.normalizedPoint).mpr hvert
          normalized_root_odometer := bundle.normalized_root_odometer
          normalized_fixed_odometer := placement.adjacency.2.1
          normalized_root_lattice := bundle.root_lattice
          normalized_fixed_lattice := bundle.fixed_lattice
          normalizedRootSlope := bundle.normalizedRootSlope
          normalizedFixedSlope := bundle.normalizedFixedSlope
          normalized_root_slope := bundle.normalized_root_slope
          normalized_fixed_slope := bundle.normalized_fixed_slope
          pieces := bundle.pieces
          functions := bundle.functions
          root_band := bundle.root_band
          piece_odometer := bundle.piece_odometer
          piece_cell_cover := bundle.piece_cell_cover
          piece_footprint := bundle.piece_footprint
          piece_centroid := bundle.piece_centroid
          function_domain_cover := bundle.function_domain_cover
          function_restriction := bundle.function_restriction
          function_compatibility := bundle.function_compatibility
          piece_slope := bundle.piece_slope
          adjacency := placement.adjacency
          layout := placement.layout
          fixed_quarter_turn := TileT2QuarterTurn q cfg bundle.normalizedCircle F placement.layout
          rightFirstSlot := placement.rightFirstSlot
          rightSecondSlot := placement.rightSecondSlot
          rightDirectionSlot := placement.rightDirectionSlot
          right_slots_cyclic := placement.right_slots_cyclic
          rightNeighborPositive := placement.rightNeighborPositive
          right_adjacency_centroid := placement.right_adjacency_centroid
          right_adjacency_slope_real := by
            have hroot : placement.rightRootSlope = bundle.normalizedRootSlope :=
              Option.some.inj (placement.right_root_slope.symm.trans
                bundle.normalized_root_slope)
            have hf : placement.rightFixedSlope = bundle.normalizedFixedSlope :=
              Option.some.inj (placement.right_fixed_slope.symm.trans
                bundle.normalized_fixed_slope)
            simpa [hroot, hf, q] using placement.right_adjacency_slope_real
          right_adjacency_slope_imag := by
            have hroot : placement.rightRootSlope = bundle.normalizedRootSlope :=
              Option.some.inj (placement.right_root_slope.symm.trans
                bundle.normalized_root_slope)
            have hf : placement.rightFixedSlope = bundle.normalizedFixedSlope :=
              Option.some.inj (placement.right_fixed_slope.symm.trans
                bundle.normalized_fixed_slope)
            simpa [hroot, hf, q] using placement.right_adjacency_slope_imag
          rightNeighborDisplacement := placement.rightNeighborDisplacement
          right_neighbor_displacement := placement.right_neighbor_displacement
          right_neighbor_cells := placement.right_neighbor_cells
          right_neighbor_empty_anchor := placement.right_neighbor_empty_anchor
          firstBoundarySign := placement.firstBoundarySign
          secondBoundarySign := placement.secondBoundarySign
          boundary_signs := placement.boundary_signs
          first_boundary_cells := placement.first_boundary_cells
          first_boundary_empty_anchor := placement.first_boundary_empty_anchor
          first_boundary_footprint := placement.first_boundary_footprint
          first_boundary_domain := placement.first_boundary_domain
          second_boundary_cells := placement.second_boundary_cells
          second_boundary_empty_anchor := placement.second_boundary_empty_anchor
          second_boundary_footprint := placement.second_boundary_footprint
          second_boundary_domain := placement.second_boundary_domain
          normalized_star := bundle.normalized_star }
        let P := placement.layout.P
        let u := placement.layout.u
        let v := placement.layout.v
        let selectedPath : Prop :=
            (∃ selectedStart selectedEnd : GaussianInt,
              SimpleGridPathBetween
                (FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                (FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                selectedStart selectedEnd ∧
              selectedEdge ∈
                FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex) ∧
              bundle.normalizedPoint ∈ selectedEdge)
        (selectedPath) → (∀ (g : BandOrderedGeneralRightInterfaceCertificate norm), ∀ (W :
            ProtoTile), ∀ (X : ProtoTile), ∀ (R1 : ExactTileInterfaceTriple F g.startCompanion
            W), ∀ (R2 : ExactTileInterfaceTriple F g.endCompanion X), (FootprintVertices W ⊆
            FootprintVertices root) → ((FootprintVertices X ⊆ FootprintVertices root) →
            ((g.startData.point ≠ g.endData.point) → (R1.point = g.startData.point ∧ R2.point =
            g.endData.point ∧ LatticeTile root ∧ LatticeTile F ∧ LatticeTile g.startCompanion ∧
            LatticeTile g.endCompanion ∧ Disjoint root.cells g.startCompanion.cells ∧ Disjoint
            F.cells g.startCompanion.cells ∧ Disjoint root.cells g.endCompanion.cells ∧ Disjoint
            F.cells g.endCompanion.cells ∧ Disjoint g.startCompanion.cells g.endCompanion.cells ∧
            TouchingTriple root F g.startCompanion ∧ TouchingTriple root F g.endCompanion ∧
            g.startData.point ≠ g.endData.point ∧ g.endData.point = g.startData.otherAB ∧
            g.endData.otherAB = g.startData.point ∧ selectedPath)))) ) := by
  classical
  intro C D T N h k x bundle placement selectedEdge q cfg F root edgeVertex norm P u v
      selectedPath originalSelectedPath g W X R1 R2 hW hX hneq
  have hp1 := (R1.unique_common R1.point).2 rfl
  have hp2 := (R2.unique_common R2.point).2 rfl
  have hp1' : R1.point ∈ FootprintVertices F ∧
      R1.point ∈ FootprintVertices g.startCompanion ∧
      R1.point ∈ FootprintVertices W := by
    simpa only [Set.mem_inter_iff, and_assoc] using hp1
  have hp2' : R2.point ∈ FootprintVertices F ∧
      R2.point ∈ FootprintVertices g.endCompanion ∧
      R2.point ∈ FootprintVertices X := by
    simpa only [Set.mem_inter_iff, and_assoc] using hp2
  rcases hp1' with ⟨hF1, hC1, hW1⟩
  rcases hp2' with ⟨hF2, hC2, hX2⟩
  have hroot1 : R1.point ∈ FootprintVertices root := hW hW1
  have hroot2 : R2.point ∈ FootprintVertices root := hX hX2
  have hcommon1 : R1.point ∈ FootprintVertices root ∩
      FootprintVertices F ∩ FootprintVertices g.startCompanion :=
    ⟨⟨hroot1, hF1⟩, hC1⟩
  have hcommon2 : R2.point ∈ FootprintVertices root ∩
      FootprintVertices F ∩ FootprintVertices g.endCompanion :=
    ⟨⟨hroot2, hF2⟩, hC2⟩
  have hpoint1 := (g.startData.unique_common R1.point).mp hcommon1
  have hpoint2 := (g.endData.unique_common R2.point).mp hcommon2
  refine ⟨hpoint1, ?_⟩
  refine ⟨hpoint2, ?_⟩
  refine ⟨g.root_lattice, ?_⟩
  refine ⟨g.fixed_lattice, ?_⟩
  refine ⟨g.start_lattice, ?_⟩
  refine ⟨g.end_lattice, ?_⟩
  refine ⟨g.root_start_disjoint, ?_⟩
  refine ⟨g.fixed_start_disjoint, ?_⟩
  refine ⟨g.root_end_disjoint, ?_⟩
  refine ⟨g.fixed_end_disjoint, ?_⟩
  refine ⟨g.start_end_disjoint, ?_⟩
  refine ⟨g.start_touching, ?_⟩
  refine ⟨g.end_touching, ?_⟩
  refine ⟨hneq, ?_⟩
  refine ⟨g.interface_endpoints.1, ?_⟩
  refine ⟨g.interface_endpoints.2, ?_⟩
  exact originalSelectedPath

private theorem castTriplePointSecond :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (B' : ProtoTile), ∀ (C : ProtoTile), ∀ (h : B =
            B'), ∀ (d : ExactTileInterfaceTriple A B C), (Eq.mp (congrArg (fun Y =>
            ExactTileInterfaceTriple A Y C) h) d).point = d.point ) := by
  classical
  intro A B B' C h d
  cases h
  rfl

private theorem castTriplePointThird :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (C' : ProtoTile), ∀ (h : C =
            C'), ∀ (d : ExactTileInterfaceTriple A B C), (Eq.mp (congrArg (fun Y =>
            ExactTileInterfaceTriple A B Y) h) d).point = d.point ) := by
  classical
  intro A B C C' h d
  cases h
  rfl

private theorem castTripleOtherABSecond :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (B' : ProtoTile), ∀ (C : ProtoTile), ∀ (h : B =
            B'), ∀ (d : ExactTileInterfaceTriple A B C), (Eq.mp (congrArg (fun Y =>
            ExactTileInterfaceTriple A Y C) h) d).otherAB = d.otherAB ) := by
  classical
  intro A B B' C h d
  cases h
  rfl

private theorem castTripleOtherABThird :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (C' : ProtoTile), ∀ (h : C =
            C'), ∀ (d : ExactTileInterfaceTriple A B C), (Eq.mp (congrArg (fun Y =>
            ExactTileInterfaceTriple A B Y) h) d).otherAB = d.otherAB ) := by
  classical
  intro A B C C' h d
  cases h
  rfl

private theorem castRoundTrip :
    (by
      classical
      exact
        ∀ (P : ProtoTile → Type), ∀ {a : ProtoTile}, ∀ {b : ProtoTile}, ∀ (h : a = b), ∀ (z : P
            a), Eq.mpr (congrArg P h) (Eq.mp (congrArg P h) z) = z ) := by
  classical
  intro P a b h z
  cases h
  rfl

private theorem packageGeometry :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), ∀ (selectedEdge : Finset GaussianInt),
        let q := bundle.normalizedPresentation
        let cfg := bundle.configuration
        let F := bundle.normalizedFixed
        let root := bundle.normalizedRoot
        ∀ (edgeVertex : ∀ (tile : ProtoTile), (tile.cells.Nonempty) → (∀ (edge : Finset
            GaussianInt), (edge ∈ FootprintEdges tile) → (∀ (point : GaussianInt), (point ∈ edge)
            → (point ∈ FootprintVertices tile)))),
        let norm : BandOrderedGeneralRightNormalizationCertificate C T N h k x := {
          presentation := bundle.presentation
          presentation_proper := bundle.presentation_proper
          presentation_child := bundle.presentation_child
          parentRotation := bundle.parentRotation
          symmetry := bundle.symmetry
          rotatedPresentation := bundle.rotatedPresentation
          rotated_presentation_eq := bundle.rotated_presentation_eq
          normalizedPresentation := q
          normalized_presentation_eq := bundle.normalized_presentation_eq
          configuration := cfg
          normalizedCircle := bundle.normalizedCircle
          normalized_circle_eq := bundle.normalized_circle_eq
          normalizedFixedCircle := bundle.normalizedCircle
          normalized_fixed_circle_eq := by
            calc
              bundle.normalizedCircle.1.1 = q 0 := bundle.normalized_circle_eq.symm
              _ = BandPackingSymmetryCircleAction bundle.symmetry C.1.1 := by
                have hq0 := congrFun bundle.normalized_presentation_eq 0
                calc
                  q 0 = BandPackingSymmetryCircleAction bundle.symmetry
                      (bundle.rotatedPresentation 0) := by
                        simpa [BandPackingSymmetryQuadrupleAction] using hq0
                  _ = BandPackingSymmetryCircleAction bundle.symmetry C.1.1 := by
                        rw [bundle.rotated_presentation_eq]
                        simp [bundle.presentation_child]
          normalizedRoot := root
          normalizedFixed := F
          normalizedRootFunction := bundle.normalizedRootFunction
          normalizedFixedFunction := bundle.normalizedFixedFunction
          normalizedPoint := bundle.normalizedPoint
          normalized_root_eq := bundle.normalized_root_eq
          normalized_fixed_eq := bundle.normalized_fixed_eq
          normalized_root_function_eq := bundle.normalized_root_function_eq
          normalized_fixed_function_eq := bundle.normalized_fixed_function_eq
          normalized_point_eq := bundle.normalized_point_eq
          normalized_point_root_domain := by
            obtain ⟨edge, hp, he⟩ := bundle.edgeAtPoint
            have hne := (LatticeTileGridStructure root bundle.root_lattice).1.1
            have hvert := edgeVertex root hne edge he.1 bundle.normalizedPoint hp
            have hdom := PositiveCurvatureTileOdometerDomain (q 0) root
              bundle.normalizedRootFunction (ProperBandCurvatureStructure q cfg.proper).1
              bundle.normalized_root_odometer
            exact (Set.ext_iff.mp hdom bundle.normalizedPoint).mpr hvert
          normalized_point_fixed_domain := by
            obtain ⟨edge, hp, he⟩ := bundle.edgeAtPoint
            have hne := (LatticeTileGridStructure F bundle.fixed_lattice).1.1
            have hvert := edgeVertex F hne edge he.2 bundle.normalizedPoint hp
            have hdom := PositiveCurvatureTileOdometerDomain
              bundle.normalizedCircle.1.1 F bundle.normalizedFixedFunction
              bundle.normalizedCircle.property placement.adjacency.2.1
            exact (Set.ext_iff.mp hdom bundle.normalizedPoint).mpr hvert
          normalized_root_odometer := bundle.normalized_root_odometer
          normalized_fixed_odometer := placement.adjacency.2.1
          normalized_root_lattice := bundle.root_lattice
          normalized_fixed_lattice := bundle.fixed_lattice
          normalizedRootSlope := bundle.normalizedRootSlope
          normalizedFixedSlope := bundle.normalizedFixedSlope
          normalized_root_slope := bundle.normalized_root_slope
          normalized_fixed_slope := bundle.normalized_fixed_slope
          pieces := bundle.pieces
          functions := bundle.functions
          root_band := bundle.root_band
          piece_odometer := bundle.piece_odometer
          piece_cell_cover := bundle.piece_cell_cover
          piece_footprint := bundle.piece_footprint
          piece_centroid := bundle.piece_centroid
          function_domain_cover := bundle.function_domain_cover
          function_restriction := bundle.function_restriction
          function_compatibility := bundle.function_compatibility
          piece_slope := bundle.piece_slope
          adjacency := placement.adjacency
          layout := placement.layout
          fixed_quarter_turn := TileT2QuarterTurn q cfg bundle.normalizedCircle F placement.layout
          rightFirstSlot := placement.rightFirstSlot
          rightSecondSlot := placement.rightSecondSlot
          rightDirectionSlot := placement.rightDirectionSlot
          right_slots_cyclic := placement.right_slots_cyclic
          rightNeighborPositive := placement.rightNeighborPositive
          right_adjacency_centroid := placement.right_adjacency_centroid
          right_adjacency_slope_real := by
            have hroot : placement.rightRootSlope = bundle.normalizedRootSlope :=
              Option.some.inj (placement.right_root_slope.symm.trans
                bundle.normalized_root_slope)
            have hf : placement.rightFixedSlope = bundle.normalizedFixedSlope :=
              Option.some.inj (placement.right_fixed_slope.symm.trans
                bundle.normalized_fixed_slope)
            simpa [hroot, hf, q] using placement.right_adjacency_slope_real
          right_adjacency_slope_imag := by
            have hroot : placement.rightRootSlope = bundle.normalizedRootSlope :=
              Option.some.inj (placement.right_root_slope.symm.trans
                bundle.normalized_root_slope)
            have hf : placement.rightFixedSlope = bundle.normalizedFixedSlope :=
              Option.some.inj (placement.right_fixed_slope.symm.trans
                bundle.normalized_fixed_slope)
            simpa [hroot, hf, q] using placement.right_adjacency_slope_imag
          rightNeighborDisplacement := placement.rightNeighborDisplacement
          right_neighbor_displacement := placement.right_neighbor_displacement
          right_neighbor_cells := placement.right_neighbor_cells
          right_neighbor_empty_anchor := placement.right_neighbor_empty_anchor
          firstBoundarySign := placement.firstBoundarySign
          secondBoundarySign := placement.secondBoundarySign
          boundary_signs := placement.boundary_signs
          first_boundary_cells := placement.first_boundary_cells
          first_boundary_empty_anchor := placement.first_boundary_empty_anchor
          first_boundary_footprint := placement.first_boundary_footprint
          first_boundary_domain := placement.first_boundary_domain
          second_boundary_cells := placement.second_boundary_cells
          second_boundary_empty_anchor := placement.second_boundary_empty_anchor
          second_boundary_footprint := placement.second_boundary_footprint
          second_boundary_domain := placement.second_boundary_domain
          normalized_star := bundle.normalized_star }
        let P := placement.layout.P
        let u := placement.layout.u
        let v := placement.layout.v
        let selectedPath : Prop :=
            (∃ selectedStart selectedEnd : GaussianInt,
              SimpleGridPathBetween
                (FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                (FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                selectedStart selectedEnd ∧
              selectedEdge ∈
                FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex) ∧
              bundle.normalizedPoint ∈ selectedEdge)
        let rightGeometry := fun (i j : Fin 3) (sgn : GaussianInt)
            (firstSign secondSign : Bool) ↦
          let firstCompanion := TileTranslation F
            (sgn * BandVectors.1 (q 0) (q i.succ))
          let secondCompanion := TileTranslation F
            (sgn * BandVectors.1 (q 0) (q j.succ))
          let firstPiece := TileTranslation (placement.layout.P i firstSign)
            placement.rightNeighborDisplacement
          let secondPiece := TileTranslation (placement.layout.P j secondSign)
            placement.rightNeighborDisplacement
          ∃ firstBoundaryData : ExactTileInterfaceTriple F firstCompanion firstPiece,
            ∃ secondBoundaryData : ExactTileInterfaceTriple F secondCompanion secondPiece,
              ∃ firstData : ExactTileInterfaceTriple root F firstCompanion,
                ∃ secondData : ExactTileInterfaceTriple root F secondCompanion,
                  firstBoundaryData.point = firstData.point ∧
                  secondBoundaryData.point = secondData.point ∧
                  LatticeTile root ∧ LatticeTile F ∧ LatticeTile firstCompanion ∧
                  LatticeTile secondCompanion ∧ Disjoint root.cells firstCompanion.cells ∧
                  Disjoint F.cells firstCompanion.cells ∧
                  Disjoint root.cells secondCompanion.cells ∧
                  Disjoint F.cells secondCompanion.cells ∧
                  Disjoint firstCompanion.cells secondCompanion.cells ∧
                  TouchingTriple root F firstCompanion ∧
                  TouchingTriple root F secondCompanion ∧
                  firstData.point ≠ secondData.point ∧
                  secondData.point = firstData.otherAB ∧
                  secondData.otherAB = firstData.point ∧ selectedPath
        (∀ (g : BandOrderedGeneralRightInterfaceCertificate norm), ∀ (W : ProtoTile), ∀ (X :
            ProtoTile), ∀ (R1 : ExactTileInterfaceTriple F g.startCompanion W), ∀ (R2 :
            ExactTileInterfaceTriple F g.endCompanion X), (FootprintVertices W ⊆
            FootprintVertices root) → ((FootprintVertices X ⊆ FootprintVertices root) →
            ((g.startData.point ≠ g.endData.point) → (R1.point = g.startData.point ∧ R2.point =
            g.endData.point ∧ LatticeTile root ∧ LatticeTile F ∧ LatticeTile g.startCompanion ∧
            LatticeTile g.endCompanion ∧ Disjoint root.cells g.startCompanion.cells ∧ Disjoint
            F.cells g.startCompanion.cells ∧ Disjoint root.cells g.endCompanion.cells ∧ Disjoint
            F.cells g.endCompanion.cells ∧ Disjoint g.startCompanion.cells g.endCompanion.cells ∧
            TouchingTriple root F g.startCompanion ∧ TouchingTriple root F g.endCompanion ∧
            g.startData.point ≠ g.endData.point ∧ g.endData.point = g.startData.otherAB ∧
            g.endData.otherAB = g.startData.point ∧ selectedPath)))) → ((∀ (A : ProtoTile), ∀ (B
            : ProtoTile), ∀ (B' : ProtoTile), ∀ (C : ProtoTile), ∀ (h : B = B'), ∀ (d :
            ExactTileInterfaceTriple A B C), (Eq.mp (congrArg (fun Y => ExactTileInterfaceTriple
            A Y C) h) d).point = d.point) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C :
            ProtoTile), ∀ (C' : ProtoTile), ∀ (h : C = C'), ∀ (d : ExactTileInterfaceTriple A B
            C), (Eq.mp (congrArg (fun Y => ExactTileInterfaceTriple A B Y) h) d).point = d.point)
            → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (C' : ProtoTile), ∀ (h
            : C = C'), ∀ (d : ExactTileInterfaceTriple A B C), (Eq.mp (congrArg (fun Y =>
            ExactTileInterfaceTriple A B Y) h) d).otherAB = d.otherAB) → (∀ (i : Fin 3), ∀ (j :
            Fin 3), ∀ (sgn : GaussianInt), ∀ (s₁ : Bool), ∀ (s₂ : Bool), ∀ (g :
            BandOrderedGeneralRightInterfaceCertificate norm), (g.startCompanion = TileTranslation F
            (sgn * BandVectors.1 (q 0) (q i.succ))) → ((g.endCompanion = TileTranslation F
            (sgn * BandVectors.1 (q 0) (q j.succ))) → ((g.startData.point ≠ g.endData.point) →
                ((ExactTileInterfaceTriple F g.startCompanion
            (TileTranslation (placement.layout.P i s₁)
              placement.rightNeighborDisplacement)) → ((ExactTileInterfaceTriple F g.endCompanion
            (TileTranslation (placement.layout.P j s₂)
              placement.rightNeighborDisplacement)) → ((FootprintVertices
            (TileTranslation (placement.layout.P i s₁)
              placement.rightNeighborDisplacement) ⊆ FootprintVertices root) → ((FootprintVertices
            (TileTranslation (placement.layout.P j s₂)
              placement.rightNeighborDisplacement) ⊆ FootprintVertices root) → (rightGeometry i j
                  sgn s₁ s₂))))))))))) ) := by
  classical
  intro C D T N h k x bundle placement selectedEdge q cfg F root edgeVertex norm P u v
      selectedPath rightGeometry geometryFields castTriplePointSecond castTriplePointThird
      castTripleOtherABThird i j sgn s₁ s₂ g hgs hge hneq R1 R2 hW hX
  dsimp [rightGeometry]
  let R1out : ExactTileInterfaceTriple F
      (TileTranslation F (sgn * BandVectors.1 (q 0) (q i.succ)))
      (TileTranslation (placement.layout.P i s₁)
        placement.rightNeighborDisplacement) :=
    Eq.mp (congrArg (fun Y => ExactTileInterfaceTriple F Y
      (TileTranslation (placement.layout.P i s₁)
        placement.rightNeighborDisplacement)) hgs) R1
  let R2out : ExactTileInterfaceTriple F
      (TileTranslation F (sgn * BandVectors.1 (q 0) (q j.succ)))
      (TileTranslation (placement.layout.P j s₂)
        placement.rightNeighborDisplacement) :=
    Eq.mp (congrArg (fun Y => ExactTileInterfaceTriple F Y
      (TileTranslation (placement.layout.P j s₂)
        placement.rightNeighborDisplacement)) hge) R2
  let startData : ExactTileInterfaceTriple root F
      (TileTranslation F (sgn * BandVectors.1 (q 0) (q i.succ))) :=
    Eq.mp (congrArg (fun Y => ExactTileInterfaceTriple root F Y) hgs)
      g.startData
  let endData : ExactTileInterfaceTriple root F
      (TileTranslation F (sgn * BandVectors.1 (q 0) (q j.succ))) :=
    Eq.mp (congrArg (fun Y => ExactTileInterfaceTriple root F Y) hge)
      g.endData
  have fields := geometryFields g _ _ R1 R2 hW hX hneq
  have p1 := castTriplePointSecond F g.startCompanion
    (TileTranslation F (sgn * BandVectors.1 (q 0) (q i.succ)))
    (TileTranslation (placement.layout.P i s₁)
      placement.rightNeighborDisplacement) hgs R1
  have p2 := castTriplePointSecond F g.endCompanion
    (TileTranslation F (sgn * BandVectors.1 (q 0) (q j.succ)))
    (TileTranslation (placement.layout.P j s₂)
      placement.rightNeighborDisplacement) hge R2
  have p3 := castTriplePointThird root F g.startCompanion
    (TileTranslation F (sgn * BandVectors.1 (q 0) (q i.succ))) hgs g.startData
  have p4 := castTriplePointThird root F g.endCompanion
    (TileTranslation F (sgn * BandVectors.1 (q 0) (q j.succ))) hge g.endData
  have o1 := castTripleOtherABThird root F g.startCompanion
    (TileTranslation F (sgn * BandVectors.1 (q 0) (q i.succ))) hgs g.startData
  have o2 := castTripleOtherABThird root F g.endCompanion
    (TileTranslation F (sgn * BandVectors.1 (q 0) (q j.succ))) hge g.endData
  have fields' := fields
  rw [← p1, ← p2, ← p3, ← p4, ← o1, ← o2] at fields'
  refine ⟨R1out, R2out, startData, endData, ?_⟩
  simpa only [hgs, hge, R1out, R2out, startData, endData,
    castRoundTrip] using fields'

private theorem firstBoundarySubset :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let root := bundle.normalizedRoot
        FootprintVertices (TileTranslation (placement.layout.P placement.rightFirstSlot
            placement.firstBoundarySign) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root ) := by
  classical
  intro C D T N h k x bundle placement root
  rw [← placement.first_boundary_footprint]
  exact bundle.piece_footprint placement.rightFirstSlot
    placement.firstBoundarySign

private theorem secondBoundarySubset :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let root := bundle.normalizedRoot
        FootprintVertices (TileTranslation (placement.layout.P placement.rightSecondSlot
            placement.secondBoundarySign) placement.rightNeighborDisplacement) ⊆
            FootprintVertices root ) := by
  classical
  intro C D T N h k x bundle placement root
  rw [← placement.second_boundary_footprint]
  exact bundle.piece_footprint placement.rightSecondSlot
    placement.secondBoundarySign

private theorem hRAt1171 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        (placement.rightDirectionSlot = (2 : Fin (3 : ℕ))) → ((placement.rightNeighborPositive =
            false) → (placement.rightNeighborDisplacement = -BandVectors.1 (q 0) (q 3))) ) := by
  classical
  intro C D T N h k x bundle placement q hk hpos
  simpa [hpos, hk] using placement.right_neighbor_displacement

private theorem tStartAt1193 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (ell : Fin 3), TouchingTriple F (TileTranslation F (-BandVectors.1 (q 0) (q
            ell.succ))) (TileTranslation F (BandVectors.1 (q 0) (q (ell + 1).succ)))) →
            ((placement.rightNeighborDisplacement = -BandVectors.1 (q 0) (q 3)) → (TouchingTriple
            F (TileTranslation F placement.rightNeighborDisplacement) (TileTranslation F ((1 :
            GaussianInt) * BandVectors.1 (q 0) (q 1))))) ) := by
  classical
  intro C D T N h k x bundle placement q F touchingMinus hR
  simpa [hR] using touchingMinus 2

private theorem tEndAt1197 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (ell : Fin 3), TouchingTriple F (TileTranslation F (BandVectors.1 (q 0) (q ell.succ)))
            (TileTranslation F (-BandVectors.1 (q 0) (q (ell + 1).succ)))) →
            ((placement.rightNeighborDisplacement = -BandVectors.1 (q 0) (q 3)) → (TouchingTriple
            F (TileTranslation F ((1 : GaussianInt) * BandVectors.1 (q 0) (q 2)))
            (TileTranslation F placement.rightNeighborDisplacement))) ) := by
  classical
  intro C D T N h k x bundle placement q F touchingPlus hR
  simpa [hR] using touchingPlus 1

private theorem geomAt1214 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), ∀ (selectedEdge : Finset GaussianInt),
        let q := bundle.normalizedPresentation;
        let cfg := bundle.configuration;
        let F := bundle.normalizedFixed;
        let root := bundle.normalizedRoot;
        ∀ (edgeVertex : ∀ (tile : ProtoTile), (tile.cells.Nonempty) → (∀ (edge : Finset
            GaussianInt), (edge ∈ FootprintEdges tile) → (∀ (point : GaussianInt), (point ∈ edge)
            → (point ∈ FootprintVertices tile)))),
                                                                                               (
        let norm : BandOrderedGeneralRightNormalizationCertificate C T N h k x := {
          presentation := bundle.presentation
          presentation_proper := bundle.presentation_proper
          presentation_child := bundle.presentation_child
          parentRotation := bundle.parentRotation
          symmetry := bundle.symmetry
          rotatedPresentation := bundle.rotatedPresentation
          rotated_presentation_eq := bundle.rotated_presentation_eq
          normalizedPresentation := q
          normalized_presentation_eq := bundle.normalized_presentation_eq
          configuration := cfg
          normalizedCircle := bundle.normalizedCircle
          normalized_circle_eq := bundle.normalized_circle_eq
          normalizedFixedCircle := bundle.normalizedCircle
          normalized_fixed_circle_eq := by
            calc
              bundle.normalizedCircle.1.1 = q 0 := bundle.normalized_circle_eq.symm
              _ = BandPackingSymmetryCircleAction bundle.symmetry C.1.1 := by
                have hq0 := congrFun bundle.normalized_presentation_eq 0
                calc
                  q 0 = BandPackingSymmetryCircleAction bundle.symmetry
                      (bundle.rotatedPresentation 0) := by
                        simpa [BandPackingSymmetryQuadrupleAction] using hq0
                  _ = BandPackingSymmetryCircleAction bundle.symmetry C.1.1 := by
                        rw [bundle.rotated_presentation_eq]
                        simp [bundle.presentation_child]
          normalizedRoot := root
          normalizedFixed := F
          normalizedRootFunction := bundle.normalizedRootFunction
          normalizedFixedFunction := bundle.normalizedFixedFunction
          normalizedPoint := bundle.normalizedPoint
          normalized_root_eq := bundle.normalized_root_eq
          normalized_fixed_eq := bundle.normalized_fixed_eq
          normalized_root_function_eq := bundle.normalized_root_function_eq
          normalized_fixed_function_eq := bundle.normalized_fixed_function_eq
          normalized_point_eq := bundle.normalized_point_eq
          normalized_point_root_domain := by
            obtain ⟨edge, hp, he⟩ := bundle.edgeAtPoint
            have hne := (LatticeTileGridStructure root bundle.root_lattice).1.1
            have hvert := edgeVertex root hne edge he.1 bundle.normalizedPoint hp
            have hdom := PositiveCurvatureTileOdometerDomain (q 0) root
              bundle.normalizedRootFunction (ProperBandCurvatureStructure q cfg.proper).1
              bundle.normalized_root_odometer
            exact (Set.ext_iff.mp hdom bundle.normalizedPoint).mpr hvert
          normalized_point_fixed_domain := by
            obtain ⟨edge, hp, he⟩ := bundle.edgeAtPoint
            have hne := (LatticeTileGridStructure F bundle.fixed_lattice).1.1
            have hvert := edgeVertex F hne edge he.2 bundle.normalizedPoint hp
            have hdom := PositiveCurvatureTileOdometerDomain
              bundle.normalizedCircle.1.1 F bundle.normalizedFixedFunction
              bundle.normalizedCircle.property placement.adjacency.2.1
            exact (Set.ext_iff.mp hdom bundle.normalizedPoint).mpr hvert
          normalized_root_odometer := bundle.normalized_root_odometer
          normalized_fixed_odometer := placement.adjacency.2.1
          normalized_root_lattice := bundle.root_lattice
          normalized_fixed_lattice := bundle.fixed_lattice
          normalizedRootSlope := bundle.normalizedRootSlope
          normalizedFixedSlope := bundle.normalizedFixedSlope
          normalized_root_slope := bundle.normalized_root_slope
          normalized_fixed_slope := bundle.normalized_fixed_slope
          pieces := bundle.pieces
          functions := bundle.functions
          root_band := bundle.root_band
          piece_odometer := bundle.piece_odometer
          piece_cell_cover := bundle.piece_cell_cover
          piece_footprint := bundle.piece_footprint
          piece_centroid := bundle.piece_centroid
          function_domain_cover := bundle.function_domain_cover
          function_restriction := bundle.function_restriction
          function_compatibility := bundle.function_compatibility
          piece_slope := bundle.piece_slope
          adjacency := placement.adjacency
          layout := placement.layout
          fixed_quarter_turn := TileT2QuarterTurn q cfg bundle.normalizedCircle F placement.layout
          rightFirstSlot := placement.rightFirstSlot
          rightSecondSlot := placement.rightSecondSlot
          rightDirectionSlot := placement.rightDirectionSlot
          right_slots_cyclic := placement.right_slots_cyclic
          rightNeighborPositive := placement.rightNeighborPositive
          right_adjacency_centroid := placement.right_adjacency_centroid
          right_adjacency_slope_real := by
            have hroot : placement.rightRootSlope = bundle.normalizedRootSlope :=
              Option.some.inj (placement.right_root_slope.symm.trans
                bundle.normalized_root_slope)
            have hf : placement.rightFixedSlope = bundle.normalizedFixedSlope :=
              Option.some.inj (placement.right_fixed_slope.symm.trans
                bundle.normalized_fixed_slope)
            simpa [hroot, hf, q] using placement.right_adjacency_slope_real
          right_adjacency_slope_imag := by
            have hroot : placement.rightRootSlope = bundle.normalizedRootSlope :=
              Option.some.inj (placement.right_root_slope.symm.trans
                bundle.normalized_root_slope)
            have hf : placement.rightFixedSlope = bundle.normalizedFixedSlope :=
              Option.some.inj (placement.right_fixed_slope.symm.trans
                bundle.normalized_fixed_slope)
            simpa [hroot, hf, q] using placement.right_adjacency_slope_imag
          rightNeighborDisplacement := placement.rightNeighborDisplacement
          right_neighbor_displacement := placement.right_neighbor_displacement
          right_neighbor_cells := placement.right_neighbor_cells
          right_neighbor_empty_anchor := placement.right_neighbor_empty_anchor
          firstBoundarySign := placement.firstBoundarySign
          secondBoundarySign := placement.secondBoundarySign
          boundary_signs := placement.boundary_signs
          first_boundary_cells := placement.first_boundary_cells
          first_boundary_empty_anchor := placement.first_boundary_empty_anchor
          first_boundary_footprint := placement.first_boundary_footprint
          first_boundary_domain := placement.first_boundary_domain
          second_boundary_cells := placement.second_boundary_cells
          second_boundary_empty_anchor := placement.second_boundary_empty_anchor
          second_boundary_footprint := placement.second_boundary_footprint
          second_boundary_domain := placement.second_boundary_domain
          normalized_star := bundle.normalized_star }
        let P := placement.layout.P
        let u := placement.layout.u
        let v := placement.layout.v
        let selectedPath : Prop :=
            (∃ selectedStart selectedEnd : GaussianInt,
              SimpleGridPathBetween
                (FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                (FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                selectedStart selectedEnd ∧
              selectedEdge ∈
                FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex) ∧
              bundle.normalizedPoint ∈ selectedEdge)
        let rightGeometry := fun (i j : Fin 3) (sgn : GaussianInt)
            (firstSign secondSign : Bool) ↦
          let firstCompanion := TileTranslation F
            (sgn * BandVectors.1 (q 0) (q i.succ))
          let secondCompanion := TileTranslation F
            (sgn * BandVectors.1 (q 0) (q j.succ))
          let firstPiece := TileTranslation (placement.layout.P i firstSign)
            placement.rightNeighborDisplacement
          let secondPiece := TileTranslation (placement.layout.P j secondSign)
            placement.rightNeighborDisplacement
          ∃ firstBoundaryData : ExactTileInterfaceTriple F firstCompanion firstPiece,
            ∃ secondBoundaryData : ExactTileInterfaceTriple F secondCompanion secondPiece,
              ∃ firstData : ExactTileInterfaceTriple root F firstCompanion,
                ∃ secondData : ExactTileInterfaceTriple root F secondCompanion,
                  firstBoundaryData.point = firstData.point ∧
                  secondBoundaryData.point = secondData.point ∧
                  LatticeTile root ∧ LatticeTile F ∧ LatticeTile firstCompanion ∧
                  LatticeTile secondCompanion ∧ Disjoint root.cells firstCompanion.cells ∧
                  Disjoint F.cells firstCompanion.cells ∧
                  Disjoint root.cells secondCompanion.cells ∧
                  Disjoint F.cells secondCompanion.cells ∧
                  Disjoint firstCompanion.cells secondCompanion.cells ∧
                  TouchingTriple root F firstCompanion ∧
                  TouchingTriple root F secondCompanion ∧
                  firstData.point ≠ secondData.point ∧
                  secondData.point = firstData.otherAB ∧
                  secondData.otherAB = firstData.point ∧ selectedPath
        (∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (sgn : GaussianInt), ∀ (s₁ : Bool), ∀ (s₂ : Bool), ∀ (g
            : BandOrderedGeneralRightInterfaceCertificate norm), (g.startCompanion =
            TileTranslation F (sgn * BandVectors.1 (q 0) (q i.succ))) → ((g.endCompanion =
            TileTranslation F (sgn * BandVectors.1 (q 0) (q j.succ))) → ((g.startData.point ≠
            g.endData.point) → ((ExactTileInterfaceTriple F g.startCompanion (TileTranslation
            (placement.layout.P i s₁) placement.rightNeighborDisplacement)) →
            ((ExactTileInterfaceTriple F g.endCompanion (TileTranslation (placement.layout.P j
            s₂) placement.rightNeighborDisplacement)) → ((FootprintVertices (TileTranslation
            (placement.layout.P i s₁) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root) → ((FootprintVertices (TileTranslation (placement.layout.P j s₂)
            placement.rightNeighborDisplacement) ⊆ FootprintVertices root) → (rightGeometry i j
            sgn s₁ s₂)))))))) → ((FootprintVertices (TileTranslation (placement.layout.P
            placement.rightFirstSlot placement.firstBoundarySign)
            placement.rightNeighborDisplacement) ⊆ FootprintVertices root) → ((FootprintVertices
            (TileTranslation (placement.layout.P placement.rightSecondSlot
            placement.secondBoundarySign) placement.rightNeighborDisplacement) ⊆
            FootprintVertices root) → ((placement.rightFirstSlot = (0 : Fin (3 : ℕ))) →
            ((placement.rightSecondSlot = (1 : Fin (3 : ℕ))) → ((ExactTileInterfaceTriple
            bundle.normalizedFixed (TileTranslation bundle.normalizedFixed (BandVectors.1
            (bundle.normalizedPresentation (0 : Fin (4 : ℕ))) (bundle.normalizedPresentation
            placement.rightFirstSlot.succ))) (TileTranslation (placement.layout.P
            placement.rightFirstSlot false) placement.rightNeighborDisplacement)) →
            ((ExactTileInterfaceTriple bundle.normalizedFixed (TileTranslation
            bundle.normalizedFixed (BandVectors.1 (bundle.normalizedPresentation (0 : Fin (4 :
            ℕ))) (bundle.normalizedPresentation placement.rightSecondSlot.succ)))
            (TileTranslation (placement.layout.P placement.rightSecondSlot true)
            placement.rightNeighborDisplacement)) → (∀ (g :
                BandOrderedGeneralRightInterfaceCertificate norm), (g.startCompanion =
            TileTranslation F ((1 : GaussianInt) * BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 :
            Fin (4 : ℕ))))) → ((g.endCompanion = TileTranslation F ((1 : GaussianInt) *
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))) → ((g.startData.point ≠
            g.endData.point) → ((placement.firstBoundarySign = false) →
            ((placement.secondBoundarySign = true) → (rightGeometry 0 1 1 false
                true)))))))))))))) := by
  classical
  intro C D T N h k x bundle placement selectedEdge q cfg F root edgeVertex norm P u v
      selectedPath rightGeometry packageGeometry firstBoundarySubset secondBoundarySubset hi hj
      R1 R2 g hgs hge hneq hfirst hsecond
  have R1g : ExactTileInterfaceTriple F g.startCompanion
      (TileTranslation (placement.layout.P 0 false)
        placement.rightNeighborDisplacement) := by
    simpa [hgs, hi] using R1
  have R2g : ExactTileInterfaceTriple F g.endCompanion
      (TileTranslation (placement.layout.P 1 true)
        placement.rightNeighborDisplacement) := by
    simpa [hge, hj] using R2
  have hW : FootprintVertices
      (TileTranslation (placement.layout.P 0 false)
        placement.rightNeighborDisplacement) ⊆ FootprintVertices root := by
    simpa [hi, hfirst] using firstBoundarySubset
  have hX : FootprintVertices
      (TileTranslation (placement.layout.P 1 true)
        placement.rightNeighborDisplacement) ⊆ FootprintVertices root := by
    simpa [hj, hsecond] using secondBoundarySubset
  exact packageGeometry 0 1 1 false true g hgs hge hneq
    R1g R2g hW hX

private theorem hRAt1245 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        (placement.rightDirectionSlot = (2 : Fin (3 : ℕ))) → ((placement.rightNeighborPositive =
            true) → (placement.rightNeighborDisplacement = BandVectors.1 (q 0) (q 3))) ) := by
  classical
  intro C D T N h k x bundle placement q hk hpos
  simpa [hpos, hk] using placement.right_neighbor_displacement

private theorem tStartAt1267 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (ell : Fin 3), TouchingTriple F (TileTranslation F (BandVectors.1 (q 0) (q ell.succ)))
            (TileTranslation F (-BandVectors.1 (q 0) (q (ell + 1).succ)))) →
            ((placement.rightNeighborDisplacement = BandVectors.1 (q 0) (q 3)) → (TouchingTriple
            F (TileTranslation F placement.rightNeighborDisplacement) (TileTranslation F ((-1 :
            GaussianInt) * BandVectors.1 (q 0) (q 1))))) ) := by
  classical
  intro C D T N h k x bundle placement q F touchingPlus hR
  simpa [hR] using touchingPlus 2

private theorem tEndAt1271 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (ell : Fin 3), TouchingTriple F (TileTranslation F (-BandVectors.1 (q 0) (q
            ell.succ))) (TileTranslation F (BandVectors.1 (q 0) (q (ell + 1).succ)))) →
            ((placement.rightNeighborDisplacement = BandVectors.1 (q 0) (q 3)) → (TouchingTriple
            F (TileTranslation F ((-1 : GaussianInt) * BandVectors.1 (q 0) (q 2)))
            (TileTranslation F placement.rightNeighborDisplacement))) ) := by
  classical
  intro C D T N h k x bundle placement q F touchingMinus hR
  simpa [hR] using touchingMinus 1

private theorem geomAt1286 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), ∀ (selectedEdge : Finset GaussianInt),
        let q := bundle.normalizedPresentation;
        let cfg := bundle.configuration;
        let F := bundle.normalizedFixed;
        let root := bundle.normalizedRoot;
        ∀ (edgeVertex : ∀ (tile : ProtoTile), (tile.cells.Nonempty) → (∀ (edge : Finset
            GaussianInt), (edge ∈ FootprintEdges tile) → (∀ (point : GaussianInt), (point ∈ edge)
            → (point ∈ FootprintVertices tile)))),
        let norm : BandOrderedGeneralRightNormalizationCertificate C T N h k x := {
          presentation := bundle.presentation
          presentation_proper := bundle.presentation_proper
          presentation_child := bundle.presentation_child
          parentRotation := bundle.parentRotation
          symmetry := bundle.symmetry
          rotatedPresentation := bundle.rotatedPresentation
          rotated_presentation_eq := bundle.rotated_presentation_eq
          normalizedPresentation := q
          normalized_presentation_eq := bundle.normalized_presentation_eq
          configuration := cfg
          normalizedCircle := bundle.normalizedCircle
          normalized_circle_eq := bundle.normalized_circle_eq
          normalizedFixedCircle := bundle.normalizedCircle
          normalized_fixed_circle_eq := by
            calc
              bundle.normalizedCircle.1.1 = q 0 := bundle.normalized_circle_eq.symm
              _ = BandPackingSymmetryCircleAction bundle.symmetry C.1.1 := by
                have hq0 := congrFun bundle.normalized_presentation_eq 0
                calc
                  q 0 = BandPackingSymmetryCircleAction bundle.symmetry
                      (bundle.rotatedPresentation 0) := by
                        simpa [BandPackingSymmetryQuadrupleAction] using hq0
                  _ = BandPackingSymmetryCircleAction bundle.symmetry C.1.1 := by
                        rw [bundle.rotated_presentation_eq]
                        simp [bundle.presentation_child]
          normalizedRoot := root
          normalizedFixed := F
          normalizedRootFunction := bundle.normalizedRootFunction
          normalizedFixedFunction := bundle.normalizedFixedFunction
          normalizedPoint := bundle.normalizedPoint
          normalized_root_eq := bundle.normalized_root_eq
          normalized_fixed_eq := bundle.normalized_fixed_eq
          normalized_root_function_eq := bundle.normalized_root_function_eq
          normalized_fixed_function_eq := bundle.normalized_fixed_function_eq
          normalized_point_eq := bundle.normalized_point_eq
          normalized_point_root_domain := by
            obtain ⟨edge, hp, he⟩ := bundle.edgeAtPoint
            have hne := (LatticeTileGridStructure root bundle.root_lattice).1.1
            have hvert := edgeVertex root hne edge he.1 bundle.normalizedPoint hp
            have hdom := PositiveCurvatureTileOdometerDomain (q 0) root
              bundle.normalizedRootFunction (ProperBandCurvatureStructure q cfg.proper).1
              bundle.normalized_root_odometer
            exact (Set.ext_iff.mp hdom bundle.normalizedPoint).mpr hvert
          normalized_point_fixed_domain := by
            obtain ⟨edge, hp, he⟩ := bundle.edgeAtPoint
            have hne := (LatticeTileGridStructure F bundle.fixed_lattice).1.1
            have hvert := edgeVertex F hne edge he.2 bundle.normalizedPoint hp
            have hdom := PositiveCurvatureTileOdometerDomain
              bundle.normalizedCircle.1.1 F bundle.normalizedFixedFunction
              bundle.normalizedCircle.property placement.adjacency.2.1
            exact (Set.ext_iff.mp hdom bundle.normalizedPoint).mpr hvert
          normalized_root_odometer := bundle.normalized_root_odometer
          normalized_fixed_odometer := placement.adjacency.2.1
          normalized_root_lattice := bundle.root_lattice
          normalized_fixed_lattice := bundle.fixed_lattice
          normalizedRootSlope := bundle.normalizedRootSlope
          normalizedFixedSlope := bundle.normalizedFixedSlope
          normalized_root_slope := bundle.normalized_root_slope
          normalized_fixed_slope := bundle.normalized_fixed_slope
          pieces := bundle.pieces
          functions := bundle.functions
          root_band := bundle.root_band
          piece_odometer := bundle.piece_odometer
          piece_cell_cover := bundle.piece_cell_cover
          piece_footprint := bundle.piece_footprint
          piece_centroid := bundle.piece_centroid
          function_domain_cover := bundle.function_domain_cover
          function_restriction := bundle.function_restriction
          function_compatibility := bundle.function_compatibility
          piece_slope := bundle.piece_slope
          adjacency := placement.adjacency
          layout := placement.layout
          fixed_quarter_turn := TileT2QuarterTurn q cfg bundle.normalizedCircle F placement.layout
          rightFirstSlot := placement.rightFirstSlot
          rightSecondSlot := placement.rightSecondSlot
          rightDirectionSlot := placement.rightDirectionSlot
          right_slots_cyclic := placement.right_slots_cyclic
          rightNeighborPositive := placement.rightNeighborPositive
          right_adjacency_centroid := placement.right_adjacency_centroid
          right_adjacency_slope_real := by
            have hroot : placement.rightRootSlope = bundle.normalizedRootSlope :=
              Option.some.inj (placement.right_root_slope.symm.trans
                bundle.normalized_root_slope)
            have hf : placement.rightFixedSlope = bundle.normalizedFixedSlope :=
              Option.some.inj (placement.right_fixed_slope.symm.trans
                bundle.normalized_fixed_slope)
            simpa [hroot, hf, q] using placement.right_adjacency_slope_real
          right_adjacency_slope_imag := by
            have hroot : placement.rightRootSlope = bundle.normalizedRootSlope :=
              Option.some.inj (placement.right_root_slope.symm.trans
                bundle.normalized_root_slope)
            have hf : placement.rightFixedSlope = bundle.normalizedFixedSlope :=
              Option.some.inj (placement.right_fixed_slope.symm.trans
                bundle.normalized_fixed_slope)
            simpa [hroot, hf, q] using placement.right_adjacency_slope_imag
          rightNeighborDisplacement := placement.rightNeighborDisplacement
          right_neighbor_displacement := placement.right_neighbor_displacement
          right_neighbor_cells := placement.right_neighbor_cells
          right_neighbor_empty_anchor := placement.right_neighbor_empty_anchor
          firstBoundarySign := placement.firstBoundarySign
          secondBoundarySign := placement.secondBoundarySign
          boundary_signs := placement.boundary_signs
          first_boundary_cells := placement.first_boundary_cells
          first_boundary_empty_anchor := placement.first_boundary_empty_anchor
          first_boundary_footprint := placement.first_boundary_footprint
          first_boundary_domain := placement.first_boundary_domain
          second_boundary_cells := placement.second_boundary_cells
          second_boundary_empty_anchor := placement.second_boundary_empty_anchor
          second_boundary_footprint := placement.second_boundary_footprint
          second_boundary_domain := placement.second_boundary_domain
          normalized_star := bundle.normalized_star }
        let P := placement.layout.P
        let u := placement.layout.u
        let v := placement.layout.v
        let selectedPath : Prop :=
            (∃ selectedStart selectedEnd : GaussianInt,
              SimpleGridPathBetween
                (FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                (FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                selectedStart selectedEnd ∧
              selectedEdge ∈
                FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex) ∧
              bundle.normalizedPoint ∈ selectedEdge)
        let rightGeometry := fun (i j : Fin 3) (sgn : GaussianInt)
            (firstSign secondSign : Bool) ↦
          let firstCompanion := TileTranslation F
            (sgn * BandVectors.1 (q 0) (q i.succ))
          let secondCompanion := TileTranslation F
            (sgn * BandVectors.1 (q 0) (q j.succ))
          let firstPiece := TileTranslation (placement.layout.P i firstSign)
            placement.rightNeighborDisplacement
          let secondPiece := TileTranslation (placement.layout.P j secondSign)
            placement.rightNeighborDisplacement
          ∃ firstBoundaryData : ExactTileInterfaceTriple F firstCompanion firstPiece,
            ∃ secondBoundaryData : ExactTileInterfaceTriple F secondCompanion secondPiece,
              ∃ firstData : ExactTileInterfaceTriple root F firstCompanion,
                ∃ secondData : ExactTileInterfaceTriple root F secondCompanion,
                  firstBoundaryData.point = firstData.point ∧
                  secondBoundaryData.point = secondData.point ∧
                  LatticeTile root ∧ LatticeTile F ∧ LatticeTile firstCompanion ∧
                  LatticeTile secondCompanion ∧ Disjoint root.cells firstCompanion.cells ∧
                  Disjoint F.cells firstCompanion.cells ∧
                  Disjoint root.cells secondCompanion.cells ∧
                  Disjoint F.cells secondCompanion.cells ∧
                  Disjoint firstCompanion.cells secondCompanion.cells ∧
                  TouchingTriple root F firstCompanion ∧
                  TouchingTriple root F secondCompanion ∧
                  firstData.point ≠ secondData.point ∧
                  secondData.point = firstData.otherAB ∧
                  secondData.otherAB = firstData.point ∧ selectedPath
        (∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (sgn : GaussianInt), ∀ (s₁ : Bool), ∀ (s₂ : Bool), ∀ (g
            : BandOrderedGeneralRightInterfaceCertificate norm), (g.startCompanion =
            TileTranslation F (sgn * BandVectors.1 (q 0) (q i.succ))) → ((g.endCompanion =
            TileTranslation F (sgn * BandVectors.1 (q 0) (q j.succ))) → ((g.startData.point ≠
            g.endData.point) → ((ExactTileInterfaceTriple F g.startCompanion (TileTranslation
            (placement.layout.P i s₁) placement.rightNeighborDisplacement)) →
            ((ExactTileInterfaceTriple F g.endCompanion (TileTranslation (placement.layout.P j
            s₂) placement.rightNeighborDisplacement)) → ((FootprintVertices (TileTranslation
            (placement.layout.P i s₁) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root) → ((FootprintVertices (TileTranslation (placement.layout.P j s₂)
            placement.rightNeighborDisplacement) ⊆ FootprintVertices root) → (rightGeometry i j
            sgn s₁ s₂)))))))) → ((FootprintVertices (TileTranslation (placement.layout.P
            placement.rightFirstSlot placement.firstBoundarySign)
            placement.rightNeighborDisplacement) ⊆ FootprintVertices root) → ((FootprintVertices
            (TileTranslation (placement.layout.P placement.rightSecondSlot
            placement.secondBoundarySign) placement.rightNeighborDisplacement) ⊆
            FootprintVertices root) → ((placement.rightFirstSlot = (0 : Fin (3 : ℕ))) →
            ((placement.rightSecondSlot = (1 : Fin (3 : ℕ))) → ((ExactTileInterfaceTriple
            bundle.normalizedFixed (TileTranslation bundle.normalizedFixed (-BandVectors.1
            (bundle.normalizedPresentation (0 : Fin (4 : ℕ))) (bundle.normalizedPresentation
            placement.rightFirstSlot.succ))) (TileTranslation (placement.layout.P
            placement.rightFirstSlot true) placement.rightNeighborDisplacement)) →
            ((ExactTileInterfaceTriple bundle.normalizedFixed (TileTranslation
            bundle.normalizedFixed (-BandVectors.1 (bundle.normalizedPresentation (0 : Fin (4 :
            ℕ))) (bundle.normalizedPresentation placement.rightSecondSlot.succ)))
            (TileTranslation (placement.layout.P placement.rightSecondSlot false)
            placement.rightNeighborDisplacement)) → (∀ (g :
            BandOrderedGeneralRightInterfaceCertificate norm), (g.startCompanion =
            TileTranslation F ((-1 : GaussianInt) * BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 :
            Fin (4 : ℕ))))) → ((g.endCompanion = TileTranslation F ((-1 : GaussianInt) *
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))) → ((g.startData.point ≠
            g.endData.point) → ((placement.firstBoundarySign = true) →
            ((placement.secondBoundarySign = false) → (rightGeometry 0 1 (-1) true
            false)))))))))))) ) := by
  classical
  intro C D T N h k x bundle placement selectedEdge q cfg F root edgeVertex norm P u v
      selectedPath rightGeometry packageGeometry firstBoundarySubset secondBoundarySubset hi hj
      R1 R2 g hgs hge hneq hfirst hsecond
  have R1g : ExactTileInterfaceTriple F g.startCompanion
      (TileTranslation (placement.layout.P 0 true)
        placement.rightNeighborDisplacement) := by
    simpa [hgs, hi] using R1
  have R2g : ExactTileInterfaceTriple F g.endCompanion
      (TileTranslation (placement.layout.P 1 false)
        placement.rightNeighborDisplacement) := by
    simpa [hge, hj] using R2
  have hW : FootprintVertices
      (TileTranslation (placement.layout.P 0 true)
        placement.rightNeighborDisplacement) ⊆ FootprintVertices root := by
    simpa [hi, hfirst] using firstBoundarySubset
  have hX : FootprintVertices
      (TileTranslation (placement.layout.P 1 false)
        placement.rightNeighborDisplacement) ⊆ FootprintVertices root := by
    simpa [hj, hsecond] using secondBoundarySubset
  exact packageGeometry 0 1 (-1) true false g hgs hge hneq
    R1g R2g hW hX

private theorem hRAt1329 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        (placement.rightDirectionSlot = (0 : Fin (3 : ℕ))) → ((placement.rightNeighborPositive =
            false) → (placement.rightNeighborDisplacement = -BandVectors.1 (q 0) (q 1))) ) := by
  classical
  intro C D T N h k x bundle placement q hk hpos
  simpa [hpos, hk] using placement.right_neighbor_displacement

private theorem tStartAt1341 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (ell : Fin 3), TouchingTriple F (TileTranslation F (-BandVectors.1 (q 0) (q
            ell.succ))) (TileTranslation F (BandVectors.1 (q 0) (q (ell + 1).succ)))) →
            ((placement.rightNeighborDisplacement = -BandVectors.1 (q 0) (q 1)) → (TouchingTriple
            F (TileTranslation F placement.rightNeighborDisplacement) (TileTranslation F ((1 :
            GaussianInt) * BandVectors.1 (q 0) (q 2))))) ) := by
  classical
  intro C D T N h k x bundle placement q F touchingMinus hR
  simpa [hR] using touchingMinus 0

private theorem tEndAt1345 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (ell : Fin 3), TouchingTriple F (TileTranslation F (BandVectors.1 (q 0) (q ell.succ)))
            (TileTranslation F (-BandVectors.1 (q 0) (q (ell + 1).succ)))) →
            ((placement.rightNeighborDisplacement = -BandVectors.1 (q 0) (q 1)) → (TouchingTriple
            F (TileTranslation F ((1 : GaussianInt) * BandVectors.1 (q 0) (q 3)))
            (TileTranslation F placement.rightNeighborDisplacement))) ) := by
  classical
  intro C D T N h k x bundle placement q F touchingPlus hR
  simpa [hR] using touchingPlus 2

private theorem hWAt1369 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let root := bundle.normalizedRoot
        (FootprintVertices (TileTranslation (placement.layout.P placement.rightFirstSlot
            placement.firstBoundarySign) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root) → ((placement.rightFirstSlot = (1 : Fin (3 : ℕ))) →
            ((placement.firstBoundarySign = false) → (FootprintVertices (TileTranslation
            (placement.layout.P 1 false) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root))) ) := by
  classical
  intro C D T N h k x bundle placement root firstBoundarySubset hi hfirst
  simpa [hi, hfirst] using firstBoundarySubset

private theorem hXAt1373 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let root := bundle.normalizedRoot
        (FootprintVertices (TileTranslation (placement.layout.P placement.rightSecondSlot
            placement.secondBoundarySign) placement.rightNeighborDisplacement) ⊆
            FootprintVertices root) → ((placement.rightSecondSlot = (2 : Fin (3 : ℕ))) →
            ((placement.secondBoundarySign = true) → (FootprintVertices (TileTranslation
            (placement.layout.P 2 true) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root))) ) := by
  classical
  intro C D T N h k x bundle placement root secondBoundarySubset hj hsecond
  simpa [hj, hsecond] using secondBoundarySubset

private theorem hRAt1390 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        (placement.rightDirectionSlot = (0 : Fin (3 : ℕ))) → ((placement.rightNeighborPositive =
            true) → (placement.rightNeighborDisplacement = BandVectors.1 (q 0) (q 1))) ) := by
  classical
  intro C D T N h k x bundle placement q hk hpos
  simpa [hpos, hk] using placement.right_neighbor_displacement

private theorem tStartAt1402 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (ell : Fin 3), TouchingTriple F (TileTranslation F (BandVectors.1 (q 0) (q ell.succ)))
            (TileTranslation F (-BandVectors.1 (q 0) (q (ell + 1).succ)))) →
            ((placement.rightNeighborDisplacement = BandVectors.1 (q 0) (q 1)) → (TouchingTriple
            F (TileTranslation F placement.rightNeighborDisplacement) (TileTranslation F ((-1 :
            GaussianInt) * BandVectors.1 (q 0) (q 2))))) ) := by
  classical
  intro C D T N h k x bundle placement q F touchingPlus hR
  simpa [hR] using touchingPlus 0

private theorem tEndAt1406 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (ell : Fin 3), TouchingTriple F (TileTranslation F (-BandVectors.1 (q 0) (q
            ell.succ))) (TileTranslation F (BandVectors.1 (q 0) (q (ell + 1).succ)))) →
            ((placement.rightNeighborDisplacement = BandVectors.1 (q 0) (q 1)) → (TouchingTriple
            F (TileTranslation F ((-1 : GaussianInt) * BandVectors.1 (q 0) (q 3)))
            (TileTranslation F placement.rightNeighborDisplacement))) ) := by
  classical
  intro C D T N h k x bundle placement q F touchingMinus hR
  simpa [hR] using touchingMinus 2

private theorem hWAt1428 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let root := bundle.normalizedRoot
        (FootprintVertices (TileTranslation (placement.layout.P placement.rightFirstSlot
            placement.firstBoundarySign) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root) → ((placement.rightFirstSlot = (1 : Fin (3 : ℕ))) →
            ((placement.firstBoundarySign = true) → (FootprintVertices (TileTranslation
            (placement.layout.P 1 true) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root))) ) := by
  classical
  intro C D T N h k x bundle placement root firstBoundarySubset hi hfirst
  simpa [hi, hfirst] using firstBoundarySubset

private theorem hXAt1432 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let root := bundle.normalizedRoot
        (FootprintVertices (TileTranslation (placement.layout.P placement.rightSecondSlot
            placement.secondBoundarySign) placement.rightNeighborDisplacement) ⊆
            FootprintVertices root) → ((placement.rightSecondSlot = (2 : Fin (3 : ℕ))) →
            ((placement.secondBoundarySign = false) → (FootprintVertices (TileTranslation
            (placement.layout.P 2 false) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root))) ) := by
  classical
  intro C D T N h k x bundle placement root secondBoundarySubset hj hsecond
  simpa [hj, hsecond] using secondBoundarySubset

private theorem hRAt1461 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        (placement.rightDirectionSlot = (1 : Fin (3 : ℕ))) → ((placement.rightNeighborPositive =
            false) → (placement.rightNeighborDisplacement = -BandVectors.1 (q 0) (q 2))) ) := by
  classical
  intro C D T N h k x bundle placement q hk hpos
  simpa [hpos, hk] using placement.right_neighbor_displacement

private theorem tStartAt1473 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (ell : Fin 3), TouchingTriple F (TileTranslation F (-BandVectors.1 (q 0) (q
            ell.succ))) (TileTranslation F (BandVectors.1 (q 0) (q (ell + 1).succ)))) →
            ((placement.rightNeighborDisplacement = -BandVectors.1 (q 0) (q 2)) → (TouchingTriple
            F (TileTranslation F placement.rightNeighborDisplacement) (TileTranslation F ((1 :
            GaussianInt) * BandVectors.1 (q 0) (q 3))))) ) := by
  classical
  intro C D T N h k x bundle placement q F touchingMinus hR
  simpa [hR] using touchingMinus 1

private theorem tEndAt1477 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (ell : Fin 3), TouchingTriple F (TileTranslation F (BandVectors.1 (q 0) (q ell.succ)))
            (TileTranslation F (-BandVectors.1 (q 0) (q (ell + 1).succ)))) →
            ((placement.rightNeighborDisplacement = -BandVectors.1 (q 0) (q 2)) → (TouchingTriple
            F (TileTranslation F ((1 : GaussianInt) * BandVectors.1 (q 0) (q 1)))
            (TileTranslation F placement.rightNeighborDisplacement))) ) := by
  classical
  intro C D T N h k x bundle placement q F touchingPlus hR
  simpa [hR] using touchingPlus 0

private theorem hWAt1501 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let root := bundle.normalizedRoot
        (FootprintVertices (TileTranslation (placement.layout.P placement.rightFirstSlot
            placement.firstBoundarySign) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root) → ((placement.rightFirstSlot = (2 : Fin (3 : ℕ))) →
            ((placement.firstBoundarySign = false) → (FootprintVertices (TileTranslation
            (placement.layout.P 2 false) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root))) ) := by
  classical
  intro C D T N h k x bundle placement root firstBoundarySubset hi hfirst
  simpa [hi, hfirst] using firstBoundarySubset

private theorem hXAt1505 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let root := bundle.normalizedRoot
        (FootprintVertices (TileTranslation (placement.layout.P placement.rightSecondSlot
            placement.secondBoundarySign) placement.rightNeighborDisplacement) ⊆
            FootprintVertices root) → ((placement.rightSecondSlot = (0 : Fin (3 : ℕ))) →
            ((placement.secondBoundarySign = true) → (FootprintVertices (TileTranslation
            (placement.layout.P 0 true) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root))) ) := by
  classical
  intro C D T N h k x bundle placement root secondBoundarySubset hj hsecond
  simpa [hj, hsecond] using secondBoundarySubset

private theorem hRAt1522 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        (placement.rightDirectionSlot = (1 : Fin (3 : ℕ))) → ((placement.rightNeighborPositive =
            true) → (placement.rightNeighborDisplacement = BandVectors.1 (q 0) (q 2))) ) := by
  classical
  intro C D T N h k x bundle placement q hk hpos
  simpa [hpos, hk] using placement.right_neighbor_displacement

private theorem tStartAt1534 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (ell : Fin 3), TouchingTriple F (TileTranslation F (BandVectors.1 (q 0) (q ell.succ)))
            (TileTranslation F (-BandVectors.1 (q 0) (q (ell + 1).succ)))) →
            ((placement.rightNeighborDisplacement = BandVectors.1 (q 0) (q 2)) → (TouchingTriple
            F (TileTranslation F placement.rightNeighborDisplacement) (TileTranslation F ((-1 :
            GaussianInt) * BandVectors.1 (q 0) (q 3))))) ) := by
  classical
  intro C D T N h k x bundle placement q F touchingPlus hR
  simpa [hR] using touchingPlus 1

private theorem tEndAt1538 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        (∀ (ell : Fin 3), TouchingTriple F (TileTranslation F (-BandVectors.1 (q 0) (q
            ell.succ))) (TileTranslation F (BandVectors.1 (q 0) (q (ell + 1).succ)))) →
            ((placement.rightNeighborDisplacement = BandVectors.1 (q 0) (q 2)) → (TouchingTriple
            F (TileTranslation F ((-1 : GaussianInt) * BandVectors.1 (q 0) (q 1)))
            (TileTranslation F placement.rightNeighborDisplacement))) ) := by
  classical
  intro C D T N h k x bundle placement q F touchingMinus hR
  simpa [hR] using touchingMinus 0

private theorem hWAt1560 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let root := bundle.normalizedRoot
        (FootprintVertices (TileTranslation (placement.layout.P placement.rightFirstSlot
            placement.firstBoundarySign) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root) → ((placement.rightFirstSlot = (2 : Fin (3 : ℕ))) →
            ((placement.firstBoundarySign = true) → (FootprintVertices (TileTranslation
            (placement.layout.P 2 true) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root))) ) := by
  classical
  intro C D T N h k x bundle placement root firstBoundarySubset hi hfirst
  simpa [hi, hfirst] using firstBoundarySubset

private theorem hXAt1564 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let root := bundle.normalizedRoot
        (FootprintVertices (TileTranslation (placement.layout.P placement.rightSecondSlot
            placement.secondBoundarySign) placement.rightNeighborDisplacement) ⊆
            FootprintVertices root) → ((placement.rightSecondSlot = (0 : Fin (3 : ℕ))) →
            ((placement.secondBoundarySign = false) → (FootprintVertices (TileTranslation
            (placement.layout.P 0 false) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root))) ) := by
  classical
  intro C D T N h k x bundle placement root secondBoundarySubset hj hsecond
  simpa [hj, hsecond] using secondBoundarySubset

end SelectedRowGeometry

namespace SelectedRowNormalization

private noncomputable def certificate
    (C D : BandCircle) (T N : ProtoTile) (h k : PartialOdometer)
    (x : GaussianInt)
    (bundle : BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x)
    (placement : BandOrderedGeneralRightPlacement bundle.normalizedPresentation
      bundle.configuration bundle.normalizedCircle bundle.normalizedRoot
      bundle.normalizedFixed bundle.normalizedRootFunction
      bundle.normalizedFixedFunction bundle.normalizedPoint bundle.pieces
      bundle.functions bundle.selectedSlot bundle.selectedSign
      bundle.routedDirection)
 :
    BandOrderedGeneralRightNormalizationCertificate C T N h k x := by
  classical
  let q := bundle.normalizedPresentation
  let cfg := bundle.configuration
  let F := bundle.normalizedFixed
  let root := bundle.normalizedRoot
  exact {
    presentation := bundle.presentation
    presentation_proper := bundle.presentation_proper
    presentation_child := bundle.presentation_child
    parentRotation := bundle.parentRotation
    symmetry := bundle.symmetry
    rotatedPresentation := bundle.rotatedPresentation
    rotated_presentation_eq := bundle.rotated_presentation_eq
    normalizedPresentation := q
    normalized_presentation_eq := bundle.normalized_presentation_eq
    configuration := cfg
    normalizedCircle := bundle.normalizedCircle
    normalized_circle_eq := bundle.normalized_circle_eq
    normalizedFixedCircle := bundle.normalizedCircle
    normalized_fixed_circle_eq := by
      calc
        bundle.normalizedCircle.1.1 = q 0 := bundle.normalized_circle_eq.symm
        _ = BandPackingSymmetryCircleAction bundle.symmetry C.1.1 := by
          have hq0 := congrFun bundle.normalized_presentation_eq 0
          calc
            q 0 = BandPackingSymmetryCircleAction bundle.symmetry
                (bundle.rotatedPresentation 0) := by
                  simpa [BandPackingSymmetryQuadrupleAction] using hq0
            _ = BandPackingSymmetryCircleAction bundle.symmetry C.1.1 := by
                  rw [bundle.rotated_presentation_eq]
                  simp [bundle.presentation_child]
    normalizedRoot := root
    normalizedFixed := F
    normalizedRootFunction := bundle.normalizedRootFunction
    normalizedFixedFunction := bundle.normalizedFixedFunction
    normalizedPoint := bundle.normalizedPoint
    normalized_root_eq := bundle.normalized_root_eq
    normalized_fixed_eq := bundle.normalized_fixed_eq
    normalized_root_function_eq := bundle.normalized_root_function_eq
    normalized_fixed_function_eq := bundle.normalized_fixed_function_eq
    normalized_point_eq := bundle.normalized_point_eq
    normalized_point_root_domain := by
      obtain ⟨edge, hp, he⟩ := bundle.edgeAtPoint
      have hne := (LatticeTileGridStructure root bundle.root_lattice).1.1
      have hvert := SelectedRowGeometry.edgeVertex root hne edge he.1 bundle.normalizedPoint hp
      have hdom := PositiveCurvatureTileOdometerDomain (q 0) root
        bundle.normalizedRootFunction (ProperBandCurvatureStructure q cfg.proper).1
        bundle.normalized_root_odometer
      exact (Set.ext_iff.mp hdom bundle.normalizedPoint).mpr hvert
    normalized_point_fixed_domain := by
      obtain ⟨edge, hp, he⟩ := bundle.edgeAtPoint
      have hne := (LatticeTileGridStructure F bundle.fixed_lattice).1.1
      have hvert := SelectedRowGeometry.edgeVertex F hne edge he.2 bundle.normalizedPoint hp
      have hdom := PositiveCurvatureTileOdometerDomain
        bundle.normalizedCircle.1.1 F bundle.normalizedFixedFunction
        bundle.normalizedCircle.property placement.adjacency.2.1
      exact (Set.ext_iff.mp hdom bundle.normalizedPoint).mpr hvert
    normalized_root_odometer := bundle.normalized_root_odometer
    normalized_fixed_odometer := placement.adjacency.2.1
    normalized_root_lattice := bundle.root_lattice
    normalized_fixed_lattice := bundle.fixed_lattice
    normalizedRootSlope := bundle.normalizedRootSlope
    normalizedFixedSlope := bundle.normalizedFixedSlope
    normalized_root_slope := bundle.normalized_root_slope
    normalized_fixed_slope := bundle.normalized_fixed_slope
    pieces := bundle.pieces
    functions := bundle.functions
    root_band := bundle.root_band
    piece_odometer := bundle.piece_odometer
    piece_cell_cover := bundle.piece_cell_cover
    piece_footprint := bundle.piece_footprint
    piece_centroid := bundle.piece_centroid
    function_domain_cover := bundle.function_domain_cover
    function_restriction := bundle.function_restriction
    function_compatibility := bundle.function_compatibility
    piece_slope := bundle.piece_slope
    adjacency := placement.adjacency
    layout := placement.layout
    fixed_quarter_turn := TileT2QuarterTurn q cfg bundle.normalizedCircle F placement.layout
    rightFirstSlot := placement.rightFirstSlot
    rightSecondSlot := placement.rightSecondSlot
    rightDirectionSlot := placement.rightDirectionSlot
    right_slots_cyclic := placement.right_slots_cyclic
    rightNeighborPositive := placement.rightNeighborPositive
    right_adjacency_centroid := placement.right_adjacency_centroid
    right_adjacency_slope_real := by
      have hroot : placement.rightRootSlope = bundle.normalizedRootSlope :=
        Option.some.inj (placement.right_root_slope.symm.trans
          bundle.normalized_root_slope)
      have hf : placement.rightFixedSlope = bundle.normalizedFixedSlope :=
        Option.some.inj (placement.right_fixed_slope.symm.trans
          bundle.normalized_fixed_slope)
      simpa [hroot, hf, q] using placement.right_adjacency_slope_real
    right_adjacency_slope_imag := by
      have hroot : placement.rightRootSlope = bundle.normalizedRootSlope :=
        Option.some.inj (placement.right_root_slope.symm.trans
          bundle.normalized_root_slope)
      have hf : placement.rightFixedSlope = bundle.normalizedFixedSlope :=
        Option.some.inj (placement.right_fixed_slope.symm.trans
          bundle.normalized_fixed_slope)
      simpa [hroot, hf, q] using placement.right_adjacency_slope_imag
    rightNeighborDisplacement := placement.rightNeighborDisplacement
    right_neighbor_displacement := placement.right_neighbor_displacement
    right_neighbor_cells := placement.right_neighbor_cells
    right_neighbor_empty_anchor := placement.right_neighbor_empty_anchor
    firstBoundarySign := placement.firstBoundarySign
    secondBoundarySign := placement.secondBoundarySign
    boundary_signs := placement.boundary_signs
    first_boundary_cells := placement.first_boundary_cells
    first_boundary_empty_anchor := placement.first_boundary_empty_anchor
    first_boundary_footprint := placement.first_boundary_footprint
    first_boundary_domain := placement.first_boundary_domain
    second_boundary_cells := placement.second_boundary_cells
    second_boundary_empty_anchor := placement.second_boundary_empty_anchor
    second_boundary_footprint := placement.second_boundary_footprint
    second_boundary_domain := placement.second_boundary_domain
    normalized_star := bundle.normalized_star }

end SelectedRowNormalization

namespace SelectedRowConclusions

private theorem firstCyclicCase :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), ∀ (selectedEdge : Finset GaussianInt), ∀ (chosenBoundary :
            bundle.selectedSlot = placement.rightFirstSlot ∧ bundle.selectedSign =
            placement.firstBoundarySign ∨ bundle.selectedSlot = placement.rightSecondSlot ∧
            bundle.selectedSign = placement.secondBoundarySign),
        let q := bundle.normalizedPresentation
        let F := bundle.normalizedFixed
        let root := bundle.normalizedRoot
        ∀ (edgeVertex : ∀ (tile : ProtoTile), (tile.cells.Nonempty) → (∀ (edge : Finset
            GaussianInt), (edge ∈ FootprintEdges tile) → (∀ (point : GaussianInt), (point ∈ edge)
            → (point ∈ FootprintVertices tile)))),
        let norm := SelectedRowNormalization.certificate C D T N h k x bundle placement
        ∀ (childInterfaces : (∀ (i : Fin (3 : ℕ)), Nonempty (ExactTileInterfaceTriple F
            (TileTranslation F (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) (TileTranslation
            F (-BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ))))))) ∧ (∀ (i
            : Fin (3 : ℕ)), ∀ (U : ProtoTile), BandPrototile (q i.succ) U → TileCentroid U -
            TileCentroid F = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)))
            → Nonempty (ExactTileInterfaceTriple F (TileTranslation F (BandVectors.1 (q i.succ)
            (q (0 : Fin (4 : ℕ))))) U)) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), BandPrototile (q i.succ) U → BandPrototile (q (i + (1 : Fin (3 :
            ℕ))).succ) V → TileCentroid U - TileCentroid F = (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1
            (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid V - TileCentroid F = (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 :
            ℕ)))) - GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i + (1 : Fin (3 :
            ℕ))).succ))) → Nonempty (ExactTileInterfaceTriple F U V)) ∧ ∀ (i : Fin (3 : ℕ)), ∀ (s
            : Fin (4 : ℕ)), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q i.succ) U →
            BandPrototile (q (if Even (↑s : ℕ) then i + (1 : Fin (3 : ℕ)) else i - (1 : Fin (3 :
            ℕ))).succ) V → TileCentroid U - TileCentroid F = (1 / 2 : ℝ) • GaussianRealPoint
            ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid V -
            TileCentroid F = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)
            ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q
            (0 : Fin (4 : ℕ))) - BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i + (1 : Fin (3 :
            ℕ))).succ) else BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i - (1 : Fin (3 : ℕ))).succ)
            - BandVectors.1 (q (i - (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))) →
        let uR := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) else BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)));
        let uL := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then
            BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))) else BandVectors.1 (q (0 : Fin (4 :
            ℕ))) (q i.succ); ∃ (rightData : ExactTileInterfaceTriple F (TileTranslation F uR) U)
            (incomingData : ExactTileInterfaceTriple F (TileTranslation F uL) U) (t5Data :
            ExactTileInterfaceTriple F U V), rightData.point = t5Data.point ∧ incomingData.point
            ≠ t5Data.point ∧ incomingData.otherCA = t5Data.point ∧ rightData.otherCA =
            incomingData.point ∧ t5Data.otherAB = incomingData.point), ∀ (turnOutgoing : ∀ (s :
            Fin 3), GaussianQuarterTurn (BandVectors.1 (q s.succ) (q 0)) = BandVectors.1 (q 0) (q
            s.succ)), ∀ (turnNeg : ∀ (z : GaussianInt), GaussianQuarterTurn (-z) =
            -GaussianQuarterTurn z), ∀ (boundaryRecords : placement.rightFirstSlot = (0 : Fin (3
            : ℕ)) ∧ placement.rightSecondSlot = (1 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot
            = (2 : Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (1 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (2 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (0 :
            Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (2 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (0 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (1 :
            Fin (3 : ℕ)) → (placement.rightNeighborPositive = true → Nonempty
            (ExactTileInterfaceTriple bundle.normalizedFixed (TileTranslation
            bundle.normalizedFixed (-BandVectors.1 (bundle.normalizedPresentation (0 : Fin (4 :
            ℕ))) (bundle.normalizedPresentation placement.rightFirstSlot.succ))) (TileTranslation
            (placement.layout.P placement.rightFirstSlot true)
            placement.rightNeighborDisplacement)) ∧ Nonempty (ExactTileInterfaceTriple
            bundle.normalizedFixed (TileTranslation bundle.normalizedFixed (-BandVectors.1
            (bundle.normalizedPresentation (0 : Fin (4 : ℕ))) (bundle.normalizedPresentation
            placement.rightSecondSlot.succ))) (TileTranslation (placement.layout.P
            placement.rightSecondSlot false) placement.rightNeighborDisplacement))) ∧
            (placement.rightNeighborPositive = false → Nonempty (ExactTileInterfaceTriple
            bundle.normalizedFixed (TileTranslation bundle.normalizedFixed (BandVectors.1
            (bundle.normalizedPresentation (0 : Fin (4 : ℕ))) (bundle.normalizedPresentation
            placement.rightFirstSlot.succ))) (TileTranslation (placement.layout.P
            placement.rightFirstSlot false) placement.rightNeighborDisplacement)) ∧ Nonempty
            (ExactTileInterfaceTriple bundle.normalizedFixed (TileTranslation
            bundle.normalizedFixed (BandVectors.1 (bundle.normalizedPresentation (0 : Fin (4 :
            ℕ))) (bundle.normalizedPresentation placement.rightSecondSlot.succ)))
            (TileTranslation (placement.layout.P placement.rightSecondSlot true)
            placement.rightNeighborDisplacement)))), ∀ (centeredExactTurn : ∀ (a : GaussianInt),
            ∀ (b : GaussianInt), (ExactTileInterfaceTriple F (TileTranslation F a)
            (TileTranslation F b)) → (Nonempty (ExactTileInterfaceTriple F (TileTranslation F
            (GaussianQuarterTurn a)) (TileTranslation F (GaussianQuarterTurn b))))), ∀
            (tripleTurnOutgoing : ∀ (ell : Fin 3), GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianQuarterTurn (BandVectors.1 (q ell.succ) (q 0)))) = -BandVectors.1 (q 0) (q
            ell.succ)), ∀ (tripleTurnNegativeNext : ∀ (ell : Fin 3), GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianQuarterTurn (-BandVectors.1 (q (ell + 1).succ) (q 0))))
            = BandVectors.1 (q 0) (q (ell + 1).succ)),
        (∀ (ell : Fin 3), TouchingTriple F (TileTranslation F (BandVectors.1 (q 0) (q ell.succ)))
            (TileTranslation F (-BandVectors.1 (q 0) (q (ell + 1).succ)))) → ((∀ (ell : Fin 3),
            TouchingTriple F (TileTranslation F (-BandVectors.1 (q 0) (q ell.succ)))
            (TileTranslation F (BandVectors.1 (q 0) (q (ell + 1).succ)))) → (
        let P := placement.layout.P
        let u := placement.layout.u
        let v := placement.layout.v
        let selectedPath : Prop :=
            (∃ selectedStart selectedEnd : GaussianInt,
              SimpleGridPathBetween
                (FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                (FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                selectedStart selectedEnd ∧
              selectedEdge ∈
                FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex) ∧
              bundle.normalizedPoint ∈ selectedEdge)
        let rightGeometry := fun (i j : Fin 3) (sgn : GaussianInt)
            (firstSign secondSign : Bool) ↦
          let firstCompanion := TileTranslation F
            (sgn * BandVectors.1 (q 0) (q i.succ))
          let secondCompanion := TileTranslation F
            (sgn * BandVectors.1 (q 0) (q j.succ))
          let firstPiece := TileTranslation (placement.layout.P i firstSign)
            placement.rightNeighborDisplacement
          let secondPiece := TileTranslation (placement.layout.P j secondSign)
            placement.rightNeighborDisplacement
          ∃ firstBoundaryData : ExactTileInterfaceTriple F firstCompanion firstPiece,
            ∃ secondBoundaryData : ExactTileInterfaceTriple F secondCompanion secondPiece,
              ∃ firstData : ExactTileInterfaceTriple root F firstCompanion,
                ∃ secondData : ExactTileInterfaceTriple root F secondCompanion,
                  firstBoundaryData.point = firstData.point ∧
                  secondBoundaryData.point = secondData.point ∧
                  LatticeTile root ∧ LatticeTile F ∧ LatticeTile firstCompanion ∧
                  LatticeTile secondCompanion ∧ Disjoint root.cells firstCompanion.cells ∧
                  Disjoint F.cells firstCompanion.cells ∧
                  Disjoint root.cells secondCompanion.cells ∧
                  Disjoint F.cells secondCompanion.cells ∧
                  Disjoint firstCompanion.cells secondCompanion.cells ∧
                  TouchingTriple root F firstCompanion ∧
                  TouchingTriple root F secondCompanion ∧
                  firstData.point ≠ secondData.point ∧
                  secondData.point = firstData.otherAB ∧
                  secondData.otherAB = firstData.point ∧ selectedPath
        (∀ (uStart : GaussianInt), ∀ (uEnd : GaussianInt), ∀ (mR : Int), ∀ (nR : Int), ∀ (mS :
            Int), ∀ (nS : Int), ∀ (mE : Int), ∀ (nE : Int), (placement.rightNeighborDisplacement
            = (mR : GaussianInt) * placement.layout.u + (nR : GaussianInt) * placement.layout.v)
            → ((uStart = (mS : GaussianInt) * placement.layout.u + (nS : GaussianInt) *
            placement.layout.v) → ((uEnd = (mE : GaussianInt) * placement.layout.u + (nE :
            GaussianInt) * placement.layout.v) → (((0, 0) ≠ (mR, nR)) → (((0, 0) ≠ (mS, nS)) →
            (((0, 0) ≠ (mE, nE)) → (((mR, nR) ≠ (mS, nS)) → (((mR, nR) ≠ (mE, nE)) → (((mS, nS) ≠
            (mE, nE)) → ((ExactTileInterfaceTriple F (TileTranslation F
            placement.rightNeighborDisplacement) (TileTranslation F uStart)) →
            ((ExactTileInterfaceTriple F (TileTranslation F uEnd) (TileTranslation F
            placement.rightNeighborDisplacement)) → ((TouchingTriple F (TileTranslation F
            placement.rightNeighborDisplacement) (TileTranslation F uStart)) → ((TouchingTriple F
            (TileTranslation F uEnd) (TileTranslation F placement.rightNeighborDisplacement)) →
            (∃ g : BandOrderedGeneralRightInterfaceCertificate norm, g.startCompanion =
            TileTranslation F uStart ∧ g.endCompanion = TileTranslation F uEnd ∧
            g.startData.point ≠ g.endData.point)))))))))))))) → ((((0, 0) : Int × Int) ≠ (1, 1) ∧
            ((0, 0) : Int × Int) ≠ (1, 0) ∧ ((0, 0) : Int × Int) ≠ (0, 1) ∧ ((1, 1) : Int × Int)
            ≠ (1, 0) ∧ ((1, 1) : Int × Int) ≠ (0, 1) ∧ ((1, 0) : Int × Int) ≠ (0, 1)) → ((((0, 0)
            : Int × Int) ≠ (-1, -1) ∧ ((0, 0) : Int × Int) ≠ (-1, 0) ∧ ((0, 0) : Int × Int) ≠ (0,
            -1) ∧ ((-1, -1) : Int × Int) ≠ (-1, 0) ∧ ((-1, -1) : Int × Int) ≠ (0, -1) ∧ ((-1, 0)
            : Int × Int) ≠ (0, -1)) → ((BandVectors.1 (q 0) (q 1) = placement.layout.u) →
            ((BandVectors.1 (q 0) (q 2) = placement.layout.v) → ((BandVectors.1 (q 0) (q 3) =
            -placement.layout.u - placement.layout.v) → ((∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (sgn :
            GaussianInt), ∀ (s₁ : Bool), ∀ (s₂ : Bool), ∀ (g :
            BandOrderedGeneralRightInterfaceCertificate norm), (g.startCompanion =
            TileTranslation F (sgn * BandVectors.1 (q 0) (q i.succ))) → ((g.endCompanion =
            TileTranslation F (sgn * BandVectors.1 (q 0) (q j.succ))) → ((g.startData.point ≠
            g.endData.point) → ((ExactTileInterfaceTriple F g.startCompanion (TileTranslation
            (placement.layout.P i s₁) placement.rightNeighborDisplacement)) →
            ((ExactTileInterfaceTriple F g.endCompanion (TileTranslation (placement.layout.P j
            s₂) placement.rightNeighborDisplacement)) → ((FootprintVertices (TileTranslation
            (placement.layout.P i s₁) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root) → ((FootprintVertices (TileTranslation (placement.layout.P j s₂)
            placement.rightNeighborDisplacement) ⊆ FootprintVertices root) → (rightGeometry i j
            sgn s₁ s₂)))))))) → ((FootprintVertices (TileTranslation (placement.layout.P
            placement.rightFirstSlot placement.firstBoundarySign)
            placement.rightNeighborDisplacement) ⊆ FootprintVertices root) → ((FootprintVertices
            (TileTranslation (placement.layout.P placement.rightSecondSlot
            placement.secondBoundarySign) placement.rightNeighborDisplacement) ⊆
            FootprintVertices root) → ((placement.rightFirstSlot = (0 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (1 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (2 :
            Fin (3 : ℕ))) → (
        let q := bundle.normalizedPresentation
            let occurrence := SubtileOccurrenceInterpretation placement.layout.P
              placement.layout.u placement.layout.v
            let selectedPath := ∃ selectedStart selectedEnd : GaussianInt,
              SimpleGridPathBetween
                (FootprintVertices (occurrence placement.exteriorIndex) ∩
                  FootprintVertices (occurrence placement.centralIndex))
                (FootprintEdges (occurrence placement.exteriorIndex) ∩
                  FootprintEdges (occurrence placement.centralIndex))
                selectedStart selectedEnd ∧
              selectedEdge ∈
                FootprintEdges (occurrence placement.exteriorIndex) ∩
                  FootprintEdges (occurrence placement.centralIndex) ∧
              bundle.normalizedPoint ∈ selectedEdge
            let rightGeometry := fun (i j : Fin 3) (sgn : GaussianInt)
                (firstSign secondSign : Bool) ↦
              let firstCompanion := TileTranslation bundle.normalizedFixed
                (sgn * BandVectors.1 (q 0) (q i.succ))
              let secondCompanion := TileTranslation bundle.normalizedFixed
                (sgn * BandVectors.1 (q 0) (q j.succ))
              let firstPiece := TileTranslation (placement.layout.P i firstSign)
                placement.rightNeighborDisplacement
              let secondPiece := TileTranslation (placement.layout.P j secondSign)
                placement.rightNeighborDisplacement
              ∃ firstBoundaryData : ExactTileInterfaceTriple bundle.normalizedFixed
                  firstCompanion firstPiece,
                ∃ secondBoundaryData : ExactTileInterfaceTriple bundle.normalizedFixed
                    secondCompanion secondPiece,
                  ∃ firstData : ExactTileInterfaceTriple bundle.normalizedRoot
                      bundle.normalizedFixed firstCompanion,
                    ∃ secondData : ExactTileInterfaceTriple bundle.normalizedRoot
                        bundle.normalizedFixed secondCompanion,
                      firstBoundaryData.point = firstData.point ∧
                      secondBoundaryData.point = secondData.point ∧
                      LatticeTile bundle.normalizedRoot ∧
                      LatticeTile bundle.normalizedFixed ∧
                      LatticeTile firstCompanion ∧
                      LatticeTile secondCompanion ∧
                      Disjoint bundle.normalizedRoot.cells firstCompanion.cells ∧
                      Disjoint bundle.normalizedFixed.cells firstCompanion.cells ∧
                      Disjoint bundle.normalizedRoot.cells secondCompanion.cells ∧
                      Disjoint bundle.normalizedFixed.cells secondCompanion.cells ∧
                      Disjoint firstCompanion.cells secondCompanion.cells ∧
                      TouchingTriple bundle.normalizedRoot bundle.normalizedFixed
                        firstCompanion ∧
                      TouchingTriple bundle.normalizedRoot bundle.normalizedFixed
                        secondCompanion ∧
                      firstData.point ≠ secondData.point ∧
                      secondData.point = firstData.otherAB ∧
                      secondData.otherAB = firstData.point ∧
                      selectedPath
            (placement.rightNeighborPositive = true ∧
                  bundle.selectedSlot = placement.rightFirstSlot ∧
                  bundle.selectedSign = true ∧
                  rightGeometry placement.rightFirstSlot placement.rightSecondSlot
                    (-1) true false) ∨
               (placement.rightNeighborPositive = true ∧
                  bundle.selectedSlot = placement.rightSecondSlot ∧
                  bundle.selectedSign = false ∧
                  rightGeometry placement.rightFirstSlot placement.rightSecondSlot
                    (-1) true false) ∨
               (placement.rightNeighborPositive = false ∧
                  bundle.selectedSlot = placement.rightFirstSlot ∧
                  bundle.selectedSign = false ∧
                  rightGeometry placement.rightFirstSlot placement.rightSecondSlot
                    1 false true) ∨
               (placement.rightNeighborPositive = false ∧
                  bundle.selectedSlot = placement.rightSecondSlot ∧
                  bundle.selectedSign = true ∧
                  rightGeometry placement.rightFirstSlot placement.rightSecondSlot
                    1 false true))))))))))))) ) := by
  classical
  intro C D T N h k x bundle placement selectedEdge chosenBoundary q F root edgeVertex norm
      childInterfaces turnOutgoing turnNeg boundaryRecords centeredExactTurn tripleTurnOutgoing
      tripleTurnNegativeNext touchingPlus touchingMinus P u v selectedPath rightGeometry
      canonicalFinish coordinateFactsApos coordinateFactsAneg period0 period1 period2
      packageGeometry firstBoundarySubset secondBoundarySubset hcycle
  let exactMinus (ell : Fin 3) : ExactTileInterfaceTriple F
      (TileTranslation F (-BandVectors.1 (q 0) (q ell.succ)))
      (TileTranslation F (BandVectors.1 (q 0) (q (ell + 1).succ))) := by
    let E := Classical.choice ((SelectedRowGeometry.thriceExactTurn C D T N h k x bundle
        centeredExactTurn)
      (BandVectors.1 (q ell.succ) (q 0))
      (-BandVectors.1 (q (ell + 1).succ) (q 0))
      (Classical.choice (childInterfaces.1 ell)))
    simpa only [tripleTurnOutgoing, tripleTurnNegativeNext] using E
  let exactPlus (ell : Fin 3) : ExactTileInterfaceTriple F
      (TileTranslation F (BandVectors.1 (q 0) (q ell.succ)))
      (TileTranslation F (-BandVectors.1 (q 0) (q (ell + 1).succ))) := by
    let E := Classical.choice (centeredExactTurn
      (BandVectors.1 (q ell.succ) (q 0))
      (-BandVectors.1 (q (ell + 1).succ) (q 0))
      (Classical.choice (childInterfaces.1 ell)))
    simpa [turnOutgoing, turnNeg] using E
  rcases hcycle with ⟨hi, hj, hk⟩
  have hcyc :
      (placement.rightFirstSlot = 0 ∧ placement.rightSecondSlot = 1 ∧
        placement.rightDirectionSlot = 2) ∨
      (placement.rightFirstSlot = 1 ∧ placement.rightSecondSlot = 2 ∧
        placement.rightDirectionSlot = 0) ∨
      (placement.rightFirstSlot = 2 ∧ placement.rightSecondSlot = 0 ∧
        placement.rightDirectionSlot = 1) := Or.inl ⟨hi, hj, hk⟩
  have records := boundaryRecords hcyc
  cases hpos : placement.rightNeighborPositive
  · have hR : placement.rightNeighborDisplacement =
        -BandVectors.1 (q 0) (q 3) := SelectedRowGeometry.hRAt1171 C D T N h k x bundle
            placement hk hpos
    rcases records.2 hpos with ⟨⟨R1⟩, ⟨R2⟩⟩
    have R1' : ExactTileInterfaceTriple F
        (TileTranslation F (BandVectors.1 (q 0) (q 1)))
        (TileTranslation (placement.layout.P 0 false)
          placement.rightNeighborDisplacement) := by
      simpa [hi] using R1
    have R2' : ExactTileInterfaceTriple F
        (TileTranslation F (BandVectors.1 (q 0) (q 2)))
        (TileTranslation (placement.layout.P 1 true)
          placement.rightNeighborDisplacement) := by
      simpa [hj] using R2
    have eStart : ExactTileInterfaceTriple F
        (TileTranslation F placement.rightNeighborDisplacement)
        (TileTranslation F ((1 : GaussianInt) * BandVectors.1 (q 0) (q 1))) := by
      simpa [hR] using exactMinus 2
    have eEnd : ExactTileInterfaceTriple F
        (TileTranslation F ((1 : GaussianInt) * BandVectors.1 (q 0) (q 2)))
        (TileTranslation F placement.rightNeighborDisplacement) := by
      simpa [hR] using exactPlus 1
    have tStart := SelectedRowGeometry.tStartAt1193 C D T N h k x bundle placement
        touchingMinus hR
    have tEnd := SelectedRowGeometry.tEndAt1197 C D T N h k x bundle placement touchingPlus hR
    rcases canonicalFinish ((1 : GaussianInt) * BandVectors.1 (q 0) (q 1))
        ((1 : GaussianInt) * BandVectors.1 (q 0) (q 2)) 1 1 1 0 0 1
        (by rw [hR, period2]; ring)
        (by rw [period0]; simp) (by rw [period1]; simp)
        coordinateFactsApos.1 coordinateFactsApos.2.1
        coordinateFactsApos.2.2.1 coordinateFactsApos.2.2.2.1
        coordinateFactsApos.2.2.2.2.1 coordinateFactsApos.2.2.2.2.2
        eStart eEnd tStart tEnd with
      ⟨g, hgs, hge, hneq⟩
    have hsigns := placement.boundary_signs
    rcases hsigns with ⟨hp, hfirst, hsecond⟩ | ⟨hp, hfirst, hsecond⟩
    · rw [hpos] at hp
      cases hp
    · have geom := SelectedRowGeometry.geomAt1214 C D T N h k x bundle placement selectedEdge
        edgeVertex packageGeometry firstBoundarySubset secondBoundarySubset hi hj R1 R2 g
        hgs hge hneq hfirst hsecond
      have hgeom := (show
          rightGeometry placement.rightFirstSlot placement.rightSecondSlot 1 false
          true
        from by
          classical
          rw [hi, hj]
          exact geom)
      rcases chosenBoundary with ⟨hs, hsign⟩ |
        ⟨hs, hsign⟩
      · have hselectedSign : bundle.selectedSign = false := by
          exact hsign.trans hfirst
        exact Or.inr (Or.inr (Or.inl ⟨rfl, hs, hselectedSign, hgeom⟩))
      · have hselectedSign : bundle.selectedSign = true := by
          exact hsign.trans hsecond
        exact Or.inr (Or.inr (Or.inr ⟨rfl, hs, hselectedSign, hgeom⟩))
  · have hR : placement.rightNeighborDisplacement =
        BandVectors.1 (q 0) (q 3) := SelectedRowGeometry.hRAt1245 C D T N h k x bundle
            placement hk hpos
    rcases records.1 hpos with ⟨⟨R1⟩, ⟨R2⟩⟩
    have R1' : ExactTileInterfaceTriple F
        (TileTranslation F (-BandVectors.1 (q 0) (q 1)))
        (TileTranslation (placement.layout.P 0 true)
          placement.rightNeighborDisplacement) := by
      simpa [hi] using R1
    have R2' : ExactTileInterfaceTriple F
        (TileTranslation F (-BandVectors.1 (q 0) (q 2)))
        (TileTranslation (placement.layout.P 1 false)
          placement.rightNeighborDisplacement) := by
      simpa [hj] using R2
    have eStart : ExactTileInterfaceTriple F
        (TileTranslation F placement.rightNeighborDisplacement)
        (TileTranslation F ((-1 : GaussianInt) * BandVectors.1 (q 0) (q 1))) := by
      simpa [hR] using exactPlus 2
    have eEnd : ExactTileInterfaceTriple F
        (TileTranslation F ((-1 : GaussianInt) * BandVectors.1 (q 0) (q 2)))
        (TileTranslation F placement.rightNeighborDisplacement) := by
      simpa [hR] using exactMinus 1
    have tStart := SelectedRowGeometry.tStartAt1267 C D T N h k x bundle placement
        touchingPlus hR
    have tEnd := SelectedRowGeometry.tEndAt1271 C D T N h k x bundle placement touchingMinus hR
    rcases canonicalFinish ((-1 : GaussianInt) * BandVectors.1 (q 0) (q 1))
        ((-1 : GaussianInt) * BandVectors.1 (q 0) (q 2)) (-1) (-1) (-1) 0 0 (-1)
        (by rw [hR, period2]; ring)
        (by rw [period0]; simp) (by rw [period1]; simp)
        coordinateFactsAneg.1 coordinateFactsAneg.2.1
        coordinateFactsAneg.2.2.1 coordinateFactsAneg.2.2.2.1
        coordinateFactsAneg.2.2.2.2.1 coordinateFactsAneg.2.2.2.2.2
        eStart eEnd tStart tEnd with
      ⟨g, hgs, hge, hneq⟩
    have hsigns := placement.boundary_signs
    rcases hsigns with ⟨hp, hfirst, hsecond⟩ | ⟨hp, hfirst, hsecond⟩
    · have geom := SelectedRowGeometry.geomAt1286 C D T N h k x bundle placement selectedEdge
        edgeVertex packageGeometry firstBoundarySubset secondBoundarySubset hi hj R1 R2 g
        hgs hge hneq hfirst hsecond
      have hgeom := (show
          rightGeometry placement.rightFirstSlot placement.rightSecondSlot (-1) true
          false
        from by
          classical
          rw [hi, hj]
          exact geom)
      rcases chosenBoundary with ⟨hs, hsign⟩ |
        ⟨hs, hsign⟩
      · have hselectedSign : bundle.selectedSign = true := by
          exact hsign.trans hfirst
        exact Or.inl ⟨rfl, hs, hselectedSign, hgeom⟩
      · have hselectedSign : bundle.selectedSign = false := by
          exact hsign.trans hsecond
        exact Or.inr (Or.inl ⟨rfl, hs, hselectedSign, hgeom⟩)
    · rw [hpos] at hp
      cases hp

private theorem secondCyclicCase :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), ∀ (selectedEdge : Finset GaussianInt), (bundle.selectedSlot
                = placement.rightFirstSlot ∧ bundle.selectedSign =
            placement.firstBoundarySign ∨ bundle.selectedSlot = placement.rightSecondSlot ∧
            bundle.selectedSign = placement.secondBoundarySign) →
        let q := bundle.normalizedPresentation;
        let F := bundle.normalizedFixed;
        let root := bundle.normalizedRoot;
        let norm := SelectedRowNormalization.certificate C D T N h k x bundle placement
        ∀ (childInterfaces : (∀ (i : Fin (3 : ℕ)), Nonempty (ExactTileInterfaceTriple F
            (TileTranslation F (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) (TileTranslation
            F (-BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ))))))) ∧ (∀ (i
            : Fin (3 : ℕ)), ∀ (U : ProtoTile), BandPrototile (q i.succ) U → TileCentroid U -
            TileCentroid F = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)))
            → Nonempty (ExactTileInterfaceTriple F (TileTranslation F (BandVectors.1 (q i.succ)
            (q (0 : Fin (4 : ℕ))))) U)) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), BandPrototile (q i.succ) U → BandPrototile (q (i + (1 : Fin (3 :
            ℕ))).succ) V → TileCentroid U - TileCentroid F = (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1
            (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid V - TileCentroid F = (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 :
            ℕ)))) - GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i + (1 : Fin (3 :
            ℕ))).succ))) → Nonempty (ExactTileInterfaceTriple F U V)) ∧ ∀ (i : Fin (3 : ℕ)), ∀ (s
            : Fin (4 : ℕ)), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q i.succ) U →
            BandPrototile (q (if Even (↑s : ℕ) then i + (1 : Fin (3 : ℕ)) else i - (1 : Fin (3 :
            ℕ))).succ) V → TileCentroid U - TileCentroid F = (1 / 2 : ℝ) • GaussianRealPoint
            ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid V -
            TileCentroid F = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)
            ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q
            (0 : Fin (4 : ℕ))) - BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i + (1 : Fin (3 :
            ℕ))).succ) else BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i - (1 : Fin (3 : ℕ))).succ)
            - BandVectors.1 (q (i - (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))) →
        let uR := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) else BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)));
        let uL := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then
            BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))) else BandVectors.1 (q (0 : Fin (4 :
            ℕ))) (q i.succ); ∃ (rightData : ExactTileInterfaceTriple F (TileTranslation F uR) U)
            (incomingData : ExactTileInterfaceTriple F (TileTranslation F uL) U) (t5Data :
            ExactTileInterfaceTriple F U V), rightData.point = t5Data.point ∧ incomingData.point
            ≠ t5Data.point ∧ incomingData.otherCA = t5Data.point ∧ rightData.otherCA =
            incomingData.point ∧ t5Data.otherAB = incomingData.point), ∀ (turnOutgoing : ∀ (s :
            Fin 3), GaussianQuarterTurn (BandVectors.1 (q s.succ) (q 0)) = BandVectors.1 (q 0) (q
            s.succ)), ∀ (turnNeg : ∀ (z : GaussianInt), GaussianQuarterTurn (-z) =
            -GaussianQuarterTurn z), ∀ (boundaryRecords : placement.rightFirstSlot = (0 : Fin (3
            : ℕ)) ∧ placement.rightSecondSlot = (1 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot
            = (2 : Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (1 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (2 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (0 :
            Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (2 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (0 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (1 :
            Fin (3 : ℕ)) → (placement.rightNeighborPositive = true → Nonempty
            (ExactTileInterfaceTriple bundle.normalizedFixed (TileTranslation
            bundle.normalizedFixed (-BandVectors.1 (bundle.normalizedPresentation (0 : Fin (4 :
            ℕ))) (bundle.normalizedPresentation placement.rightFirstSlot.succ))) (TileTranslation
            (placement.layout.P placement.rightFirstSlot true)
            placement.rightNeighborDisplacement)) ∧ Nonempty (ExactTileInterfaceTriple
            bundle.normalizedFixed (TileTranslation bundle.normalizedFixed (-BandVectors.1
            (bundle.normalizedPresentation (0 : Fin (4 : ℕ))) (bundle.normalizedPresentation
            placement.rightSecondSlot.succ))) (TileTranslation (placement.layout.P
            placement.rightSecondSlot false) placement.rightNeighborDisplacement))) ∧
            (placement.rightNeighborPositive = false → Nonempty (ExactTileInterfaceTriple
            bundle.normalizedFixed (TileTranslation bundle.normalizedFixed (BandVectors.1
            (bundle.normalizedPresentation (0 : Fin (4 : ℕ))) (bundle.normalizedPresentation
            placement.rightFirstSlot.succ))) (TileTranslation (placement.layout.P
            placement.rightFirstSlot false) placement.rightNeighborDisplacement)) ∧ Nonempty
            (ExactTileInterfaceTriple bundle.normalizedFixed (TileTranslation
            bundle.normalizedFixed (BandVectors.1 (bundle.normalizedPresentation (0 : Fin (4 :
            ℕ))) (bundle.normalizedPresentation placement.rightSecondSlot.succ)))
            (TileTranslation (placement.layout.P placement.rightSecondSlot true)
            placement.rightNeighborDisplacement)))), ∀ (centeredExactTurn : ∀ (a : GaussianInt),
            ∀ (b : GaussianInt), (ExactTileInterfaceTriple F (TileTranslation F a)
            (TileTranslation F b)) → (Nonempty (ExactTileInterfaceTriple F (TileTranslation F
            (GaussianQuarterTurn a)) (TileTranslation F (GaussianQuarterTurn b))))), ∀
            (tripleTurnOutgoing : ∀ (ell : Fin 3), GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianQuarterTurn (BandVectors.1 (q ell.succ) (q 0)))) = -BandVectors.1 (q 0) (q
            ell.succ)), ∀ (tripleTurnNegativeNext : ∀ (ell : Fin 3), GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianQuarterTurn (-BandVectors.1 (q (ell + 1).succ) (q 0))))
            = BandVectors.1 (q 0) (q (ell + 1).succ)),
        (∀ (ell : Fin 3), TouchingTriple F (TileTranslation F (BandVectors.1 (q 0) (q ell.succ)))
            (TileTranslation F (-BandVectors.1 (q 0) (q (ell + 1).succ)))) → ((∀ (ell : Fin 3),
            TouchingTriple F (TileTranslation F (-BandVectors.1 (q 0) (q ell.succ)))
            (TileTranslation F (BandVectors.1 (q 0) (q (ell + 1).succ)))) → (
        let P := placement.layout.P
        let u := placement.layout.u
        let v := placement.layout.v
        let selectedPath : Prop :=
            (∃ selectedStart selectedEnd : GaussianInt,
              SimpleGridPathBetween
                (FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                (FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                selectedStart selectedEnd ∧
              selectedEdge ∈
                FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex) ∧
              bundle.normalizedPoint ∈ selectedEdge)
        let rightGeometry := fun (i j : Fin 3) (sgn : GaussianInt)
            (firstSign secondSign : Bool) ↦
          let firstCompanion := TileTranslation F
            (sgn * BandVectors.1 (q 0) (q i.succ))
          let secondCompanion := TileTranslation F
            (sgn * BandVectors.1 (q 0) (q j.succ))
          let firstPiece := TileTranslation (placement.layout.P i firstSign)
            placement.rightNeighborDisplacement
          let secondPiece := TileTranslation (placement.layout.P j secondSign)
            placement.rightNeighborDisplacement
          ∃ firstBoundaryData : ExactTileInterfaceTriple F firstCompanion firstPiece,
            ∃ secondBoundaryData : ExactTileInterfaceTriple F secondCompanion secondPiece,
              ∃ firstData : ExactTileInterfaceTriple root F firstCompanion,
                ∃ secondData : ExactTileInterfaceTriple root F secondCompanion,
                  firstBoundaryData.point = firstData.point ∧
                  secondBoundaryData.point = secondData.point ∧
                  LatticeTile root ∧ LatticeTile F ∧ LatticeTile firstCompanion ∧
                  LatticeTile secondCompanion ∧ Disjoint root.cells firstCompanion.cells ∧
                  Disjoint F.cells firstCompanion.cells ∧
                  Disjoint root.cells secondCompanion.cells ∧
                  Disjoint F.cells secondCompanion.cells ∧
                  Disjoint firstCompanion.cells secondCompanion.cells ∧
                  TouchingTriple root F firstCompanion ∧
                  TouchingTriple root F secondCompanion ∧
                  firstData.point ≠ secondData.point ∧
                  secondData.point = firstData.otherAB ∧
                  secondData.otherAB = firstData.point ∧ selectedPath
        (∀ (uStart : GaussianInt), ∀ (uEnd : GaussianInt), ∀ (mR : Int), ∀ (nR : Int), ∀ (mS :
            Int), ∀ (nS : Int), ∀ (mE : Int), ∀ (nE : Int), (placement.rightNeighborDisplacement
            = (mR : GaussianInt) * placement.layout.u + (nR : GaussianInt) * placement.layout.v)
            → ((uStart = (mS : GaussianInt) * placement.layout.u + (nS : GaussianInt) *
            placement.layout.v) → ((uEnd = (mE : GaussianInt) * placement.layout.u + (nE :
            GaussianInt) * placement.layout.v) → (((0, 0) ≠ (mR, nR)) → (((0, 0) ≠ (mS, nS)) →
            (((0, 0) ≠ (mE, nE)) → (((mR, nR) ≠ (mS, nS)) → (((mR, nR) ≠ (mE, nE)) → (((mS, nS) ≠
            (mE, nE)) → ((ExactTileInterfaceTriple F (TileTranslation F
            placement.rightNeighborDisplacement) (TileTranslation F uStart)) →
            ((ExactTileInterfaceTriple F (TileTranslation F uEnd) (TileTranslation F
            placement.rightNeighborDisplacement)) → ((TouchingTriple F (TileTranslation F
            placement.rightNeighborDisplacement) (TileTranslation F uStart)) → ((TouchingTriple F
            (TileTranslation F uEnd) (TileTranslation F placement.rightNeighborDisplacement)) →
            (∃ g : BandOrderedGeneralRightInterfaceCertificate norm, g.startCompanion =
            TileTranslation F uStart ∧ g.endCompanion = TileTranslation F uEnd ∧
            g.startData.point ≠ g.endData.point)))))))))))))) → ((((0, 0) : Int × Int) ≠ (-1, 0)
            ∧ ((0, 0) : Int × Int) ≠ (0, 1) ∧ ((0, 0) : Int × Int) ≠ (-1, -1) ∧ ((-1, 0) : Int ×
            Int) ≠ (0, 1) ∧ ((-1, 0) : Int × Int) ≠ (-1, -1) ∧ ((0, 1) : Int × Int) ≠ (-1, -1)) →
            ((((0, 0) : Int × Int) ≠ (1, 0) ∧ ((0, 0) : Int × Int) ≠ (0, -1) ∧ ((0, 0) : Int ×
            Int) ≠ (1, 1) ∧ ((1, 0) : Int × Int) ≠ (0, -1) ∧ ((1, 0) : Int × Int) ≠ (1, 1) ∧ ((0,
            -1) : Int × Int) ≠ (1, 1)) → ((BandVectors.1 (q 0) (q 1) = placement.layout.u) →
            ((BandVectors.1 (q 0) (q 2) = placement.layout.v) → ((BandVectors.1 (q 0) (q 3) =
            -placement.layout.u - placement.layout.v) → ((∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (sgn :
            GaussianInt), ∀ (s₁ : Bool), ∀ (s₂ : Bool), ∀ (g :
            BandOrderedGeneralRightInterfaceCertificate norm), (g.startCompanion =
            TileTranslation F (sgn * BandVectors.1 (q 0) (q i.succ))) → ((g.endCompanion =
            TileTranslation F (sgn * BandVectors.1 (q 0) (q j.succ))) → ((g.startData.point ≠
            g.endData.point) → ((ExactTileInterfaceTriple F g.startCompanion (TileTranslation
            (placement.layout.P i s₁) placement.rightNeighborDisplacement)) →
            ((ExactTileInterfaceTriple F g.endCompanion (TileTranslation (placement.layout.P j
            s₂) placement.rightNeighborDisplacement)) → ((FootprintVertices (TileTranslation
            (placement.layout.P i s₁) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root) → ((FootprintVertices (TileTranslation (placement.layout.P j s₂)
            placement.rightNeighborDisplacement) ⊆ FootprintVertices root) → (rightGeometry i j
            sgn s₁ s₂)))))))) → ((FootprintVertices (TileTranslation (placement.layout.P
            placement.rightFirstSlot placement.firstBoundarySign)
            placement.rightNeighborDisplacement) ⊆ FootprintVertices root) → ((FootprintVertices
            (TileTranslation (placement.layout.P placement.rightSecondSlot
            placement.secondBoundarySign) placement.rightNeighborDisplacement) ⊆
            FootprintVertices root) → ((placement.rightFirstSlot = (1 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (2 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (0 :
            Fin (3 : ℕ))) → (
        let q := bundle.normalizedPresentation
            let occurrence := SubtileOccurrenceInterpretation placement.layout.P
              placement.layout.u placement.layout.v
            let selectedPath := ∃ selectedStart selectedEnd : GaussianInt,
              SimpleGridPathBetween
                (FootprintVertices (occurrence placement.exteriorIndex) ∩
                  FootprintVertices (occurrence placement.centralIndex))
                (FootprintEdges (occurrence placement.exteriorIndex) ∩
                  FootprintEdges (occurrence placement.centralIndex))
                selectedStart selectedEnd ∧
              selectedEdge ∈
                FootprintEdges (occurrence placement.exteriorIndex) ∩
                  FootprintEdges (occurrence placement.centralIndex) ∧
              bundle.normalizedPoint ∈ selectedEdge
            let rightGeometry := fun (i j : Fin 3) (sgn : GaussianInt)
                (firstSign secondSign : Bool) ↦
              let firstCompanion := TileTranslation bundle.normalizedFixed
                (sgn * BandVectors.1 (q 0) (q i.succ))
              let secondCompanion := TileTranslation bundle.normalizedFixed
                (sgn * BandVectors.1 (q 0) (q j.succ))
              let firstPiece := TileTranslation (placement.layout.P i firstSign)
                placement.rightNeighborDisplacement
              let secondPiece := TileTranslation (placement.layout.P j secondSign)
                placement.rightNeighborDisplacement
              ∃ firstBoundaryData : ExactTileInterfaceTriple bundle.normalizedFixed
                  firstCompanion firstPiece,
                ∃ secondBoundaryData : ExactTileInterfaceTriple bundle.normalizedFixed
                    secondCompanion secondPiece,
                  ∃ firstData : ExactTileInterfaceTriple bundle.normalizedRoot
                      bundle.normalizedFixed firstCompanion,
                    ∃ secondData : ExactTileInterfaceTriple bundle.normalizedRoot
                        bundle.normalizedFixed secondCompanion,
                      firstBoundaryData.point = firstData.point ∧
                      secondBoundaryData.point = secondData.point ∧
                      LatticeTile bundle.normalizedRoot ∧
                      LatticeTile bundle.normalizedFixed ∧
                      LatticeTile firstCompanion ∧
                      LatticeTile secondCompanion ∧
                      Disjoint bundle.normalizedRoot.cells firstCompanion.cells ∧
                      Disjoint bundle.normalizedFixed.cells firstCompanion.cells ∧
                      Disjoint bundle.normalizedRoot.cells secondCompanion.cells ∧
                      Disjoint bundle.normalizedFixed.cells secondCompanion.cells ∧
                      Disjoint firstCompanion.cells secondCompanion.cells ∧
                      TouchingTriple bundle.normalizedRoot bundle.normalizedFixed
                        firstCompanion ∧
                      TouchingTriple bundle.normalizedRoot bundle.normalizedFixed
                        secondCompanion ∧
                      firstData.point ≠ secondData.point ∧
                      secondData.point = firstData.otherAB ∧
                      secondData.otherAB = firstData.point ∧
                      selectedPath
            (placement.rightNeighborPositive = true ∧
                  bundle.selectedSlot = placement.rightFirstSlot ∧
                  bundle.selectedSign = true ∧
                  rightGeometry placement.rightFirstSlot placement.rightSecondSlot
                    (-1) true false) ∨
               (placement.rightNeighborPositive = true ∧
                  bundle.selectedSlot = placement.rightSecondSlot ∧
                  bundle.selectedSign = false ∧
                  rightGeometry placement.rightFirstSlot placement.rightSecondSlot
                    (-1) true false) ∨
               (placement.rightNeighborPositive = false ∧
                  bundle.selectedSlot = placement.rightFirstSlot ∧
                  bundle.selectedSign = false ∧
                  rightGeometry placement.rightFirstSlot placement.rightSecondSlot
                    1 false true) ∨
               (placement.rightNeighborPositive = false ∧
                  bundle.selectedSlot = placement.rightSecondSlot ∧
                  bundle.selectedSign = true ∧
                  rightGeometry placement.rightFirstSlot placement.rightSecondSlot
                    1 false true))))))))))))) ) := by
  classical
  intro C D T N h k x bundle placement selectedEdge chosenBoundary q F root norm childInterfaces
      turnOutgoing turnNeg boundaryRecords centeredExactTurn tripleTurnOutgoing
      tripleTurnNegativeNext touchingPlus touchingMinus P u v selectedPath rightGeometry
      canonicalFinish coordinateFactsBpos coordinateFactsBneg period0 period1 period2
      packageGeometry firstBoundarySubset secondBoundarySubset hcycle
  let exactMinus (ell : Fin 3) : ExactTileInterfaceTriple F
      (TileTranslation F (-BandVectors.1 (q 0) (q ell.succ)))
      (TileTranslation F (BandVectors.1 (q 0) (q (ell + 1).succ))) := by
    let E := Classical.choice ((SelectedRowGeometry.thriceExactTurn C D T N h k x bundle
        centeredExactTurn)
      (BandVectors.1 (q ell.succ) (q 0))
      (-BandVectors.1 (q (ell + 1).succ) (q 0))
      (Classical.choice (childInterfaces.1 ell)))
    simpa only [tripleTurnOutgoing, tripleTurnNegativeNext] using E
  let exactPlus (ell : Fin 3) : ExactTileInterfaceTriple F
      (TileTranslation F (BandVectors.1 (q 0) (q ell.succ)))
      (TileTranslation F (-BandVectors.1 (q 0) (q (ell + 1).succ))) := by
    let E := Classical.choice (centeredExactTurn
      (BandVectors.1 (q ell.succ) (q 0))
      (-BandVectors.1 (q (ell + 1).succ) (q 0))
      (Classical.choice (childInterfaces.1 ell)))
    simpa [turnOutgoing, turnNeg] using E
  rcases hcycle with ⟨hi, hj, hk⟩
  have hcyc :
      (placement.rightFirstSlot = 0 ∧ placement.rightSecondSlot = 1 ∧
        placement.rightDirectionSlot = 2) ∨
      (placement.rightFirstSlot = 1 ∧ placement.rightSecondSlot = 2 ∧
        placement.rightDirectionSlot = 0) ∨
      (placement.rightFirstSlot = 2 ∧ placement.rightSecondSlot = 0 ∧
        placement.rightDirectionSlot = 1) := Or.inr (Or.inl ⟨hi, hj, hk⟩)
  have records := boundaryRecords hcyc
  cases hpos : placement.rightNeighborPositive
  · have hR : placement.rightNeighborDisplacement =
        -BandVectors.1 (q 0) (q 1) := SelectedRowGeometry.hRAt1329 C D T N h k x bundle
            placement hk hpos
    rcases records.2 hpos with ⟨⟨R1⟩, ⟨R2⟩⟩
    have eStart : ExactTileInterfaceTriple F
        (TileTranslation F placement.rightNeighborDisplacement)
        (TileTranslation F ((1 : GaussianInt) * BandVectors.1 (q 0) (q 2))) := by
      simpa [hR] using exactMinus 0
    have eEnd : ExactTileInterfaceTriple F
        (TileTranslation F ((1 : GaussianInt) * BandVectors.1 (q 0) (q 3)))
        (TileTranslation F placement.rightNeighborDisplacement) := by
      simpa [hR] using exactPlus 2
    have tStart := SelectedRowGeometry.tStartAt1341 C D T N h k x bundle placement
        touchingMinus hR
    have tEnd := SelectedRowGeometry.tEndAt1345 C D T N h k x bundle placement touchingPlus hR
    rcases canonicalFinish ((1 : GaussianInt) * BandVectors.1 (q 0) (q 2))
        ((1 : GaussianInt) * BandVectors.1 (q 0) (q 3)) (-1) 0 0 1 (-1) (-1)
        (by rw [hR, period0]; simp)
        (by rw [period1]; simp) (by rw [period2]; ring)
        coordinateFactsBpos.1 coordinateFactsBpos.2.1
        coordinateFactsBpos.2.2.1 coordinateFactsBpos.2.2.2.1
        coordinateFactsBpos.2.2.2.2.1 coordinateFactsBpos.2.2.2.2.2
        eStart eEnd tStart tEnd with
      ⟨g, hgs, hge, hneq⟩
    rcases placement.boundary_signs with ⟨hp, _, _⟩ | ⟨hp, hfirst, hsecond⟩
    · rw [hpos] at hp
      cases hp
    · have R1g : ExactTileInterfaceTriple F g.startCompanion
          (TileTranslation (placement.layout.P 1 false)
            placement.rightNeighborDisplacement) := by
        simpa [hgs, hi] using R1
      have R2g : ExactTileInterfaceTriple F g.endCompanion
          (TileTranslation (placement.layout.P 2 true)
            placement.rightNeighborDisplacement) := by
        simpa [hge, hj] using R2
      have hW := SelectedRowGeometry.hWAt1369 C D T N h k x bundle placement
          firstBoundarySubset hi hfirst
      have hX := SelectedRowGeometry.hXAt1373 C D T N h k x bundle placement
          secondBoundarySubset hj hsecond
      have geom := packageGeometry 1 2 1 false true g hgs hge hneq R1g R2g hW hX
      have hgeom := (show
          rightGeometry placement.rightFirstSlot placement.rightSecondSlot 1 false
          true
        from by
          classical
          rw [hi, hj]
          exact geom)
      rcases chosenBoundary with ⟨hs, hsign⟩ |
        ⟨hs, hsign⟩
      · have hs' : bundle.selectedSign = false := by
          exact hsign.trans hfirst
        exact Or.inr (Or.inr (Or.inl ⟨rfl, hs, hs', hgeom⟩))
      · have hs' : bundle.selectedSign = true := by
          exact hsign.trans hsecond
        exact Or.inr (Or.inr (Or.inr ⟨rfl, hs, hs', hgeom⟩))
  · have hR : placement.rightNeighborDisplacement =
        BandVectors.1 (q 0) (q 1) := SelectedRowGeometry.hRAt1390 C D T N h k x bundle
            placement hk hpos
    rcases records.1 hpos with ⟨⟨R1⟩, ⟨R2⟩⟩
    have eStart : ExactTileInterfaceTriple F
        (TileTranslation F placement.rightNeighborDisplacement)
        (TileTranslation F ((-1 : GaussianInt) * BandVectors.1 (q 0) (q 2))) := by
      simpa [hR] using exactPlus 0
    have eEnd : ExactTileInterfaceTriple F
        (TileTranslation F ((-1 : GaussianInt) * BandVectors.1 (q 0) (q 3)))
        (TileTranslation F placement.rightNeighborDisplacement) := by
      simpa [hR] using exactMinus 2
    have tStart := SelectedRowGeometry.tStartAt1402 C D T N h k x bundle placement
        touchingPlus hR
    have tEnd := SelectedRowGeometry.tEndAt1406 C D T N h k x bundle placement touchingMinus hR
    have finishResult := canonicalFinish ((-1 : GaussianInt) * BandVectors.1 (q 0) (q 2))
        ((-1 : GaussianInt) * BandVectors.1 (q 0) (q 3)) 1 0 0 (-1) 1 1
        (by simp [hR, period0])
        (by rw [period1]; simp) (by rw [period2]; ring)
        coordinateFactsBneg.1 coordinateFactsBneg.2.1
        coordinateFactsBneg.2.2.1 coordinateFactsBneg.2.2.2.1
        coordinateFactsBneg.2.2.2.2.1 coordinateFactsBneg.2.2.2.2.2
        eStart eEnd tStart tEnd
    rcases finishResult with ⟨g, hgs, hge, hneq⟩
    rcases placement.boundary_signs with ⟨hp, hfirst, hsecond⟩ | ⟨hp, _, _⟩
    · have R1g : ExactTileInterfaceTriple F g.startCompanion
          (TileTranslation (placement.layout.P 1 true)
            placement.rightNeighborDisplacement) := by
        simpa [hgs, hi] using R1
      have R2g : ExactTileInterfaceTriple F g.endCompanion
          (TileTranslation (placement.layout.P 2 false)
            placement.rightNeighborDisplacement) := by
        simpa [hge, hj] using R2
      have hW := SelectedRowGeometry.hWAt1428 C D T N h k x bundle placement
          firstBoundarySubset hi hfirst
      have hX := SelectedRowGeometry.hXAt1432 C D T N h k x bundle placement
          secondBoundarySubset hj hsecond
      have geom := packageGeometry 1 2 (-1) true false g hgs hge hneq R1g R2g hW hX
      have hgeom := (show
          rightGeometry placement.rightFirstSlot placement.rightSecondSlot (-1) true
          false
        from by
          classical
          rw [hi, hj]
          exact geom)
      rcases chosenBoundary with ⟨hs, hsign⟩ |
        ⟨hs, hsign⟩
      · have hs' : bundle.selectedSign = true := by
          exact hsign.trans hfirst
        exact Or.inl ⟨rfl, hs, hs', hgeom⟩
      · have hs' : bundle.selectedSign = false := by
          exact hsign.trans hsecond
        exact Or.inr (Or.inl ⟨rfl, hs, hs', hgeom⟩)
    · rw [hpos] at hp
      cases hp

private theorem thirdCyclicCase :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection), ∀ (selectedEdge : Finset GaussianInt), (bundle.selectedSlot
                = placement.rightFirstSlot ∧ bundle.selectedSign =
            placement.firstBoundarySign ∨ bundle.selectedSlot = placement.rightSecondSlot ∧
            bundle.selectedSign = placement.secondBoundarySign) →
        let q := bundle.normalizedPresentation;
        let F := bundle.normalizedFixed;
        let root := bundle.normalizedRoot;
        let norm := SelectedRowNormalization.certificate C D T N h k x bundle placement
        ∀ (childInterfaces : (∀ (i : Fin (3 : ℕ)), Nonempty (ExactTileInterfaceTriple F
            (TileTranslation F (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) (TileTranslation
            F (-BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ))))))) ∧ (∀ (i
            : Fin (3 : ℕ)), ∀ (U : ProtoTile), BandPrototile (q i.succ) U → TileCentroid U -
            TileCentroid F = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)))
            → Nonempty (ExactTileInterfaceTriple F (TileTranslation F (BandVectors.1 (q i.succ)
            (q (0 : Fin (4 : ℕ))))) U)) ∧ (∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), BandPrototile (q i.succ) U → BandPrototile (q (i + (1 : Fin (3 :
            ℕ))).succ) V → TileCentroid U - TileCentroid F = (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1
            (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid V - TileCentroid F = (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 :
            ℕ)))) - GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i + (1 : Fin (3 :
            ℕ))).succ))) → Nonempty (ExactTileInterfaceTriple F U V)) ∧ ∀ (i : Fin (3 : ℕ)), ∀ (s
            : Fin (4 : ℕ)), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q i.succ) U →
            BandPrototile (q (if Even (↑s : ℕ) then i + (1 : Fin (3 : ℕ)) else i - (1 : Fin (3 :
            ℕ))).succ) V → TileCentroid U - TileCentroid F = (1 / 2 : ℝ) • GaussianRealPoint
            ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid V -
            TileCentroid F = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)
            ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q
            (0 : Fin (4 : ℕ))) - BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i + (1 : Fin (3 :
            ℕ))).succ) else BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i - (1 : Fin (3 : ℕ))).succ)
            - BandVectors.1 (q (i - (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))) →
        let uR := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) else BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)));
        let uL := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then
            BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))) else BandVectors.1 (q (0 : Fin (4 :
            ℕ))) (q i.succ); ∃ (rightData : ExactTileInterfaceTriple F (TileTranslation F uR) U)
            (incomingData : ExactTileInterfaceTriple F (TileTranslation F uL) U) (t5Data :
            ExactTileInterfaceTriple F U V), rightData.point = t5Data.point ∧ incomingData.point
            ≠ t5Data.point ∧ incomingData.otherCA = t5Data.point ∧ rightData.otherCA =
            incomingData.point ∧ t5Data.otherAB = incomingData.point), ∀ (turnOutgoing : ∀ (s :
            Fin 3), GaussianQuarterTurn (BandVectors.1 (q s.succ) (q 0)) = BandVectors.1 (q 0) (q
            s.succ)), ∀ (turnNeg : ∀ (z : GaussianInt), GaussianQuarterTurn (-z) =
            -GaussianQuarterTurn z), ∀ (boundaryRecords : placement.rightFirstSlot = (0 : Fin (3
            : ℕ)) ∧ placement.rightSecondSlot = (1 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot
            = (2 : Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (1 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (2 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (0 :
            Fin (3 : ℕ)) ∨ placement.rightFirstSlot = (2 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (0 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (1 :
            Fin (3 : ℕ)) → (placement.rightNeighborPositive = true → Nonempty
            (ExactTileInterfaceTriple bundle.normalizedFixed (TileTranslation
            bundle.normalizedFixed (-BandVectors.1 (bundle.normalizedPresentation (0 : Fin (4 :
            ℕ))) (bundle.normalizedPresentation placement.rightFirstSlot.succ))) (TileTranslation
            (placement.layout.P placement.rightFirstSlot true)
            placement.rightNeighborDisplacement)) ∧ Nonempty (ExactTileInterfaceTriple
            bundle.normalizedFixed (TileTranslation bundle.normalizedFixed (-BandVectors.1
            (bundle.normalizedPresentation (0 : Fin (4 : ℕ))) (bundle.normalizedPresentation
            placement.rightSecondSlot.succ))) (TileTranslation (placement.layout.P
            placement.rightSecondSlot false) placement.rightNeighborDisplacement))) ∧
            (placement.rightNeighborPositive = false → Nonempty (ExactTileInterfaceTriple
            bundle.normalizedFixed (TileTranslation bundle.normalizedFixed (BandVectors.1
            (bundle.normalizedPresentation (0 : Fin (4 : ℕ))) (bundle.normalizedPresentation
            placement.rightFirstSlot.succ))) (TileTranslation (placement.layout.P
            placement.rightFirstSlot false) placement.rightNeighborDisplacement)) ∧ Nonempty
            (ExactTileInterfaceTriple bundle.normalizedFixed (TileTranslation
            bundle.normalizedFixed (BandVectors.1 (bundle.normalizedPresentation (0 : Fin (4 :
            ℕ))) (bundle.normalizedPresentation placement.rightSecondSlot.succ)))
            (TileTranslation (placement.layout.P placement.rightSecondSlot true)
            placement.rightNeighborDisplacement)))), ∀ (centeredExactTurn : ∀ (a : GaussianInt),
            ∀ (b : GaussianInt), (ExactTileInterfaceTriple F (TileTranslation F a)
            (TileTranslation F b)) → (Nonempty (ExactTileInterfaceTriple F (TileTranslation F
            (GaussianQuarterTurn a)) (TileTranslation F (GaussianQuarterTurn b))))), ∀
            (tripleTurnOutgoing : ∀ (ell : Fin 3), GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianQuarterTurn (BandVectors.1 (q ell.succ) (q 0)))) = -BandVectors.1 (q 0) (q
            ell.succ)), ∀ (tripleTurnNegativeNext : ∀ (ell : Fin 3), GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianQuarterTurn (-BandVectors.1 (q (ell + 1).succ) (q 0))))
            = BandVectors.1 (q 0) (q (ell + 1).succ)),
        (∀ (ell : Fin 3), TouchingTriple F (TileTranslation F (BandVectors.1 (q 0) (q ell.succ)))
            (TileTranslation F (-BandVectors.1 (q 0) (q (ell + 1).succ)))) → ((∀ (ell : Fin 3),
            TouchingTriple F (TileTranslation F (-BandVectors.1 (q 0) (q ell.succ)))
            (TileTranslation F (BandVectors.1 (q 0) (q (ell + 1).succ)))) → (
        let P := placement.layout.P
        let u := placement.layout.u
        let v := placement.layout.v
        let selectedPath : Prop :=
            (∃ selectedStart selectedEnd : GaussianInt,
              SimpleGridPathBetween
                (FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintVertices
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                (FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex))
                selectedStart selectedEnd ∧
              selectedEdge ∈
                FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation P u v placement.centralIndex) ∧
              bundle.normalizedPoint ∈ selectedEdge)
        let rightGeometry := fun (i j : Fin 3) (sgn : GaussianInt)
            (firstSign secondSign : Bool) ↦
          let firstCompanion := TileTranslation F
            (sgn * BandVectors.1 (q 0) (q i.succ))
          let secondCompanion := TileTranslation F
            (sgn * BandVectors.1 (q 0) (q j.succ))
          let firstPiece := TileTranslation (placement.layout.P i firstSign)
            placement.rightNeighborDisplacement
          let secondPiece := TileTranslation (placement.layout.P j secondSign)
            placement.rightNeighborDisplacement
          ∃ firstBoundaryData : ExactTileInterfaceTriple F firstCompanion firstPiece,
            ∃ secondBoundaryData : ExactTileInterfaceTriple F secondCompanion secondPiece,
              ∃ firstData : ExactTileInterfaceTriple root F firstCompanion,
                ∃ secondData : ExactTileInterfaceTriple root F secondCompanion,
                  firstBoundaryData.point = firstData.point ∧
                  secondBoundaryData.point = secondData.point ∧
                  LatticeTile root ∧ LatticeTile F ∧ LatticeTile firstCompanion ∧
                  LatticeTile secondCompanion ∧ Disjoint root.cells firstCompanion.cells ∧
                  Disjoint F.cells firstCompanion.cells ∧
                  Disjoint root.cells secondCompanion.cells ∧
                  Disjoint F.cells secondCompanion.cells ∧
                  Disjoint firstCompanion.cells secondCompanion.cells ∧
                  TouchingTriple root F firstCompanion ∧
                  TouchingTriple root F secondCompanion ∧
                  firstData.point ≠ secondData.point ∧
                  secondData.point = firstData.otherAB ∧
                  secondData.otherAB = firstData.point ∧ selectedPath
        (∀ (uStart : GaussianInt), ∀ (uEnd : GaussianInt), ∀ (mR : Int), ∀ (nR : Int), ∀ (mS :
            Int), ∀ (nS : Int), ∀ (mE : Int), ∀ (nE : Int), (placement.rightNeighborDisplacement
            = (mR : GaussianInt) * placement.layout.u + (nR : GaussianInt) * placement.layout.v)
            → ((uStart = (mS : GaussianInt) * placement.layout.u + (nS : GaussianInt) *
            placement.layout.v) → ((uEnd = (mE : GaussianInt) * placement.layout.u + (nE :
            GaussianInt) * placement.layout.v) → (((0, 0) ≠ (mR, nR)) → (((0, 0) ≠ (mS, nS)) →
            (((0, 0) ≠ (mE, nE)) → (((mR, nR) ≠ (mS, nS)) → (((mR, nR) ≠ (mE, nE)) → (((mS, nS) ≠
            (mE, nE)) → ((ExactTileInterfaceTriple F (TileTranslation F
            placement.rightNeighborDisplacement) (TileTranslation F uStart)) →
            ((ExactTileInterfaceTriple F (TileTranslation F uEnd) (TileTranslation F
            placement.rightNeighborDisplacement)) → ((TouchingTriple F (TileTranslation F
            placement.rightNeighborDisplacement) (TileTranslation F uStart)) → ((TouchingTriple F
            (TileTranslation F uEnd) (TileTranslation F placement.rightNeighborDisplacement)) →
            (∃ g : BandOrderedGeneralRightInterfaceCertificate norm, g.startCompanion =
            TileTranslation F uStart ∧ g.endCompanion = TileTranslation F uEnd ∧
            g.startData.point ≠ g.endData.point)))))))))))))) → ((((0, 0) : Int × Int) ≠ (0, -1)
            ∧ ((0, 0) : Int × Int) ≠ (-1, -1) ∧ ((0, 0) : Int × Int) ≠ (1, 0) ∧ ((0, -1) : Int ×
            Int) ≠ (-1, -1) ∧ ((0, -1) : Int × Int) ≠ (1, 0) ∧ ((-1, -1) : Int × Int) ≠ (1, 0)) →
            ((((0, 0) : Int × Int) ≠ (0, 1) ∧ ((0, 0) : Int × Int) ≠ (1, 1) ∧ ((0, 0) : Int ×
            Int) ≠ (-1, 0) ∧ ((0, 1) : Int × Int) ≠ (1, 1) ∧ ((0, 1) : Int × Int) ≠ (-1, 0) ∧
            ((1, 1) : Int × Int) ≠ (-1, 0)) → ((BandVectors.1 (q 0) (q 1) = placement.layout.u) →
            ((BandVectors.1 (q 0) (q 2) = placement.layout.v) → ((BandVectors.1 (q 0) (q 3) =
            -placement.layout.u - placement.layout.v) → ((∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (sgn :
            GaussianInt), ∀ (s₁ : Bool), ∀ (s₂ : Bool), ∀ (g :
            BandOrderedGeneralRightInterfaceCertificate norm), (g.startCompanion =
            TileTranslation F (sgn * BandVectors.1 (q 0) (q i.succ))) → ((g.endCompanion =
            TileTranslation F (sgn * BandVectors.1 (q 0) (q j.succ))) → ((g.startData.point ≠
            g.endData.point) → ((ExactTileInterfaceTriple F g.startCompanion (TileTranslation
            (placement.layout.P i s₁) placement.rightNeighborDisplacement)) →
            ((ExactTileInterfaceTriple F g.endCompanion (TileTranslation (placement.layout.P j
            s₂) placement.rightNeighborDisplacement)) → ((FootprintVertices (TileTranslation
            (placement.layout.P i s₁) placement.rightNeighborDisplacement) ⊆ FootprintVertices
            root) → ((FootprintVertices (TileTranslation (placement.layout.P j s₂)
            placement.rightNeighborDisplacement) ⊆ FootprintVertices root) → (rightGeometry i j
            sgn s₁ s₂)))))))) → ((FootprintVertices (TileTranslation (placement.layout.P
            placement.rightFirstSlot placement.firstBoundarySign)
            placement.rightNeighborDisplacement) ⊆ FootprintVertices root) → ((FootprintVertices
            (TileTranslation (placement.layout.P placement.rightSecondSlot
            placement.secondBoundarySign) placement.rightNeighborDisplacement) ⊆
            FootprintVertices root) → ((placement.rightFirstSlot = (2 : Fin (3 : ℕ)) ∧
            placement.rightSecondSlot = (0 : Fin (3 : ℕ)) ∧ placement.rightDirectionSlot = (1 :
            Fin (3 : ℕ))) → (
        let q := bundle.normalizedPresentation
            let occurrence := SubtileOccurrenceInterpretation placement.layout.P
              placement.layout.u placement.layout.v
            let selectedPath := ∃ selectedStart selectedEnd : GaussianInt,
              SimpleGridPathBetween
                (FootprintVertices (occurrence placement.exteriorIndex) ∩
                  FootprintVertices (occurrence placement.centralIndex))
                (FootprintEdges (occurrence placement.exteriorIndex) ∩
                  FootprintEdges (occurrence placement.centralIndex))
                selectedStart selectedEnd ∧
              selectedEdge ∈
                FootprintEdges (occurrence placement.exteriorIndex) ∩
                  FootprintEdges (occurrence placement.centralIndex) ∧
              bundle.normalizedPoint ∈ selectedEdge
            let rightGeometry := fun (i j : Fin 3) (sgn : GaussianInt)
                (firstSign secondSign : Bool) ↦
              let firstCompanion := TileTranslation bundle.normalizedFixed
                (sgn * BandVectors.1 (q 0) (q i.succ))
              let secondCompanion := TileTranslation bundle.normalizedFixed
                (sgn * BandVectors.1 (q 0) (q j.succ))
              let firstPiece := TileTranslation (placement.layout.P i firstSign)
                placement.rightNeighborDisplacement
              let secondPiece := TileTranslation (placement.layout.P j secondSign)
                placement.rightNeighborDisplacement
              ∃ firstBoundaryData : ExactTileInterfaceTriple bundle.normalizedFixed
                  firstCompanion firstPiece,
                ∃ secondBoundaryData : ExactTileInterfaceTriple bundle.normalizedFixed
                    secondCompanion secondPiece,
                  ∃ firstData : ExactTileInterfaceTriple bundle.normalizedRoot
                      bundle.normalizedFixed firstCompanion,
                    ∃ secondData : ExactTileInterfaceTriple bundle.normalizedRoot
                        bundle.normalizedFixed secondCompanion,
                      firstBoundaryData.point = firstData.point ∧
                      secondBoundaryData.point = secondData.point ∧
                      LatticeTile bundle.normalizedRoot ∧
                      LatticeTile bundle.normalizedFixed ∧
                      LatticeTile firstCompanion ∧
                      LatticeTile secondCompanion ∧
                      Disjoint bundle.normalizedRoot.cells firstCompanion.cells ∧
                      Disjoint bundle.normalizedFixed.cells firstCompanion.cells ∧
                      Disjoint bundle.normalizedRoot.cells secondCompanion.cells ∧
                      Disjoint bundle.normalizedFixed.cells secondCompanion.cells ∧
                      Disjoint firstCompanion.cells secondCompanion.cells ∧
                      TouchingTriple bundle.normalizedRoot bundle.normalizedFixed
                        firstCompanion ∧
                      TouchingTriple bundle.normalizedRoot bundle.normalizedFixed
                        secondCompanion ∧
                      firstData.point ≠ secondData.point ∧
                      secondData.point = firstData.otherAB ∧
                      secondData.otherAB = firstData.point ∧
                      selectedPath
            (placement.rightNeighborPositive = true ∧
                  bundle.selectedSlot = placement.rightFirstSlot ∧
                  bundle.selectedSign = true ∧
                  rightGeometry placement.rightFirstSlot placement.rightSecondSlot
                    (-1) true false) ∨
               (placement.rightNeighborPositive = true ∧
                  bundle.selectedSlot = placement.rightSecondSlot ∧
                  bundle.selectedSign = false ∧
                  rightGeometry placement.rightFirstSlot placement.rightSecondSlot
                    (-1) true false) ∨
               (placement.rightNeighborPositive = false ∧
                  bundle.selectedSlot = placement.rightFirstSlot ∧
                  bundle.selectedSign = false ∧
                  rightGeometry placement.rightFirstSlot placement.rightSecondSlot
                    1 false true) ∨
               (placement.rightNeighborPositive = false ∧
                  bundle.selectedSlot = placement.rightSecondSlot ∧
                  bundle.selectedSign = true ∧
                  rightGeometry placement.rightFirstSlot placement.rightSecondSlot
                    1 false true))))))))))))) ) := by
  classical
  intro C D T N h k x bundle placement selectedEdge chosenBoundary q F root norm childInterfaces
      turnOutgoing turnNeg boundaryRecords centeredExactTurn tripleTurnOutgoing
      tripleTurnNegativeNext touchingPlus touchingMinus P u v selectedPath rightGeometry
      canonicalFinish coordinateFactsCpos coordinateFactsCneg period0 period1 period2
      packageGeometry firstBoundarySubset secondBoundarySubset hcycle
  let exactMinus (ell : Fin 3) : ExactTileInterfaceTriple F
      (TileTranslation F (-BandVectors.1 (q 0) (q ell.succ)))
      (TileTranslation F (BandVectors.1 (q 0) (q (ell + 1).succ))) := by
    let E := Classical.choice ((SelectedRowGeometry.thriceExactTurn C D T N h k x bundle
        centeredExactTurn)
      (BandVectors.1 (q ell.succ) (q 0))
      (-BandVectors.1 (q (ell + 1).succ) (q 0))
      (Classical.choice (childInterfaces.1 ell)))
    simpa only [tripleTurnOutgoing, tripleTurnNegativeNext] using E
  let exactPlus (ell : Fin 3) : ExactTileInterfaceTriple F
      (TileTranslation F (BandVectors.1 (q 0) (q ell.succ)))
      (TileTranslation F (-BandVectors.1 (q 0) (q (ell + 1).succ))) := by
    let E := Classical.choice (centeredExactTurn
      (BandVectors.1 (q ell.succ) (q 0))
      (-BandVectors.1 (q (ell + 1).succ) (q 0))
      (Classical.choice (childInterfaces.1 ell)))
    simpa [turnOutgoing, turnNeg] using E
  rcases hcycle with ⟨hi, hj, hk⟩
  have hcyc :
      (placement.rightFirstSlot = 0 ∧ placement.rightSecondSlot = 1 ∧
        placement.rightDirectionSlot = 2) ∨
      (placement.rightFirstSlot = 1 ∧ placement.rightSecondSlot = 2 ∧
        placement.rightDirectionSlot = 0) ∨
      (placement.rightFirstSlot = 2 ∧ placement.rightSecondSlot = 0 ∧
        placement.rightDirectionSlot = 1) := Or.inr (Or.inr ⟨hi, hj, hk⟩)
  have records := boundaryRecords hcyc
  cases hpos : placement.rightNeighborPositive
  · have hR : placement.rightNeighborDisplacement =
        -BandVectors.1 (q 0) (q 2) := SelectedRowGeometry.hRAt1461 C D T N h k x bundle
            placement hk hpos
    rcases records.2 hpos with ⟨⟨R1⟩, ⟨R2⟩⟩
    have eStart : ExactTileInterfaceTriple F
        (TileTranslation F placement.rightNeighborDisplacement)
        (TileTranslation F ((1 : GaussianInt) * BandVectors.1 (q 0) (q 3))) := by
      simpa [hR] using exactMinus 1
    have eEnd : ExactTileInterfaceTriple F
        (TileTranslation F ((1 : GaussianInt) * BandVectors.1 (q 0) (q 1)))
        (TileTranslation F placement.rightNeighborDisplacement) := by
      simpa [hR] using exactPlus 0
    have tStart := SelectedRowGeometry.tStartAt1473 C D T N h k x bundle placement
        touchingMinus hR
    have tEnd := SelectedRowGeometry.tEndAt1477 C D T N h k x bundle placement touchingPlus hR
    rcases canonicalFinish ((1 : GaussianInt) * BandVectors.1 (q 0) (q 3))
        ((1 : GaussianInt) * BandVectors.1 (q 0) (q 1)) 0 (-1) (-1) (-1) 1 0
        (by rw [hR, period1]; simp)
        (by rw [period2]; ring) (by rw [period0]; simp)
        coordinateFactsCpos.1 coordinateFactsCpos.2.1
        coordinateFactsCpos.2.2.1 coordinateFactsCpos.2.2.2.1
        coordinateFactsCpos.2.2.2.2.1 coordinateFactsCpos.2.2.2.2.2
        eStart eEnd tStart tEnd with
      ⟨g, hgs, hge, hneq⟩
    rcases placement.boundary_signs with ⟨hp, _, _⟩ | ⟨hp, hfirst, hsecond⟩
    · rw [hpos] at hp
      cases hp
    · have R1g : ExactTileInterfaceTriple F g.startCompanion
          (TileTranslation (placement.layout.P 2 false)
            placement.rightNeighborDisplacement) := by
        simpa [hgs, hi] using R1
      have R2g : ExactTileInterfaceTriple F g.endCompanion
          (TileTranslation (placement.layout.P 0 true)
            placement.rightNeighborDisplacement) := by
        simpa [hge, hj] using R2
      have hW := SelectedRowGeometry.hWAt1501 C D T N h k x bundle placement
          firstBoundarySubset hi hfirst
      have hX := SelectedRowGeometry.hXAt1505 C D T N h k x bundle placement
          secondBoundarySubset hj hsecond
      have geom := packageGeometry 2 0 1 false true g hgs hge hneq R1g R2g hW hX
      have hgeom := (show
          rightGeometry placement.rightFirstSlot placement.rightSecondSlot 1 false
          true
        from by
          classical
          rw [hi, hj]
          exact geom)
      rcases chosenBoundary with ⟨hs, hsign⟩ |
        ⟨hs, hsign⟩
      · have hs' : bundle.selectedSign = false := by
          exact hsign.trans hfirst
        exact Or.inr (Or.inr (Or.inl ⟨rfl, hs, hs', hgeom⟩))
      · have hs' : bundle.selectedSign = true := by
          exact hsign.trans hsecond
        exact Or.inr (Or.inr (Or.inr ⟨rfl, hs, hs', hgeom⟩))
  · have hR : placement.rightNeighborDisplacement =
        BandVectors.1 (q 0) (q 2) := SelectedRowGeometry.hRAt1522 C D T N h k x bundle
            placement hk hpos
    rcases records.1 hpos with ⟨⟨R1⟩, ⟨R2⟩⟩
    have eStart : ExactTileInterfaceTriple F
        (TileTranslation F placement.rightNeighborDisplacement)
        (TileTranslation F ((-1 : GaussianInt) * BandVectors.1 (q 0) (q 3))) := by
      simpa [hR] using exactPlus 1
    have eEnd : ExactTileInterfaceTriple F
        (TileTranslation F ((-1 : GaussianInt) * BandVectors.1 (q 0) (q 1)))
        (TileTranslation F placement.rightNeighborDisplacement) := by
      simpa [hR] using exactMinus 0
    have tStart := SelectedRowGeometry.tStartAt1534 C D T N h k x bundle placement
        touchingPlus hR
    have tEnd := SelectedRowGeometry.tEndAt1538 C D T N h k x bundle placement touchingMinus hR
    rcases canonicalFinish ((-1 : GaussianInt) * BandVectors.1 (q 0) (q 3))
        ((-1 : GaussianInt) * BandVectors.1 (q 0) (q 1)) 0 1 1 1 (-1) 0
        (by simp [hR, period1])
        (by rw [period2]; ring) (by rw [period0]; simp)
        coordinateFactsCneg.1 coordinateFactsCneg.2.1
        coordinateFactsCneg.2.2.1 coordinateFactsCneg.2.2.2.1
        coordinateFactsCneg.2.2.2.2.1 coordinateFactsCneg.2.2.2.2.2
        eStart eEnd tStart tEnd with
      ⟨g, hgs, hge, hneq⟩
    rcases placement.boundary_signs with ⟨hp, hfirst, hsecond⟩ | ⟨hp, _, _⟩
    · have R1g : ExactTileInterfaceTriple F g.startCompanion
          (TileTranslation (placement.layout.P 2 true)
            placement.rightNeighborDisplacement) := by
        simpa [hgs, hi] using R1
      have R2g : ExactTileInterfaceTriple F g.endCompanion
          (TileTranslation (placement.layout.P 0 false)
            placement.rightNeighborDisplacement) := by
        simpa [hge, hj] using R2
      have hW := SelectedRowGeometry.hWAt1560 C D T N h k x bundle placement
          firstBoundarySubset hi hfirst
      have hX := SelectedRowGeometry.hXAt1564 C D T N h k x bundle placement
          secondBoundarySubset hj hsecond
      have geom := packageGeometry 2 0 (-1) true false g hgs hge hneq R1g R2g hW hX
      have hgeom := (show
          rightGeometry placement.rightFirstSlot placement.rightSecondSlot (-1) true
          false
        from by
          classical
          rw [hi, hj]
          exact geom)
      rcases chosenBoundary with ⟨hs, hsign⟩ |
        ⟨hs, hsign⟩
      · have hs' : bundle.selectedSign = true := by
          exact hsign.trans hfirst
        exact Or.inl ⟨rfl, hs, hs', hgeom⟩
      · have hs' : bundle.selectedSign = false := by
          exact hsign.trans hsecond
        exact Or.inr (Or.inl ⟨rfl, hs, hs', hgeom⟩)
    · rw [hpos] at hp
      cases hp

end SelectedRowConclusions

namespace SelectedRowExactInterfaces

private noncomputable def swapExact (A B D : ProtoTile) (E : ExactTileInterfaceTriple A B D) :
    ExactTileInterfaceTriple B A D :=
  { point := E.point
    otherAB := E.otherAB
    otherBC := E.otherCA
    otherCA := E.otherBC
    pathAB := by simpa [Set.inter_comm] using E.pathAB
    pathBC := by simpa [Set.inter_comm] using E.pathCA
    pathCA := by simpa [Set.inter_comm] using E.pathBC
    unique_common := by
      intro y
      simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
        E.unique_common y }

private noncomputable def cycleExact (A B D : ProtoTile) (E : ExactTileInterfaceTriple A B D) :
    ExactTileInterfaceTriple D A B :=
  { point := E.point
    otherAB := E.otherCA
    otherBC := E.otherAB
    otherCA := E.otherBC
    pathAB := E.pathCA
    pathBC := E.pathAB
    pathCA := E.pathBC
    unique_common := by
      intro y
      simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
        E.unique_common y }

private noncomputable def retargetExactFirst (A A' B D : ProtoTile)
    (hcell : A.cells = A'.cells)
    (hanchor : A.cells = ∅ → A.anchor = A'.anchor)
    (E : ExactTileInterfaceTriple A B D) : ExactTileInterfaceTriple A' B D := by
  have hobs := ProtoTileObservableExtensionality A A' hcell hanchor
  have hedge : FootprintEdges A = FootprintEdges A' := SelectedRowGeometry.hedge A A' hcell
  exact
    { point := E.point
      otherAB := E.otherAB
      otherBC := E.otherBC
      otherCA := E.otherCA
      pathAB := by simpa [hobs.1, hedge] using E.pathAB
      pathBC := E.pathBC
      pathCA := by simpa [hobs.1, hedge] using E.pathCA
      unique_common := by intro y; simpa [hobs.1] using E.unique_common y }

end SelectedRowExactInterfaces

theorem BandOrderedGeneralRightSelectedRowGeometry
    (C D : BandCircle) (T N : ProtoTile) (h k : PartialOdometer)
    (x : GaussianInt)
    (bundle : BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x)
    (placement : BandOrderedGeneralRightPlacement bundle.normalizedPresentation
      bundle.configuration bundle.normalizedCircle bundle.normalizedRoot
      bundle.normalizedFixed bundle.normalizedRootFunction
      bundle.normalizedFixedFunction bundle.normalizedPoint bundle.pieces
      bundle.functions bundle.selectedSlot bundle.selectedSign
      bundle.routedDirection)
    (selectedEdge : Finset GaussianInt)
    (hx : bundle.normalizedPoint ∈ selectedEdge)
    (hedge : selectedEdge ∈
      FootprintEdges
          (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.exteriorIndex) ∩
        FootprintEdges
          (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.centralIndex))
    (row : BandOrderedGeneralSelectedContactRow
      bundle.normalizedPresentation bundle.configuration
      bundle.normalizedCircle bundle.normalizedFixed placement.layout
      placement.exteriorIndex placement.centralIndex) :
    let q := bundle.normalizedPresentation
    let occurrence := SubtileOccurrenceInterpretation placement.layout.P
      placement.layout.u placement.layout.v
    let selectedPath := ∃ selectedStart selectedEnd : GaussianInt,
      SimpleGridPathBetween
        (FootprintVertices (occurrence placement.exteriorIndex) ∩
          FootprintVertices (occurrence placement.centralIndex))
        (FootprintEdges (occurrence placement.exteriorIndex) ∩
          FootprintEdges (occurrence placement.centralIndex))
        selectedStart selectedEnd ∧
      selectedEdge ∈
        FootprintEdges (occurrence placement.exteriorIndex) ∩
          FootprintEdges (occurrence placement.centralIndex) ∧
      bundle.normalizedPoint ∈ selectedEdge
    let rightGeometry := fun (i j : Fin 3) (sgn : GaussianInt)
        (firstSign secondSign : Bool) ↦
      let firstCompanion := TileTranslation bundle.normalizedFixed
        (sgn * BandVectors.1 (q 0) (q i.succ))
      let secondCompanion := TileTranslation bundle.normalizedFixed
        (sgn * BandVectors.1 (q 0) (q j.succ))
      let firstPiece := TileTranslation (placement.layout.P i firstSign)
        placement.rightNeighborDisplacement
      let secondPiece := TileTranslation (placement.layout.P j secondSign)
        placement.rightNeighborDisplacement
      ∃ firstBoundaryData : ExactTileInterfaceTriple bundle.normalizedFixed
          firstCompanion firstPiece,
        ∃ secondBoundaryData : ExactTileInterfaceTriple bundle.normalizedFixed
            secondCompanion secondPiece,
          ∃ firstData : ExactTileInterfaceTriple bundle.normalizedRoot
              bundle.normalizedFixed firstCompanion,
            ∃ secondData : ExactTileInterfaceTriple bundle.normalizedRoot
                bundle.normalizedFixed secondCompanion,
              firstBoundaryData.point = firstData.point ∧
              secondBoundaryData.point = secondData.point ∧
              LatticeTile bundle.normalizedRoot ∧
              LatticeTile bundle.normalizedFixed ∧
              LatticeTile firstCompanion ∧
              LatticeTile secondCompanion ∧
              Disjoint bundle.normalizedRoot.cells firstCompanion.cells ∧
              Disjoint bundle.normalizedFixed.cells firstCompanion.cells ∧
              Disjoint bundle.normalizedRoot.cells secondCompanion.cells ∧
              Disjoint bundle.normalizedFixed.cells secondCompanion.cells ∧
              Disjoint firstCompanion.cells secondCompanion.cells ∧
              TouchingTriple bundle.normalizedRoot bundle.normalizedFixed
                firstCompanion ∧
              TouchingTriple bundle.normalizedRoot bundle.normalizedFixed
                secondCompanion ∧
              firstData.point ≠ secondData.point ∧
              secondData.point = firstData.otherAB ∧
              secondData.otherAB = firstData.point ∧
              selectedPath
    (placement.rightNeighborPositive = true ∧
          bundle.selectedSlot = placement.rightFirstSlot ∧
          bundle.selectedSign = true ∧
          rightGeometry placement.rightFirstSlot placement.rightSecondSlot
            (-1) true false) ∨
       (placement.rightNeighborPositive = true ∧
          bundle.selectedSlot = placement.rightSecondSlot ∧
          bundle.selectedSign = false ∧
          rightGeometry placement.rightFirstSlot placement.rightSecondSlot
            (-1) true false) ∨
       (placement.rightNeighborPositive = false ∧
          bundle.selectedSlot = placement.rightFirstSlot ∧
          bundle.selectedSign = false ∧
          rightGeometry placement.rightFirstSlot placement.rightSecondSlot
            1 false true) ∨
       (placement.rightNeighborPositive = false ∧
          bundle.selectedSlot = placement.rightSecondSlot ∧
          bundle.selectedSign = true ∧
          rightGeometry placement.rightFirstSlot placement.rightSecondSlot
            1 false true) := by
-- BODY
  classical
  have chosenBoundary := placement.selected_boundary_piece
  let q := bundle.normalizedPresentation
  let cfg := bundle.configuration
  let F := bundle.normalizedFixed
  let root := bundle.normalizedRoot
  have edgeVertex := SelectedRowGeometry.edgeVertex
  let norm := SelectedRowNormalization.certificate C D T N h k x bundle placement
  have outer := (BandOrderedGeneralRightInterfaceCertificateExists norm).some
  have childInterfaces := BandOrderedGeneralChildInterfaces q cfg
    bundle.normalizedCircle F placement.layout
      (TileT2QuarterTurn q cfg bundle.normalizedCircle F placement.layout)
  have translatedTouching := TileT3TranslateTouching q cfg
    bundle.normalizedCircle F placement.layout
      (TileT2QuarterTurn q cfg bundle.normalizedCircle F placement.layout)
  have blockCells := BandOrderedGeneralPeriodicBlockCells q cfg
    bundle.normalizedCircle F placement.layout
  have vectorLaws := VectorRecursionLaws q cfg.proper.1
  have turnFlip := vectorLaws.2.2.2.2 cfg.proper
  have turnOutgoing (s : Fin 3) :
      GaussianQuarterTurn (BandVectors.1 (q s.succ) (q 0)) =
        BandVectors.1 (q 0) (q s.succ) := SelectedRowGeometry.turnOutgoing C D T N h k x bundle
            turnFlip s
  have turnNeg (z : GaussianInt) :
      GaussianQuarterTurn (-z) = -GaussianQuarterTurn z := GaussianQuarterTurnProperties.negation z
  have turnThrice := SelectedRowGeometry.turnThrice turnNeg (GaussianQuarterTurnProperties.twice)
  have fixedPositive : 0 < (q 0).1 :=
    (ProperBandCurvatureStructure q cfg.proper).1
  have boundaryRecords := P5635T1RightBoundaryInterfaceRecords
    C D T N h k x bundle placement
  have centeredExactTurn := SelectedRowGeometry.centeredExactTurn C D T N h k x bundle placement
  have twiceExactTurn := SelectedRowGeometry.twiceExactTurn C D T N h k x bundle centeredExactTurn
  have tripleTurnOutgoing (ell : Fin 3) :
      GaussianQuarterTurn (GaussianQuarterTurn
        (GaussianQuarterTurn (BandVectors.1 (q ell.succ) (q 0)))) =
        -BandVectors.1 (q 0) (q ell.succ) := SelectedRowGeometry.tripleTurnOutgoing C D T N h k x
            bundle turnOutgoing turnThrice ell
  have tripleTurnNegativeNext (ell : Fin 3) :
      GaussianQuarterTurn (GaussianQuarterTurn
        (GaussianQuarterTurn (-BandVectors.1 (q (ell + 1).succ) (q 0)))) =
        BandVectors.1 (q 0) (q (ell + 1).succ) := SelectedRowGeometry.tripleTurnNegativeNext C D
            T N h k x bundle turnOutgoing turnNeg turnThrice ell
  have swapExact (A B D : ProtoTile) (E : ExactTileInterfaceTriple A B D) :
      ExactTileInterfaceTriple B A D := SelectedRowExactInterfaces.swapExact A B D E
  have cycleExact (A B D : ProtoTile) (E : ExactTileInterfaceTriple A B D) :
      ExactTileInterfaceTriple D A B := SelectedRowExactInterfaces.cycleExact A B D E
  have retargetExactFirst (A A' B D : ProtoTile)
      (hcell : A.cells = A'.cells)
      (hanchor : A.cells = ∅ → A.anchor = A'.anchor)
      (E : ExactTileInterfaceTriple A B D) : ExactTileInterfaceTriple A' B D :=
          SelectedRowExactInterfaces.retargetExactFirst A A' B D hcell hanchor E
  have touchingRetarget := ObservableTileRetargeting.triple
  have centeredTurnTouching := SelectedRowGeometry.centeredTurnTouching touchingRetarget
      (TileQuarterTurnTranslation.translated) (SelectedRowGeometry.translateObs)
  have exactPlus (ell : Fin 3) : ExactTileInterfaceTriple F
      (TileTranslation F (BandVectors.1 (q 0) (q ell.succ)))
      (TileTranslation F (-BandVectors.1 (q 0) (q (ell + 1).succ))) := by
    let E := Classical.choice (centeredExactTurn
      (BandVectors.1 (q ell.succ) (q 0))
      (-BandVectors.1 (q (ell + 1).succ) (q 0))
      (Classical.choice (childInterfaces.1 ell)))
    simpa [turnOutgoing, turnNeg] using E
  have exactMinus (ell : Fin 3) : ExactTileInterfaceTriple F
      (TileTranslation F (-BandVectors.1 (q 0) (q ell.succ)))
      (TileTranslation F (BandVectors.1 (q 0) (q (ell + 1).succ))) := by
    let E := Classical.choice ((SelectedRowGeometry.thriceExactTurn C D T N h k x bundle
        centeredExactTurn)
      (BandVectors.1 (q ell.succ) (q 0))
      (-BandVectors.1 (q (ell + 1).succ) (q 0))
      (Classical.choice (childInterfaces.1 ell)))
    simpa only [tripleTurnOutgoing, tripleTurnNegativeNext] using E
  have touchingPlus := SelectedRowGeometry.touchingPlus C D T N h k x bundle placement
      translatedTouching turnOutgoing turnNeg centeredTurnTouching
  have touchingMinus := SelectedRowGeometry.touchingMinus C D T N h k x bundle placement
      translatedTouching tripleTurnOutgoing tripleTurnNegativeNext
      (SelectedRowGeometry.thriceTouching centeredTurnTouching (SelectedRowGeometry.twiceTouching
      centeredTurnTouching))
  have indexNe := SelectedRowGeometry.indexNe C D T N h k x bundle placement row
  have originalAllowed := SelectedRowGeometry.originalAllowed C D T N h k x bundle placement
      selectedEdge hedge indexNe
  have modifiedAdjacent : placement.layout.modified.plane.adjacent
      placement.exteriorIndex placement.centralIndex :=
    (placement.layout.modified_adjacency _ _).2 originalAllowed
  let P := placement.layout.P
  let u := placement.layout.u
  let v := placement.layout.v
  have selectedOccurrenceRetarget := P5640T1NonpairedOccurrenceIntersections
    q cfg bundle.normalizedCircle F placement.layout
    placement.exteriorIndex placement.centralIndex originalAllowed
    (SelectedRowGeometry.noPairedOccurrence C D T N h k x bundle placement row)
  let selectedPath : Prop :=
      (∃ selectedStart selectedEnd : GaussianInt,
        SimpleGridPathBetween
          (FootprintVertices
              (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
            FootprintVertices
              (SubtileOccurrenceInterpretation P u v placement.centralIndex))
          (FootprintEdges
              (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
            FootprintEdges
              (SubtileOccurrenceInterpretation P u v placement.centralIndex))
          selectedStart selectedEnd ∧
        selectedEdge ∈
          FootprintEdges
              (SubtileOccurrenceInterpretation P u v placement.exteriorIndex) ∩
            FootprintEdges
              (SubtileOccurrenceInterpretation P u v placement.centralIndex) ∧
        bundle.normalizedPoint ∈ selectedEdge)
  let rightGeometry := fun (i j : Fin 3) (sgn : GaussianInt)
      (firstSign secondSign : Bool) ↦
    let firstCompanion := TileTranslation F
      (sgn * BandVectors.1 (q 0) (q i.succ))
    let secondCompanion := TileTranslation F
      (sgn * BandVectors.1 (q 0) (q j.succ))
    let firstPiece := TileTranslation (placement.layout.P i firstSign)
      placement.rightNeighborDisplacement
    let secondPiece := TileTranslation (placement.layout.P j secondSign)
      placement.rightNeighborDisplacement
    ∃ firstBoundaryData : ExactTileInterfaceTriple F firstCompanion firstPiece,
      ∃ secondBoundaryData : ExactTileInterfaceTriple F secondCompanion secondPiece,
        ∃ firstData : ExactTileInterfaceTriple root F firstCompanion,
          ∃ secondData : ExactTileInterfaceTriple root F secondCompanion,
            firstBoundaryData.point = firstData.point ∧
            secondBoundaryData.point = secondData.point ∧
            LatticeTile root ∧ LatticeTile F ∧ LatticeTile firstCompanion ∧
            LatticeTile secondCompanion ∧ Disjoint root.cells firstCompanion.cells ∧
            Disjoint F.cells firstCompanion.cells ∧
            Disjoint root.cells secondCompanion.cells ∧
            Disjoint F.cells secondCompanion.cells ∧
            Disjoint firstCompanion.cells secondCompanion.cells ∧
            TouchingTriple root F firstCompanion ∧
            TouchingTriple root F secondCompanion ∧
            firstData.point ≠ secondData.point ∧
            secondData.point = firstData.otherAB ∧
            secondData.otherAB = firstData.point ∧ selectedPath
  have canonicalFinish := SelectedRowGeometry.canonicalFinish C D T N h k x bundle placement
      selectedEdge hedge edgeVertex blockCells fixedPositive touchingRetarget
  have coordinateFactsApos := SelectedRowGeometry.coordinateFactsApos
  have coordinateFactsAneg := SelectedRowGeometry.coordinateFactsAneg
  have coordinateFactsBpos := SelectedRowGeometry.coordinateFactsBpos
  have coordinateFactsBneg := SelectedRowGeometry.coordinateFactsBneg
  have coordinateFactsCpos := SelectedRowGeometry.coordinateFactsCpos
  have coordinateFactsCneg := SelectedRowGeometry.coordinateFactsCneg
  have period0 : BandVectors.1 (q 0) (q 1) = placement.layout.u :=
    placement.layout.period_u.symm
  have period1 : BandVectors.1 (q 0) (q 2) = placement.layout.v :=
    placement.layout.period_v.symm
  have period2 := SelectedRowGeometry.period2 C D T N h k x
          bundle placement (SelectedRowGeometry.outgoingSum C D T N h k x bundle turnOutgoing
          (SelectedRowGeometry.turnAdd) (SelectedRowGeometry.incomingSum C D T N h k x bundle))
          period0 period1
  have castTripleOtherABSecond := SelectedRowGeometry.castTripleOtherABSecond
  have castRoundTrip (P : ProtoTile → Type) {a b : ProtoTile}
      (h : a = b) (z : P a) := SelectedRowGeometry.castRoundTrip P (a := a) (b := b) h z
  have packageGeometry := SelectedRowGeometry.packageGeometry C D T N h k x bundle placement
      selectedEdge edgeVertex (SelectedRowGeometry.geometryFields C D T N h k x bundle placement
      selectedEdge edgeVertex (SelectedRowGeometry.originalSelectedPath C D T N h k x bundle
      placement selectedEdge hx hedge (SelectedRowGeometry.modifiedPath C D T N h k x bundle
      placement indexNe (SelectedRowGeometry.modifiedEdgesNonempty C D T N h k x bundle placement
      indexNe modifiedAdjacent)) selectedOccurrenceRetarget))
      (SelectedRowGeometry.castTriplePointSecond) (SelectedRowGeometry.castTriplePointThird)
      (SelectedRowGeometry.castTripleOtherABThird)
  have firstBoundarySubset := SelectedRowGeometry.firstBoundarySubset C D T N h k x bundle placement
  have secondBoundarySubset := SelectedRowGeometry.secondBoundarySubset C D T N h k x bundle
      placement
  rcases placement.right_slots_cyclic with hcycle | hcycle | hcycle
  · have firstCyclicCase := SelectedRowConclusions.firstCyclicCase C D T N h k x bundle placement
      selectedEdge chosenBoundary edgeVertex childInterfaces turnOutgoing turnNeg boundaryRecords
      centeredExactTurn tripleTurnOutgoing tripleTurnNegativeNext touchingPlus touchingMinus
      canonicalFinish coordinateFactsApos coordinateFactsAneg period0 period1 period2
      packageGeometry firstBoundarySubset secondBoundarySubset hcycle
    exact firstCyclicCase
  · have secondCyclicCase := SelectedRowConclusions.secondCyclicCase C D T N h k x bundle
      placement selectedEdge chosenBoundary childInterfaces turnOutgoing turnNeg
      boundaryRecords centeredExactTurn tripleTurnOutgoing tripleTurnNegativeNext touchingPlus
      touchingMinus canonicalFinish coordinateFactsBpos coordinateFactsBneg period0 period1
      period2 packageGeometry firstBoundarySubset secondBoundarySubset hcycle
    exact secondCyclicCase
  · have thirdCyclicCase := SelectedRowConclusions.thirdCyclicCase C D T N h k x bundle placement
      selectedEdge chosenBoundary childInterfaces turnOutgoing turnNeg boundaryRecords
      centeredExactTurn tripleTurnOutgoing tripleTurnNegativeNext touchingPlus touchingMinus
      canonicalFinish coordinateFactsCpos coordinateFactsCneg period0 period1 period2
      packageGeometry firstBoundarySubset secondBoundarySubset hcycle
    exact thirdCyclicCase

end ApollonianSuperharmonic

end
