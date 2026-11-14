/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4564T2ElementaryQuarterTurn
public import LeanPool.ApollonianSuperharmonic.P4564T2FordGeometry
public import LeanPool.ApollonianSuperharmonic.P4564T2DiamondGeometry
public import LeanPool.ApollonianSuperharmonic.P4564T2GeometryPullback
public import LeanPool.ApollonianSuperharmonic.P4564T2FordT6Transport
public import LeanPool.ApollonianSuperharmonic.P4564T2GeneralT6Transport
public import LeanPool.ApollonianSuperharmonic.P4564T2DiamondOrderExclusion
public import LeanPool.ApollonianSuperharmonic.TileT2QuarterTurn
public import LeanPool.ApollonianSuperharmonic.TileT3TranslateTouching
public import LeanPool.ApollonianSuperharmonic.TileT4ParentTranslateTouching
public import LeanPool.ApollonianSuperharmonic.TileT5ParentTouching
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayout
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryT3T5Covariance
public import LeanPool.ApollonianSuperharmonic.BandRegimeClassification
public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public import LeanPool.ApollonianSuperharmonic.TileCellComplement
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.TileArea

-- [TABLET NODE: BandTileSimultaneousInduction]

/-!
# BandTileSimultaneousInduction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

private def tileInductionConclusion (q : Fin 4 → CircleCoordinates) (T : ProtoTile)
    (m : ℕ) : Prop :=
  LatticeTile T ∧ TileArea T = m ∧
  (∀ (S : Fin 3 → Bool → ProtoTile),
    (∀ i s, BandSubtileOccurrence q T i s (S i s)) →
    (∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (S i s).cells) →
    ∀ i s, LatticeTile (TileCellComplement T (S i s)) ∧
      TileTouching (TileCellComplement T (S i s)) (S i s)) ∧
  QuarterTurnSymmetric T ∧
  (1 < (q 0).1 → ∀ i : Fin 3,
    TouchingTriple T
      (TileTranslation T (BandVectors.1 (q i.succ) (q 0)))
      (TileTranslation T
        (-BandVectors.1 (q ((i + 1).succ)) (q 0)))) ∧
  (1 < (q 0).1 → ∀ (i : Fin 3) (U : ProtoTile),
    BandPrototile (q i.succ) U →
    TileCentroid U - TileCentroid T = (1 / 2 : Real) •
      (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
        GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
    TouchingTriple T
      (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) U) ∧
  (∀ (i : Fin 3) (U V : ProtoTile),
    BandPrototile (q i.succ) U →
    BandPrototile (q ((i + 1).succ)) V →
    TileCentroid U - TileCentroid T = (1 / 2 : Real) •
      (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
        GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
    TileCentroid V - TileCentroid T = (1 / 2 : Real) •
      (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
        GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ)))) →
    TouchingTriple T U V) ∧
  (∀ (r : Fin 4 → CircleCoordinates), ProperBandQuadruple r →
    r 0 = q 1 → r 2 = q 2 → r 3 = q 3 →
    (q 2).1 ≤ (q 1).1 → (q 3).1 ≤ (q 2).1 →
    1 < (q 2).1 →
    ∀ (P Q S : Fin 3 → Bool → ProtoTile),
    (∀ i s, BandSubtileOccurrence q T i s (P i s)) →
    (∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (P i s).cells) →
    (∀ i s, BandSubtileOccurrence r (P 0 true) i s (Q i s)) →
    (∀ x, x ∈ (P 0 true).cells ↔ ∃ i s, x ∈ (Q i s).cells) →
    (∀ i s, BandSubtileOccurrence r (P 0 false) i s (S i s)) →
    (∀ x, x ∈ (P 0 false).cells ↔ ∃ i s, x ∈ (S i s).cells) →
    (let u := BandVectors.1 (q 0) (q 1)
     let v := BandVectors.1 (q 0) (q 2)
     (∀ a b : PeriodicSubtileIndex, a ≠ b →
       ((FootprintEdges (SubtileOccurrenceInterpretation P u v a) ∩
           FootprintEdges
             (SubtileOccurrenceInterpretation P u v b)).Nonempty →
         AllowedSubtileIncidence a b) ∧
       (¬ AllowedSubtileIncidence a b →
         FootprintVertices (SubtileOccurrenceInterpretation P u v a) ∩
             FootprintVertices
               (SubtileOccurrenceInterpretation P u v b) = ∅ ∨
           (FootprintVertices
                (SubtileOccurrenceInterpretation P u v a) ∩
              FootprintVertices
                (SubtileOccurrenceInterpretation P u v b)).Subsingleton)) ∧
     FootprintVertices (P 0 true) ∩ FootprintVertices (P 1 true) ⊆
       FootprintVertices (Q 1 true) ∩ FootprintVertices (P 1 true) ∧
     FootprintVertices (P 0 true) ∩ FootprintVertices (P 0 false) ⊆
       (FootprintVertices (Q 1 true) ∩ FootprintVertices (S 2 false)) ∪
         FootprintVertices (Q 0 false) ∪
         (FootprintVertices (Q 2 true) ∩
           FootprintVertices (S 1 false))))

private def tileInductionHypothesis (n : ℕ) : Prop :=
  ∀ m < n, ∀ (q : Fin 4 → CircleCoordinates), ProperBandQuadruple q →
    ∀ (T : ProtoTile), BandPrototile (q 0) T → Int.toNat (q 0).1 = m →
      tileInductionConclusion q T m

namespace TileInductionGeometry

private theorem smallT1 :
    (by
      classical
      exact
        ∀ (n : ℕ), tileInductionHypothesis n →
                                                                          (∀ (p : Fin 4 →
                                                                          CircleCoordinates), ∀
                                                                          (U : ProtoTile), ∀ (S :
                                                                          Fin 3 → Bool →
                                                                          ProtoTile),
                                                                          ProperBandQuadruple p →
                                                                          BandPrototile (p 0) U →
                                                                          (∀ i, ∀ s,
                                                                          BandSubtileOccurrence p
                                                                          U i s (S i s)) → (∀ x,
                                                                          x ∈ U.cells ↔ ∃ i s, x
                                                                          ∈ (S i s).cells) →
                                                                          Int.toNat (p 0).1 < n →
                                                                          LatticeTile U ∧
                                                                          TileArea U = Int.toNat
                                                                          (p 0).1 ∧ ∀ i, ∀ s,
                                                                          LatticeTile
                                                                          (TileCellComplement U
                                                                          (S i s)) ∧ TileTouching
                                                                          (TileCellComplement U
                                                                          (S i s)) (S i s)) ) := by
  classical
  intro n ih p U S hp hU hS hcover hlt
  have h := ih _ hlt p hp U hU rfl
  exact ⟨h.1, h.2.1, h.2.2.1 S hS hcover⟩

private theorem smallT2 :
    (by
      classical
      exact
        ∀ (n : ℕ), tileInductionHypothesis n →
                                                                          (∀ (D :
                                                                          CircleCoordinates), ∀
                                                                          (U : ProtoTile),
                                                                          BandPrototile D U →
                                                                          Int.toNat D.1 < n →
                                                                          QuarterTurnSymmetric U)
                                                                          ) := by
  classical
  intro n ih D U hU hlt
  cases hU with
  | line w x hw =>
    exact (P4564T2ElementaryQuarterTurn x x).1
  | unit z x anchor =>
    exact (P4564T2ElementaryQuarterTurn x anchor).2
  | @decompose p hp S U hS hcells hfoot hcent =>
    exact (ih _ hlt p hp U
      (BandPrototile.decompose hp hS hcells hfoot hcent) rfl).2.2.2.1

private theorem smallT4 :
    (by
      classical
      exact
        ∀ (n : ℕ), tileInductionHypothesis n →
                                                                          (∀ (p : Fin 4 →
                                                                          CircleCoordinates), ∀
                                                                          (U : ProtoTile), ∀ (V :
                                                                          ProtoTile),
                                                                          ProperBandQuadruple p →
                                                                          BandPrototile (p 0) U →
                                                                          Int.toNat (p 0).1 < n →
                                                                          1 < (p 0).1 → ∀ i : Fin
                                                                          3, BandPrototile (p
                                                                          i.succ) V →
                                                                          TileCentroid V -
                                                                          TileCentroid U = (1 / 2
                                                                          : Real) •
                                                                          (GaussianRealPoint
                                                                          (BandVectors.1 (p
                                                                          i.succ) (p 0)) +
                                                                          GaussianRealPoint
                                                                          (BandVectors.1 (p 0) (p
                                                                          i.succ))) →
                                                                          TouchingTriple U
                                                                          (TileTranslation U
                                                                          (BandVectors.1 (p
                                                                          i.succ) (p 0))) V) ) := by
  classical
  intro n ih p U V hp hU hlt hc i hV hcent
  exact (ih _ hlt p hp U hU rfl).2.2.2.2.2.1 hc i V hV hcent

private theorem smallT5 :
    (by
      classical
      exact
        ∀ (n : ℕ), tileInductionHypothesis n →
                                                                          (∀ (p : Fin 4 →
                                                                          CircleCoordinates), ∀
                                                                          (U : ProtoTile), ∀ (V :
                                                                          ProtoTile), ∀ (W :
                                                                          ProtoTile),
                                                                          ProperBandQuadruple p →
                                                                          BandPrototile (p 0) U →
                                                                          Int.toNat (p 0).1 < n →
                                                                          ∀ i : Fin 3,
                                                                          BandPrototile (p
                                                                          i.succ) V →
                                                                          BandPrototile (p ((i +
                                                                          1).succ)) W →
                                                                          TileCentroid V -
                                                                          TileCentroid U = (1 / 2
                                                                          : Real) •
                                                                          (GaussianRealPoint
                                                                          (BandVectors.1 (p
                                                                          i.succ) (p 0)) +
                                                                          GaussianRealPoint
                                                                          (BandVectors.1 (p 0) (p
                                                                          i.succ))) →
                                                                          TileCentroid W -
                                                                          TileCentroid U = (1 / 2
                                                                          : Real) •
                                                                          (GaussianRealPoint
                                                                          (BandVectors.1 (p ((i +
                                                                          1).succ)) (p 0)) -
                                                                          GaussianRealPoint
                                                                          (BandVectors.1 (p 0) (p
                                                                          ((i + 1).succ)))) →
                                                                          TouchingTriple U V W) )
                                                                          := by
  classical
  intro n ih p U V W hp hU hlt i hV hW hcV hcW
  exact (ih _ hlt p hp U hU rfl).2.2.2.2.2.2.1 i V W hV hW hcV hcW

private theorem hqa :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (a : Fin (3 : ℕ)), ∀ (raw
            : BandPackingSymmetry), (
        let q' := BandPackingSymmetryQuadrupleAction raw ![q (0 : Fin (4 : ℕ)), q a.succ, q (a +
            (1 : Fin (3 : ℕ))).succ, q (a + (2 : Fin (3 : ℕ))).succ]; Xor (∃ (P :
            FordFareyParameter), (1 : ℕ) < P.q ∧ q' = FordRecursiveQuadruple P) (Xor (∃ (K :
            DiamondParameter), (1 : ℕ) < K.1 ∧ q' = DiamondRecursiveQuadruple K) (Nonempty
            (BandOrderedGeneralConfiguration q')))) → (
        let qa : Fin 4 → CircleCoordinates :=
          ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
        ProperBandQuadruple qa)) ) := by
  classical
  intro q hq a raw regimes qa
  fin_cases a
  · have heq : qa = q := by funext i; fin_cases i <;> rfl
    exact heq.symm ▸ hq
  · refine ⟨SemiProperQuadruple.rotate hq.1, ?_⟩
    intro i
    fin_cases i
    · exact hq.2 1
    · exact hq.2 2
    · exact hq.2 0
  · refine ⟨SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1), ?_⟩
    intro i
    fin_cases i
    · exact hq.2 2
    · exact hq.2 0
    · exact hq.2 1

private theorem hregimes :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (a : Fin (3 : ℕ)), ∀ (raw : BandPackingSymmetry), (
        let q' := BandPackingSymmetryQuadrupleAction raw ![q (0 : Fin (4 : ℕ)), q a.succ, q (a +
            (1 : Fin (3 : ℕ))).succ, q (a + (2 : Fin (3 : ℕ))).succ]; Xor (∃ (P :
            FordFareyParameter), (1 : ℕ) < P.q ∧ q' = FordRecursiveQuadruple P) (Xor (∃ (K :
            DiamondParameter), (1 : ℕ) < K.1 ∧ q' = DiamondRecursiveQuadruple K) (Nonempty
            (BandOrderedGeneralConfiguration q')))) → (
        let qa : Fin 4 → CircleCoordinates :=
          ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
        ∀ (g : BandPackingSymmetry), (∀ (p : Fin (4 : ℕ) → CircleCoordinates),
            BandPackingSymmetryQuadrupleAction g p = BandPackingSymmetryQuadrupleAction raw p) → (
        let qg := BandPackingSymmetryQuadrupleAction g qa
        Xor (∃ F : FordFareyParameter, 1 < F.q ∧ qg = FordRecursiveQuadruple F) (Xor (∃ K :
            DiamondParameter, 1 < K.1 ∧ qg = DiamondRecursiveQuadruple K) (Nonempty
            (BandOrderedGeneralConfiguration qg))))) ) := by
  classical
  intro q a raw regimes qa g htuple qg
  simpa only [qg, htuple] using regimes

private theorem normalized :
    (by
      classical
      exact
        ∀ (n : ℕ), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (T :
            ProtoTile), (BandPrototile (q (0 : Fin (4 : ℕ))) T) → ((∀ (p : Fin 4 →
            CircleCoordinates), ∀ (U : ProtoTile), ∀ (S : Fin 3 → Bool → ProtoTile),
            ProperBandQuadruple p → BandPrototile (p 0) U → (∀ i, ∀ s, BandSubtileOccurrence p U
            i s (S i s)) → (∀ x, x ∈ U.cells ↔ ∃ i s, x ∈ (S i s).cells) → Int.toNat (p 0).1 < n
            → LatticeTile U ∧ TileArea U = Int.toNat (p 0).1 ∧ ∀ i, ∀ s, LatticeTile
            (TileCellComplement U (S i s)) ∧ TileTouching (TileCellComplement U (S i s)) (S i s))
            → ((∀ (D : CircleCoordinates), ∀ (U : ProtoTile), BandPrototile D U → Int.toNat D.1 <
            n → QuarterTurnSymmetric U) → ((∀ (p : Fin 4 → CircleCoordinates), ∀ (U : ProtoTile),
            ∀ (V : ProtoTile), ProperBandQuadruple p → BandPrototile (p 0) U → Int.toNat (p 0).1
            < n → 1 < (p 0).1 → ∀ i : Fin 3, BandPrototile (p i.succ) V → TileCentroid V -
            TileCentroid U = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (p i.succ) (p 0))
            + GaussianRealPoint (BandVectors.1 (p 0) (p i.succ))) → TouchingTriple U
            (TileTranslation U (BandVectors.1 (p i.succ) (p 0))) V) → ((∀ (p : Fin 4 →
            CircleCoordinates), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (W : ProtoTile),
            ProperBandQuadruple p → BandPrototile (p 0) U → Int.toNat (p 0).1 < n → ∀ i : Fin 3,
            BandPrototile (p i.succ) V → BandPrototile (p ((i + 1).succ)) W → TileCentroid V -
            TileCentroid U = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (p i.succ) (p 0))
            + GaussianRealPoint (BandVectors.1 (p 0) (p i.succ))) → TileCentroid W - TileCentroid
            U = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (p ((i + 1).succ)) (p 0)) -
            GaussianRealPoint (BandVectors.1 (p 0) (p ((i + 1).succ)))) → TouchingTriple U V W) →
            (∀ (a : Fin (3 : ℕ)),
        let qa : Fin 4 → CircleCoordinates :=
          ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
        ∀ (g : BandPackingSymmetry), (BandPackingSymmetryScopedPhase g qa false) → ((∀ (r : Fin
            (4 : ℕ) → CircleCoordinates), ProperBandQuadruple r → r (0 : Fin (4 : ℕ)) = qa (1 :
            Fin (4 : ℕ)) → r (2 : Fin (4 : ℕ)) = qa (2 : Fin (4 : ℕ)) → r (3 : Fin (4 : ℕ)) = qa
            (3 : Fin (4 : ℕ)) → BandPackingSymmetryScopedPhase g r false) → (
        let qg := BandPackingSymmetryQuadrupleAction g qa
        let Tg := BandPackingSymmetryTileAction g T
        (BandPrototile (qg 0) Tg) → ((Int.toNat (qg 0).1 = n) → ((Xor (∃ F : FordFareyParameter,
            1 < F.q ∧ qg = FordRecursiveQuadruple F) (Xor (∃ K : DiamondParameter, 1 < K.1 ∧ qg =
            DiamondRecursiveQuadruple K) (Nonempty (BandOrderedGeneralConfiguration qg)))) →
            ((LatticeTile Tg ∧ TileArea Tg = Int.toNat (qg 0).1 ∧
          (∀ (S : Fin 3 → Bool → ProtoTile), (∀ i, ∀ s, BandSubtileOccurrence qg Tg i s (S i s)) →
            (∀ x, x ∈ Tg.cells ↔ ∃ i s, x ∈ (S i s).cells) →
            ∀ i, ∀ s, LatticeTile (TileCellComplement Tg (S i s)) ∧
              TileTouching (TileCellComplement Tg (S i s)) (S i s)) ∧
          QuarterTurnSymmetric Tg ∧
          (1 < (qg 0).1 → ∀ i : Fin 3,
            TouchingTriple Tg
              (TileTranslation Tg (BandVectors.1 (qg i.succ) (qg 0)))
              (TileTranslation Tg
                (-BandVectors.1 (qg ((i + 1).succ)) (qg 0)))) ∧
          (1 < (qg 0).1 → ∀ (i : Fin 3), ∀ (U : ProtoTile), BandPrototile (qg i.succ) U →
            TileCentroid U - TileCentroid Tg = (1 / 2 : Real) •
              (GaussianRealPoint (BandVectors.1 (qg i.succ) (qg 0)) +
                GaussianRealPoint (BandVectors.1 (qg 0) (qg i.succ))) →
            TouchingTriple Tg
              (TileTranslation Tg (BandVectors.1 (qg i.succ) (qg 0))) U) ∧
          (∀ (i : Fin 3), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (qg i.succ) U →
            BandPrototile (qg ((i + 1).succ)) V →
            TileCentroid U - TileCentroid Tg = (1 / 2 : Real) •
              (GaussianRealPoint (BandVectors.1 (qg i.succ) (qg 0)) +
                GaussianRealPoint (BandVectors.1 (qg 0) (qg i.succ))) →
            TileCentroid V - TileCentroid Tg = (1 / 2 : Real) •
              (GaussianRealPoint (BandVectors.1 (qg ((i + 1).succ)) (qg 0)) -
                GaussianRealPoint (BandVectors.1 (qg 0) (qg ((i + 1).succ)))) →
            TouchingTriple Tg U V)) ∧
          (∀ (r : Fin 4 → CircleCoordinates), ProperBandQuadruple r →
          r 0 = q 1 → r 2 = q 2 → r 3 = q 3 →
          (q 2).1 ≤ (q 1).1 → (q 3).1 ≤ (q 2).1 →
          1 < (q 2).1 →
          ∀ (P : Fin 3 → Bool → ProtoTile), ∀ (Q : Fin 3 → Bool → ProtoTile), ∀ (S : Fin 3 → Bool
              → ProtoTile), (∀ i, ∀ s, BandSubtileOccurrence q T i s (P i s)) →
          (∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (P i s).cells) →
          (∀ i, ∀ s, BandSubtileOccurrence r (P 0 true) i s (Q i s)) →
          (∀ x, x ∈ (P 0 true).cells ↔ ∃ i s, x ∈ (Q i s).cells) →
          (∀ i, ∀ s, BandSubtileOccurrence r (P 0 false) i s (S i s)) →
          (∀ x, x ∈ (P 0 false).cells ↔ ∃ i s, x ∈ (S i s).cells) →
          (
        let u := BandVectors.1 (q 0) (q 1)
           let v := BandVectors.1 (q 0) (q 2)
           (∀ a b : PeriodicSubtileIndex, a ≠ b →
             ((FootprintEdges (SubtileOccurrenceInterpretation P u v a) ∩
                 FootprintEdges
                   (SubtileOccurrenceInterpretation P u v b)).Nonempty →
               AllowedSubtileIncidence a b) ∧
             (¬ AllowedSubtileIncidence a b →
               FootprintVertices (SubtileOccurrenceInterpretation P u v a) ∩
                   FootprintVertices
                     (SubtileOccurrenceInterpretation P u v b) = ∅ ∨
                 (FootprintVertices
                      (SubtileOccurrenceInterpretation P u v a) ∩
                    FootprintVertices
                      (SubtileOccurrenceInterpretation P u v b)).Subsingleton)) ∧
           FootprintVertices (P 0 true) ∩ FootprintVertices (P 1 true) ⊆
             FootprintVertices (Q 1 true) ∩ FootprintVertices (P 1 true) ∧
           FootprintVertices (P 0 true) ∩ FootprintVertices (P 0 false) ⊆
             (FootprintVertices (Q 1 true) ∩ FootprintVertices (S 2 false)) ∪
               FootprintVertices (Q 0 false) ∪
               (FootprintVertices (Q 2 true) ∩
                 FootprintVertices (S 1 false))))))))))))))) ) := by
  classical
  intro n q hq T hT smallT1 smallT2 smallT4 smallT5 a qa g hphase hpred qg Tg hTg hng hregimes
  rcases hregimes with ⟨hford, _⟩ | ⟨hother, _⟩
  · obtain ⟨F, hF, heq⟩ := hford
    refine ⟨?_, P4564T2FordT6Transport q hq T hT a g F hF heq⟩
    have h := P4564T2FordGeometry F hF Tg (heq ▸ hTg)
    simpa only [← heq] using h
  · rcases hother with ⟨hdiamond, _⟩ | ⟨hgeneral, _⟩
    · obtain ⟨K, hK, heq⟩ := hdiamond
      refine ⟨?_, ?_⟩
      · have h := P4564T2DiamondGeometry K hK Tg (heq ▸ hTg)
        simpa only [← heq] using h
      · intro r hr hr0 hr2 hr3 h12 h23 hlarge
        have hle := P4564T2DiamondOrderExclusion q a g K heq h12 h23
        omega
    · obtain ⟨cfg⟩ := hgeneral
      have hpositive : 0 < (qg 0).1 := lt_trans (by norm_num) cfg.childLarge
      let Cg : BandCircle :=
        ⟨⟨qg 0, Or.inl hpositive, ⟨qg, cfg.proper.1, 0, rfl⟩⟩, hpositive⟩
      obtain ⟨cert⟩ := BandOrderedGeneralLayout qg cfg Cg rfl Tg hTg
        (by
          intro p U S hp hU hS hcover hlt
          exact smallT1 p U S hp hU hS hcover (by simpa only [hng] using hlt))
        (by
          intro D U hU hlt
          exact smallT2 D U hU (by simpa only [hng] using hlt))
        (by
          intro p U V hp hU hlt hc i hV hcent
          exact smallT4 p U V hp hU (by simpa only [hng] using hlt)
            hc i hV hcent)
        (by
          intro p U V W hp hU hlt i hV hW hcV hcW
          exact smallT5 p U V W hp hU (by simpa only [hng] using hlt)
            i hV hW hcV hcW)
      have hT1 := TileT1DiskArea qg cfg Cg Tg hTg cert
      have hT2 := TileT2QuarterTurn qg cfg Cg Tg cert
      refine ⟨⟨hT1.1, hT1.2.1, ?_, hT2, ?_, ?_, ?_⟩, ?_⟩
      · intro S hS _ i s
        have hA := hS i s
        have hB := cert.outer_occurrence i s
        have hc : TileCentroid (S i s) = TileCentroid (cert.P i s) :=
          sub_left_injective (hA.2.2.trans hB.2.2.symm)
        obtain ⟨hcells, hanchor⟩ :=
          BandPrototileCentroidUnique _ _ _ hA.1 hB.1 hc
        have hcomp : TileCellComplement Tg (S i s) =
            TileCellComplement Tg (cert.P i s) := by
          simp only [TileCellComplement, hcells]
        obtain ⟨hdisk, htouch⟩ := hT1.2.2 i s
        refine ⟨hcomp.symm ▸ hdisk, ?_⟩
        rw [hcomp]
        by_cases hempty : (S i s).cells = ∅
        · have heq : S i s = cert.P i s := by
            have ha := hanchor hempty
            cases hSi : S i s
            cases hPi : cert.P i s
            simp only [hSi, hPi] at hcells ha
            cases hcells
            cases ha
            rfl
          simpa only [heq] using htouch
        · have obs := ProtoTileObservableExtensionality _ _ hcells hanchor
          have hnonempty : (cert.P i s).cells ≠ ∅ := by rwa [← hcells]
          simpa only [TileTouching, hcells, obs.2.1, obs.2.2.1,
            hnonempty, false_and, or_false] using htouch
      · intro _ i
        exact TileT3TranslateTouching qg cfg Cg Tg cert hT2 i
      · intro _ i U hU hcent
        exact TileT4ParentTranslateTouching qg cfg Cg Tg U cert hT2 i hU hcent
      · intro i U V hU hV hcU hcV
        exact TileT5ParentTouching qg cfg Cg Tg U V cert hT2 i hU hV hcU hcV
      · exact P4564T2GeneralT6Transport q hq T hT a g hphase hpred cfg Cg cert

private theorem parentQuarter :
    (by
      classical
      exact
        ∀ (n : ℕ), ∀ (q : Fin 4 → CircleCoordinates), ((q (0 : Fin (4 : ℕ))).1.toNat = n) → ((∀
            (D : CircleCoordinates), ∀ (U : ProtoTile), BandPrototile D U → Int.toNat D.1 < n →
            QuarterTurnSymmetric U) → (∀ (a : Fin (3 : ℕ)),
        let qa : Fin 4 → CircleCoordinates :=
          ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
        (ProperBandQuadruple qa) → (∀ (i : Fin 3), ∀ (U : ProtoTile), BandPrototile (qa i.succ) U
            → QuarterTurnSymmetric U))) ) := by
  classical
  intro n q hn smallT2 a qa hqa i U hU
  apply smallT2 (qa i.succ) U hU
  rw [← hn]
  exact (Int.toNat_lt_toNat (ProperBandCurvatureStructure qa hqa).1).mpr (hqa.2 i)

private theorem parentIndex :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (a : Fin (3 : ℕ)),
        let qa : Fin 4 → CircleCoordinates :=
          ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
        ∀ i : Fin 3, qa i.succ = q (a + i).succ ) := by
  classical
  intro q a qa i
  fin_cases i <;> simp [qa]

private theorem cyclicIndices :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (a : Fin (3 : ℕ)),
        let qa : Fin 4 → CircleCoordinates :=
          ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
        (∀ i : Fin 3, qa i.succ = q (a + i).succ) → (∀ i : Fin 3, qa (i - a).succ = q i.succ ∧ qa
            ((i - a + 1).succ) = q ((i + 1).succ)) ) := by
  classical
  intro q a qa parentIndex i
  constructor
  · simpa only [add_sub_cancel] using parentIndex (i - a)
  · simpa only [← add_assoc, add_sub_cancel] using parentIndex (i - a + 1)

end TileInductionGeometry

theorem BandTileSimultaneousInduction (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) (T : ProtoTile)
    (hT : BandPrototile (q 0) T) :
    LatticeTile T ∧ TileArea T = Int.toNat (q 0).1 ∧
    (∀ (S : Fin 3 → Bool → ProtoTile),
      (∀ i s, BandSubtileOccurrence q T i s (S i s)) →
      (∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (S i s).cells) →
      ∀ i s, LatticeTile (TileCellComplement T (S i s)) ∧
        TileTouching (TileCellComplement T (S i s)) (S i s)) ∧
    QuarterTurnSymmetric T ∧
    (1 < (q 0).1 → ∀ i : Fin 3,
      TouchingTriple T
        (TileTranslation T (BandVectors.1 (q i.succ) (q 0)))
        (TileTranslation T
          (-BandVectors.1 (q ((i + 1).succ)) (q 0)))) ∧
    (1 < (q 0).1 → ∀ (i : Fin 3) (U : ProtoTile),
      BandPrototile (q i.succ) U →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      TouchingTriple T
        (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) U) ∧
    (∀ (i : Fin 3) (U V : ProtoTile),
      BandPrototile (q i.succ) U →
      BandPrototile (q ((i + 1).succ)) V →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      TileCentroid V - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
          GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ)))) →
      TouchingTriple T U V) ∧
    (∀ (r : Fin 4 → CircleCoordinates), ProperBandQuadruple r →
      r 0 = q 1 → r 2 = q 2 → r 3 = q 3 →
      (q 2).1 ≤ (q 1).1 → (q 3).1 ≤ (q 2).1 →
      1 < (q 2).1 →
      ∀ (P Q S : Fin 3 → Bool → ProtoTile),
      (∀ i s, BandSubtileOccurrence q T i s (P i s)) →
      (∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (P i s).cells) →
      (∀ i s, BandSubtileOccurrence r (P 0 true) i s (Q i s)) →
      (∀ x, x ∈ (P 0 true).cells ↔ ∃ i s, x ∈ (Q i s).cells) →
      (∀ i s, BandSubtileOccurrence r (P 0 false) i s (S i s)) →
      (∀ x, x ∈ (P 0 false).cells ↔ ∃ i s, x ∈ (S i s).cells) →
      (let u := BandVectors.1 (q 0) (q 1)
       let v := BandVectors.1 (q 0) (q 2)
       (∀ a b : PeriodicSubtileIndex, a ≠ b →
         ((FootprintEdges (SubtileOccurrenceInterpretation P u v a) ∩
             FootprintEdges
               (SubtileOccurrenceInterpretation P u v b)).Nonempty →
           AllowedSubtileIncidence a b) ∧
         (¬ AllowedSubtileIncidence a b →
           FootprintVertices (SubtileOccurrenceInterpretation P u v a) ∩
               FootprintVertices
                 (SubtileOccurrenceInterpretation P u v b) = ∅ ∨
             (FootprintVertices
                  (SubtileOccurrenceInterpretation P u v a) ∩
                FootprintVertices
                  (SubtileOccurrenceInterpretation P u v b)).Subsingleton)) ∧
       FootprintVertices (P 0 true) ∩ FootprintVertices (P 1 true) ⊆
         FootprintVertices (Q 1 true) ∩ FootprintVertices (P 1 true) ∧
       FootprintVertices (P 0 true) ∩ FootprintVertices (P 0 false) ⊆
         (FootprintVertices (Q 1 true) ∩ FootprintVertices (S 2 false)) ∪
           FootprintVertices (Q 0 false) ∪
           (FootprintVertices (Q 2 true) ∩
             FootprintVertices (S 1 false)))) := by
-- BODY
  classical
  generalize hn : Int.toNat (q 0).1 = n
  induction n using Nat.strong_induction_on generalizing q T with
  | h n ih =>
    have smallT1 : ∀ (p : Fin 4 → CircleCoordinates) (U : ProtoTile)
        (S : Fin 3 → Bool → ProtoTile), ProperBandQuadruple p →
        BandPrototile (p 0) U →
        (∀ i s, BandSubtileOccurrence p U i s (S i s)) →
        (∀ x, x ∈ U.cells ↔ ∃ i s, x ∈ (S i s).cells) →
        Int.toNat (p 0).1 < n →
        LatticeTile U ∧ TileArea U = Int.toNat (p 0).1 ∧
          ∀ i s, LatticeTile (TileCellComplement U (S i s)) ∧
            TileTouching (TileCellComplement U (S i s)) (S i s) := TileInductionGeometry.smallT1
                n ih
    have smallT2 : ∀ (D : CircleCoordinates) (U : ProtoTile),
        BandPrototile D U → Int.toNat D.1 < n →
        QuarterTurnSymmetric U := TileInductionGeometry.smallT2 n ih
    have smallT4 : ∀ (p : Fin 4 → CircleCoordinates)
        (U V : ProtoTile), ProperBandQuadruple p →
        BandPrototile (p 0) U → Int.toNat (p 0).1 < n →
        1 < (p 0).1 → ∀ i : Fin 3, BandPrototile (p i.succ) V →
        TileCentroid V - TileCentroid U = (1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 (p i.succ) (p 0)) +
            GaussianRealPoint (BandVectors.1 (p 0) (p i.succ))) →
        TouchingTriple U
          (TileTranslation U (BandVectors.1 (p i.succ) (p 0))) V := TileInductionGeometry.smallT4
              n ih
    have smallT5 : ∀ (p : Fin 4 → CircleCoordinates)
        (U V W : ProtoTile), ProperBandQuadruple p →
        BandPrototile (p 0) U → Int.toNat (p 0).1 < n →
        ∀ i : Fin 3, BandPrototile (p i.succ) V →
        BandPrototile (p ((i + 1).succ)) W →
        TileCentroid V - TileCentroid U = (1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 (p i.succ) (p 0)) +
            GaussianRealPoint (BandVectors.1 (p 0) (p i.succ))) →
        TileCentroid W - TileCentroid U = (1 / 2 : Real) •
          (GaussianRealPoint (BandVectors.1 (p ((i + 1).succ)) (p 0)) -
            GaussianRealPoint (BandVectors.1 (p 0) (p ((i + 1).succ)))) →
        TouchingTriple U V W := TileInductionGeometry.smallT5 n ih
    obtain ⟨a, raw, regimes⟩ := BandRegimeClassification q hq
    let qa : Fin 4 → CircleCoordinates :=
      ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
    have hqa : ProperBandQuadruple qa := TileInductionGeometry.hqa q hq a raw regimes
    obtain ⟨negative, hrawphase, hrawpred, hrawnext, hcentralCircle,
      hcentralParity, hcentralTuple, hcentralVector, g, hchoice, hcircle,
      hparity, htuple, hphase, hpred, hnext⟩ :=
      BandPackingSymmetryProjectiveVectorCovariance raw qa hqa
    let qg := BandPackingSymmetryQuadrupleAction g qa
    let Tg := BandPackingSymmetryTileAction g T
    have hTg : BandPrototile (qg 0) Tg :=
      (BandPackingSymmetryCovariance g).2.1 (q 0) T |>.mp hT
    have hcurv : (qg 0).1 = (q 0).1 :=
      (BandPackingSymmetryCovariance g).1 (q 0)
    have hng : Int.toNat (qg 0).1 = n := hcurv ▸ hn
    have hregimes :
        Xor (∃ F : FordFareyParameter, 1 < F.q ∧ qg = FordRecursiveQuadruple F)
          (Xor (∃ K : DiamondParameter, 1 < K.1 ∧ qg = DiamondRecursiveQuadruple K)
            (Nonempty (BandOrderedGeneralConfiguration qg))) := TileInductionGeometry.hregimes q
                a raw regimes g htuple
    have normalized :
        (LatticeTile Tg ∧ TileArea Tg = Int.toNat (qg 0).1 ∧
        (∀ (S : Fin 3 → Bool → ProtoTile),
          (∀ i s, BandSubtileOccurrence qg Tg i s (S i s)) →
          (∀ x, x ∈ Tg.cells ↔ ∃ i s, x ∈ (S i s).cells) →
          ∀ i s, LatticeTile (TileCellComplement Tg (S i s)) ∧
            TileTouching (TileCellComplement Tg (S i s)) (S i s)) ∧
        QuarterTurnSymmetric Tg ∧
        (1 < (qg 0).1 → ∀ i : Fin 3,
          TouchingTriple Tg
            (TileTranslation Tg (BandVectors.1 (qg i.succ) (qg 0)))
            (TileTranslation Tg
              (-BandVectors.1 (qg ((i + 1).succ)) (qg 0)))) ∧
        (1 < (qg 0).1 → ∀ (i : Fin 3) (U : ProtoTile),
          BandPrototile (qg i.succ) U →
          TileCentroid U - TileCentroid Tg = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (qg i.succ) (qg 0)) +
              GaussianRealPoint (BandVectors.1 (qg 0) (qg i.succ))) →
          TouchingTriple Tg
            (TileTranslation Tg (BandVectors.1 (qg i.succ) (qg 0))) U) ∧
        (∀ (i : Fin 3) (U V : ProtoTile),
          BandPrototile (qg i.succ) U →
          BandPrototile (qg ((i + 1).succ)) V →
          TileCentroid U - TileCentroid Tg = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (qg i.succ) (qg 0)) +
              GaussianRealPoint (BandVectors.1 (qg 0) (qg i.succ))) →
          TileCentroid V - TileCentroid Tg = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (qg ((i + 1).succ)) (qg 0)) -
              GaussianRealPoint (BandVectors.1 (qg 0) (qg ((i + 1).succ)))) →
          TouchingTriple Tg U V)) ∧
        (∀ (r : Fin 4 → CircleCoordinates), ProperBandQuadruple r →
        r 0 = q 1 → r 2 = q 2 → r 3 = q 3 →
        (q 2).1 ≤ (q 1).1 → (q 3).1 ≤ (q 2).1 →
        1 < (q 2).1 →
        ∀ (P Q S : Fin 3 → Bool → ProtoTile),
        (∀ i s, BandSubtileOccurrence q T i s (P i s)) →
        (∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (P i s).cells) →
        (∀ i s, BandSubtileOccurrence r (P 0 true) i s (Q i s)) →
        (∀ x, x ∈ (P 0 true).cells ↔ ∃ i s, x ∈ (Q i s).cells) →
        (∀ i s, BandSubtileOccurrence r (P 0 false) i s (S i s)) →
        (∀ x, x ∈ (P 0 false).cells ↔ ∃ i s, x ∈ (S i s).cells) →
        (let u := BandVectors.1 (q 0) (q 1)
         let v := BandVectors.1 (q 0) (q 2)
         (∀ a b : PeriodicSubtileIndex, a ≠ b →
           ((FootprintEdges (SubtileOccurrenceInterpretation P u v a) ∩
               FootprintEdges
                 (SubtileOccurrenceInterpretation P u v b)).Nonempty →
             AllowedSubtileIncidence a b) ∧
           (¬ AllowedSubtileIncidence a b →
             FootprintVertices (SubtileOccurrenceInterpretation P u v a) ∩
                 FootprintVertices
                   (SubtileOccurrenceInterpretation P u v b) = ∅ ∨
               (FootprintVertices
                    (SubtileOccurrenceInterpretation P u v a) ∩
                  FootprintVertices
                    (SubtileOccurrenceInterpretation P u v b)).Subsingleton)) ∧
         FootprintVertices (P 0 true) ∩ FootprintVertices (P 1 true) ⊆
           FootprintVertices (Q 1 true) ∩ FootprintVertices (P 1 true) ∧
         FootprintVertices (P 0 true) ∩ FootprintVertices (P 0 false) ⊆
           (FootprintVertices (Q 1 true) ∩ FootprintVertices (S 2 false)) ∪
             FootprintVertices (Q 0 false) ∪
             (FootprintVertices (Q 2 true) ∩
               FootprintVertices (S 1 false)))) := TileInductionGeometry.normalized n q hq T hT
                   smallT1 smallT2 smallT4 smallT5 a g hphase hpred hTg hng hregimes
    obtain ⟨geometry, hT6⟩ := normalized
    have disks := P4564T2GeometryPullback q hq T hT a g
      ⟨geometry.1, geometry.2.1, geometry.2.2.1, geometry.2.2.2.1⟩
    have parentQuarter : ∀ (i : Fin 3) (U : ProtoTile),
        BandPrototile (qa i.succ) U → QuarterTurnSymmetric U :=
            TileInductionGeometry.parentQuarter n q hn smallT2 a hqa
    have touching := (BandPackingSymmetryT3T5Covariance g qa hqa hphase
      T hT disks.2.2.2 parentQuarter).mpr
        ⟨geometry.2.2.2.2.1, geometry.2.2.2.2.2.1, geometry.2.2.2.2.2.2⟩
    have childIndex : qa 0 = q 0 := rfl
    have parentIndex : ∀ i : Fin 3, qa i.succ = q (a + i).succ :=
        TileInductionGeometry.parentIndex q a
    have cyclicIndices : ∀ i : Fin 3,
        qa (i - a).succ = q i.succ ∧
          qa ((i - a + 1).succ) = q ((i + 1).succ) := TileInductionGeometry.cyclicIndices q a
              parentIndex
    refine ⟨disks.1, disks.2.1.trans hn, disks.2.2.1, disks.2.2.2,
      ?_, ?_, ?_, hT6⟩
    · intro hc i
      simpa only [childIndex, (cyclicIndices i).1, (cyclicIndices i).2] using
        touching.1 hc (i - a)
    · intro hc i U hU hcent
      have h := touching.2.1 hc (i - a) U
      simp only [(cyclicIndices i).1] at h
      exact h hU hcent
    · intro i U V hU hV hcU hcV
      have h := touching.2.2 (i - a) U V
      simp only [(cyclicIndices i).1, (cyclicIndices i).2] at h
      exact h hU hV hcU hcV

end ApollonianSuperharmonic

end
