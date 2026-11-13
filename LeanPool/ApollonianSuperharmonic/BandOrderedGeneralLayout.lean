/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintInclusion

public import LeanPool.ApollonianSuperharmonic.BandDoubleDecomposition
public import LeanPool.ApollonianSuperharmonic.BandModifiedCoverage
public import LeanPool.ApollonianSuperharmonic.BandModifiedOrbitArea
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTilingTransport
public import LeanPool.ApollonianSuperharmonic.BandPrototileReindexedDecomposition
public import LeanPool.ApollonianSuperharmonic.BandSignedOccurrenceHalfTurn
public import LeanPool.ApollonianSuperharmonic.BandUnmodifiedPeriodicCore
public import LeanPool.ApollonianSuperharmonic.ExceptionalModifiedABPath
public import LeanPool.ApollonianSuperharmonic.IsolatedPrecursorCoverage
public import LeanPool.ApollonianSuperharmonic.OrientedTouchingCovariance
public import LeanPool.ApollonianSuperharmonic.OuterLayoutTouching
public import LeanPool.ApollonianSuperharmonic.P4670T1SmallerGeometry
public import LeanPool.ApollonianSuperharmonic.P4670T1ComplementReflection
public import LeanPool.ApollonianSuperharmonic.P4670T1OrdinaryEdges
public import LeanPool.ApollonianSuperharmonic.BandModifiedCellPartition
public import LeanPool.ApollonianSuperharmonic.BandModifiedPeriodicComplex
public import LeanPool.ApollonianSuperharmonic.TilingLatticeBasis

-- [TABLET NODE: BandOrderedGeneralLayout]

/-!
# BandOrderedGeneralLayout

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OrderedLayoutGeometry

private theorem hPr :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), BandSubtileOccurrence q T i s (P i s)) → (∀ (s : Bool), BandPrototile
            (cfg.firstPredecessor 0) (P 0 s)) ) := by
  classical
  intro q cfg T P hP s
  rw [cfg.firstChild]
  exact (hP 0 s).1

private theorem hQcells :
    (by
      classical
      exact
        ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (x :
            LatticeCell), x ∈ (P (0 : Fin (3 : ℕ)) true).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool),
            x ∈ (Q i s).cells) → (∀ (i : Fin 3), ∀ (s : Bool), (Q i s).cells ⊆ (P 0 true).cells)
            ) := by
  classical
  intro P Q hQunion i s x hx
  exact (hQunion x).mpr ⟨i, s, hx⟩

private theorem hScells :
    (by
      classical
      exact
        ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (x :
            LatticeCell), x ∈ (P (0 : Fin (3 : ℕ)) false).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool),
            x ∈ (S i s).cells) → (∀ (i : Fin 3), ∀ (s : Bool), (S i s).cells ⊆ (P 0 false).cells)
            ) := by
  classical
  intro P S hSunion i s x hx
  exact (hSunion x).mpr ⟨i, s, hx⟩

private theorem pne :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → ((∀ (i : Fin 3),
            0 < (q i.succ).1) → (∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin 3), ∀ (s :
            Bool), TileArea (P i s) = (q i.succ).1.toNat) → (∀ (i : Fin 3), ∀ (s : Bool), (P i
            s).cells.Nonempty))) ) := by
  classical
  intro q cfg parentPos P parea i s
  have ha := parea i s
  have hp := parentPos i
  change (P i s).cells.card = _ at ha
  exact Finset.card_pos.mp (by omega)

private theorem rpPos :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), (∀ (i :
            Fin 3), 0 < (q i.succ).1) → (∀ (i : Fin 3), (i = 1 ∨ i = 2) → (0 <
            (cfg.firstPredecessor i.succ).1)) ) := by
  classical
  intro q cfg parentPos i hi
  rcases hi with rfl | rfl
  · simpa [cfg.firstParentTwo] using parentPos 1
  · simpa [cfg.firstParentThree] using parentPos 2

private theorem qne :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (Q :
            Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (0 : ℤ) ≤
            (cfg.firstPredecessor i.succ).1 ∧ TileArea (Q i s) = (cfg.firstPredecessor
            i.succ).1.toNat ∧ ((0 : ℤ) < (cfg.firstPredecessor i.succ).1 → LatticeTile (Q i s)))
            → ((∀ (i : Fin 3), (i = 1 ∨ i = 2) → (0 < (cfg.firstPredecessor i.succ).1)) → (∀ (i :
            Fin 3), ∀ (s : Bool), (i = 1 ∨ i = 2) → ((Q i s).cells.Nonempty))) ) := by
  classical
  intro q cfg Q qg rpPos i s hi
  have ha := (qg i s).2.1
  have hp := rpPos i hi
  change (Q i s).cells.card = _ at ha
  exact Finset.card_pos.mp (by omega)

private abbrev sne :=
  ApollonianSuperharmonic.OrderedLayoutGeometry.qne

private theorem oriented :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (∀ (D : CircleCoordinates), ∀ (U : ProtoTile),
            BandPrototile D U → D.1.toNat < (q (0 : Fin (4 : ℕ))).1.toNat → QuarterTurnSymmetric
            U) → ((∀ (q' : Fin (4 : ℕ) → CircleCoordinates), ∀ (T' : ProtoTile), ∀ (U :
            ProtoTile), ProperBandQuadruple q' → BandPrototile (q' (0 : Fin (4 : ℕ))) T' → (q' (0
            : Fin (4 : ℕ))).1.toNat < (q (0 : Fin (4 : ℕ))).1.toNat → (1 : ℤ) < (q' (0 : Fin (4 :
            ℕ))).1 → ∀ (i : Fin (3 : ℕ)), BandPrototile (q' i.succ) U → TileCentroid U -
            TileCentroid T' = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q' i.succ) (q' (0
            : Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q'
            i.succ))) → TouchingTriple T' (TileTranslation T' (BandVectors.1 (q' i.succ) (q' (0 :
            Fin (4 : ℕ))))) U) → ((∀ (q' : Fin (4 : ℕ) → CircleCoordinates), ∀ (T' : ProtoTile),
            ∀ (U : ProtoTile), ∀ (V : ProtoTile), ProperBandQuadruple q' → BandPrototile (q' (0 :
            Fin (4 : ℕ))) T' → (q' (0 : Fin (4 : ℕ))).1.toNat < (q (0 : Fin (4 : ℕ))).1.toNat → ∀
            (i : Fin (3 : ℕ)), BandPrototile (q' i.succ) U → BandPrototile (q' (i + (1 : Fin (3 :
            ℕ))).succ) V → TileCentroid U - TileCentroid T' = (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (q' i.succ) (q' (0 : Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1
            (q' (0 : Fin (4 : ℕ))) (q' i.succ))) → TileCentroid V - TileCentroid T' = (1 / 2 : ℝ)
            • (GaussianRealPoint (BandVectors.1 (q' (i + (1 : Fin (3 : ℕ))).succ) (q' (0 : Fin (4
            : ℕ)))) - GaussianRealPoint (BandVectors.1 (q' (0 : Fin (4 : ℕ))) (q' (i + (1 : Fin
            (3 : ℕ))).succ))) → TouchingTriple T' U V) → ((0 < (q 0).1) → (∀ (p : Fin (4 : ℕ) →
            CircleCoordinates), ProperBandQuadruple p → (p (0 : Fin (4 : ℕ))).1 < (q (0 : Fin (4
            : ℕ))).1 → (1 : ℤ) < (p (0 : Fin (4 : ℕ))).1 → (∀ (T₀ : ProtoTile), ∀ (Tᵢ :
            ProtoTile), ∀ (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), BandPrototile (p (0 : Fin (4 :
            ℕ))) T₀ → BandPrototile (p i.succ) Tᵢ → TileCentroid Tᵢ - TileCentroid T₀ = (1 / 2 :
            ℝ) • (GaussianRealPoint (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (p i.succ) (p
            (0 : Fin (4 : ℕ))))) + GaussianRealPoint (GaussianQuarterTurn^[(↑s : ℕ)]
            (BandVectors.1 (p (0 : Fin (4 : ℕ))) (p i.succ)))) → TouchingTriple T₀
            (TileTranslation T₀ (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (p i.succ) (p (0 :
            Fin (4 : ℕ)))))) Tᵢ) ∧ ∀ (T₀ : ProtoTile), ∀ (Tᵢ : ProtoTile), ∀ (Tⱼ : ProtoTile), ∀
            (i : Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), BandPrototile (p (0 : Fin (4 : ℕ))) T₀ →
            BandPrototile (p i.succ) Tᵢ → BandPrototile (p (i + (1 : Fin (3 : ℕ))).succ) Tⱼ →
            TileCentroid Tᵢ - TileCentroid T₀ = (1 / 2 : ℝ) • (GaussianRealPoint
            (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (p i.succ) (p (0 : Fin (4 : ℕ))))) +
            GaussianRealPoint (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (p (0 : Fin (4 :
            ℕ))) (p i.succ)))) → TileCentroid Tⱼ - TileCentroid T₀ = (1 / 2 : ℝ) •
            (GaussianRealPoint (GaussianQuarterTurn^[(↑s : ℕ)] (BandVectors.1 (p (i + (1 : Fin (3
            : ℕ))).succ) (p (0 : Fin (4 : ℕ))))) - GaussianRealPoint (GaussianQuarterTurn^[(↑s :
            ℕ)] (BandVectors.1 (p (0 : Fin (4 : ℕ))) (p (i + (1 : Fin (3 : ℕ))).succ)))) →
            TouchingTriple T₀ Tᵢ Tⱼ)))) ) := by
  classical
  intro q hsmallT2 hsmallT4 hsmallT5 hqpos p hp hlt hlarge
  have hs := (Int.toNat_lt_toNat hqpos).mpr hlt
  exact OrientedTouchingCovariance p hp
    (fun a U hu => hsmallT2 _ U hu ((Int.toNat_lt_toNat hqpos).mpr (by
      fin_cases a
      · exact hlt
      · exact (hp.2 0).trans hlt
      · exact (hp.2 1).trans hlt
      · exact (hp.2 2).trans hlt)))
    (fun V U i hv hu hc => hsmallT4 p V U hp hv hs hlarge i hu hc)
    (fun V U W i hv hu hw hc hd => hsmallT5 p V U W hp hv hs i hu hw hc hd)

private theorem rlarge :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), 1 <
            (cfg.firstPredecessor 0).1 ) := by
  classical
  intro q cfg
  rw [cfg.firstChild]
  have := cfg.order12
  have := cfg.secondLarge
  omega

private theorem tlarge :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), 1 <
            (cfg.secondPredecessor 0).1 ) := by
  classical
  intro q cfg
  rw [cfg.secondChild]
  have := cfg.secondLarge
  omega

private theorem nonunitA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (∀ (P : Fin (3 :
            ℕ) → Bool → ProtoTile), (∀ (i : Fin 3), ∀ (s : Bool), TileArea (P i s) = (q
            i.succ).1.toNat) → (TileArea (P 0 true) ≠ 1)) ) := by
  classical
  intro q cfg P parea
  rw [parea]
  have := cfg.order12
  have := cfg.secondLarge
  change (q 1).1.toNat ≠ 1
  omega

private theorem nonunitB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (∀ (P : Fin (3 :
            ℕ) → Bool → ProtoTile), (∀ (i : Fin 3), ∀ (s : Bool), TileArea (P i s) = (q
            i.succ).1.toNat) → (TileArea (P 0 false) ≠ 1)) ) := by
  classical
  intro q cfg P parea
  rw [parea]
  have := cfg.order12
  have := cfg.secondLarge
  change (q 1).1.toNat ≠ 1
  omega

private theorem nonunitC :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (∀ (P : Fin (3 :
            ℕ) → Bool → ProtoTile), (∀ (i : Fin 3), ∀ (s : Bool), TileArea (P i s) = (q
            i.succ).1.toNat) → (TileArea (P 1 true) ≠ 1)) ) := by
  classical
  intro q cfg P parea
  rw [parea]
  have := cfg.secondLarge
  change (q 2).1.toNat ≠ 1
  omega

private theorem Odisk :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (Q :
            Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (0 : ℤ) ≤
            (cfg.firstPredecessor i.succ).1 ∧ TileArea (Q i s) = (cfg.firstPredecessor
            i.succ).1.toNat ∧ ((0 : ℤ) < (cfg.firstPredecessor i.succ).1 → LatticeTile (Q i s))) → (
        let O := Q 0 false
        O.cells.Nonempty → LatticeTile O) ) := by
  classical
  intro q cfg Q qg O ho
  apply (qg 0 false).2.2
  have ha := (qg 0 false).2.1
  have hp := (qg 0 false).1
  have hc := Finset.card_pos.mpr ho
  change O.cells.card = _ at ha
  change 0 < (cfg.firstPredecessor (0 : Fin 3).succ).1
  omega

private theorem hindex :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandOrderedGeneralConfiguration q) → (∀ (C₀ :
            BandCircle), (q (0 : Fin (4 : ℕ)) = C₀.1.1) → ((∀ (k : Fin (4 : ℕ)), (0 : ℤ) ≤ (q
            k).1) → (∀ (R : Finset GaussianInt), (R.card = C₀.1.1.1.natAbs) → (R.card = (q
            0).1.toNat)))) ) := by
  classical
  intro q cfg C₀ hC₀ hn R hcount
  rw [hC₀]
  apply hcount.trans
  have ha := Int.natAbs_of_nonneg (by simpa [hC₀] using hn 0)
  omega

private theorem ocenter :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), BandSubtileOccurrence q T i s (P i s)) → (∀ (Q : Fin (3 : ℕ) → Bool →
            ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence
            cfg.firstPredecessor (P (0 : Fin (3 : ℕ)) true) i s (Q i s)) → (
        let O := Q 0 false
        TileCentroid O = TileCentroid T)) ) := by
  classical
  intro q cfg T P hP Q hQ O
  let d := (1 / 2 : Real) •
    (GaussianRealPoint (BandVectors.1 (q 3) (q 2)) -
      (-(GaussianRealPoint (BandVectors.1 (q 3) (q 2))).2,
        (GaussianRealPoint (BandVectors.1 (q 3) (q 2))).1))
  have hp : TileCentroid (P 0 true) - TileCentroid T = d := by
    simpa [d] using (hP 0 true).2.2
  have hq : TileCentroid O - TileCentroid (P 0 true) = -d := by
    have h := (hQ 0 false).2.2
    change TileCentroid O - TileCentroid (P 0 true) =
      (-1 : Real) • ((1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 3) (cfg.firstPredecessor 2)) -
          (-(GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 3)
            (cfg.firstPredecessor 2))).2,
            (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor 3)
              (cfg.firstPredecessor 2))).1))) at h
    simpa [cfg.firstParentThree, cfg.firstParentTwo, d] using h
  apply sub_eq_zero.mp
  calc
    TileCentroid O - TileCentroid T =
      (TileCentroid O - TileCentroid (P 0 true)) +
        (TileCentroid (P 0 true) - TileCentroid T) := by abel
    _ = 0 := by rw [hp, hq]; simp

private theorem compEq :
    (by
      classical
      exact
        ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (S :
            Fin (3 : ℕ) → Bool → ProtoTile), ((Q (0 : Fin (3 : ℕ)) false).cells = (S (0 : Fin (3
            : ℕ)) true).cells) → (
        let O := Q 0 false
        TileCellComplement (P 0 false) (S 0 true) = TileCellComplement (P 0 false) O) ) := by
  classical
  intro P Q S hcommon O
  simp only [TileCellComplement, ← hcommon, O]

private theorem sameTouch :
    (by
      classical
      exact
        ∀ (Q : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ((Q (0 :
            Fin (3 : ℕ)) false).cells = (S (0 : Fin (3 : ℕ)) true).cells) → (((Q (0 : Fin (3 :
            ℕ)) false).cells = ∅ → (Q (0 : Fin (3 : ℕ)) false).anchor = (S (0 : Fin (3 : ℕ))
            true).anchor) → (
        let O := Q 0 false
        (FootprintVertices (Q (0 : Fin (3 : ℕ)) false) = FootprintVertices (S (0 : Fin (3 : ℕ))
            true) ∧ BoundaryFootprintVertices (Q (0 : Fin (3 : ℕ)) false) =
            BoundaryFootprintVertices (S (0 : Fin (3 : ℕ)) true) ∧ BoundaryFootprintEdges (Q (0 :
            Fin (3 : ℕ)) false) = BoundaryFootprintEdges (S (0 : Fin (3 : ℕ)) true) ∧
            TileRealization (Q (0 : Fin (3 : ℕ)) false) = TileRealization (S (0 : Fin (3 : ℕ))
            true) ∧ TileCentroid (Q (0 : Fin (3 : ℕ)) false) = TileCentroid (S (0 : Fin (3 : ℕ))
            true)) → (∀ (U : ProtoTile), TileTouching U (S 0 true) ↔ TileTouching U O))) ) := by
  classical
  intro Q S hcommon hanchor O sameObs U
  unfold TileTouching
  rw [← sameObs.2.1, ← sameObs.2.2.1, ← hcommon]
  by_cases he : (Q 0 false).cells = ∅
  · simp only [O, he, Finset.not_nonempty_empty, false_and, true_and,
      hanchor he]
  · simp [O, he]

private theorem compB :
    (by
      classical
      exact
        ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (S :
            Fin (3 : ℕ) → Bool → ProtoTile), (LatticeTile (TileCellComplement (P (0 : Fin (3 :
            ℕ)) false) (S (0 : Fin (3 : ℕ)) true)) ∧ TileTouching (TileCellComplement (P (0 : Fin
            (3 : ℕ)) false) (S (0 : Fin (3 : ℕ)) true)) (S (0 : Fin (3 : ℕ)) true)) → (
        let O := Q 0 false
        (TileCellComplement (P 0 false) (S 0 true) = TileCellComplement (P 0 false) O) → ((∀ (U :
            ProtoTile), TileTouching U (S 0 true) ↔ TileTouching U O) → (LatticeTile
            (TileCellComplement (P 0 false) O) ∧ TileTouching (TileCellComplement (P 0 false) O)
            O))) ) := by
  classical
  intro P Q S compS O compEq sameTouch
  refine ⟨compEq ▸ compS.1, ?_⟩
  exact (sameTouch _).mp (compEq ▸ compS.2)

private theorem central :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (T :
            ProtoTile), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), BandSubtileOccurrence q T i s (P i s)) → (∀ (Q : Fin (3 : ℕ) → Bool →
            ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence
            cfg.firstPredecessor (P (0 : Fin (3 : ℕ)) true) i s (Q i s)) → ((∀ (i : Fin 3), ∀ (s
            : Bool), (P i s).cells.Nonempty) → (
        let O := Q 0 false
        (TileCentroid O = TileCentroid T) → (CentrallyReflectedAt (TileCentroid O)
            (TileCellComplement (P 0 true) O) (TileCellComplement (P 0 false) O))))) ) := by
  classical
  intro q cfg T P hP Q hQ pne O ocenter
  apply P4670T1ComplementReflection _ _ _ _ (pne 0 true)
  · rw [ocenter]
    exact (BandSignedOccurrenceHalfTurn q (TileCentroid T) P
      (fun i s => (hP i s).1) (fun i s => (hP i s).2.2) 0).2.2.2.2.2
  · exact BandPrototileCentralSymmetry _ _ (hQ 0 false).1

private theorem compDisjoint :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3
            : ℕ) → Bool → ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let O := Q 0 false
        let u := BandVectors.1 (q 0) (q 1)
        let v := BandVectors.1 (q 0) (q 2)
        ((∀ (m : ℤ), ∀ (n : ℤ), (SubtileOccurrenceInterpretation P u v (⟨SixSubtileLabel.A, m, n⟩
            : PeriodicSubtileIndex)).cells ∩ (SubtileOccurrenceInterpretation P u v
            (⟨SixSubtileLabel.B, m, n⟩ : PeriodicSubtileIndex)).cells = (TileTranslation O ((↑m :
            GaussianInt) * u + (↑n : GaussianInt) * v)).cells) ∧ ∀ (a : PeriodicSubtileIndex), ∀
            (b : PeriodicSubtileIndex), a ≠ b → ¬((a.label = SixSubtileLabel.A ∧ b.label =
            SixSubtileLabel.B ∨ a.label = SixSubtileLabel.B ∧ b.label = SixSubtileLabel.A) ∧
            a.first = b.first ∧ a.second = b.second) → Disjoint (SubtileOccurrenceInterpretation
            P u v a).cells (SubtileOccurrenceInterpretation P u v b).cells) → (Disjoint
            (TileCellComplement (P 0 true) O).cells (TileCellComplement (P 0 false) (S 0
            true)).cells) ) := by
  classical
  intro q P Q S O u v hsep
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have hc : a ∈ (P 0 true).cells ∩ (P 0 false).cells :=
    Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp ha).1, (Finset.mem_sdiff.mp hb).1⟩
  have hz := hsep.1 0 0
  have ht0 (U : ProtoTile) : TileTranslation U 0 = U := by
    have hz : GaussianTranslation 0 = id := by funext z; exact add_zero z
    cases U
    simp only [TileTranslation, hz, Finset.image_id, id_eq]
  simp only [SubtileOccurrenceInterpretation, Int.cast_zero, zero_mul, zero_add, ht0] at hz
  exact (Finset.mem_sdiff.mp ha).2 (hz ▸ hc)

private theorem periodicIsolation :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3
            : ℕ) → Bool → ProtoTile),
        let O := Q 0 false
        let u := BandVectors.1 (q 0) (q 1)
        let v := BandVectors.1 (q 0) (q 2)
        (∀ y ∈ FootprintVertices (Q (0 : Fin (3 : ℕ)) false), ∀ (a : GaussianInt), y ∈
            FootprintVertices (⟨{a}, a⟩ : ProtoTile) → a ∈ (P (0 : Fin (3 : ℕ)) true).cells ∨ a ∈
            (P (0 : Fin (3 : ℕ)) false).cells) → (∀ m n : Int, ∀ x ∈ FootprintVertices
            (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)), ∀ a :
            GaussianInt, x ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) → a ∈
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells ∨ a ∈
            (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells) ) := by
  classical
  intro q P Q O u v isolated m n x hx a hxa
  let w := (m : GaussianInt) * u + (n : GaussianInt) * v
  rw [(TileTranslationFormulas O w).2.2.2.2.2.1] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  have hs : TileTranslation (⟨{a - w}, a - w⟩ : ProtoTile) w = ⟨{a}, a⟩ := by
    simp [TileTranslation, GaussianTranslation]
  rw [← hs, (TileTranslationFormulas _ w).2.2.2.2.2.1] at hxa
  obtain ⟨b, hb, hbx⟩ := hxa
  have hbz : b = z := add_right_cancel (hbx.trans hzx.symm)
  subst b
  have ht (U : ProtoTile) (ha : a - w ∈ U.cells) : a ∈ (TileTranslation U w).cells := by
    exact Finset.mem_image.mpr ⟨a - w, ha, sub_add_cancel a w⟩
  exact (isolated z hz (a - w) hb).imp (ht _) (ht _)

private theorem diskNonempty :
    (by
      classical
      exact
        ∀ (U : ProtoTile), (LatticeTile U) → (U.cells.Nonempty) ) := by
  classical
  intro U hU
  obtain ⟨e⟩ := hU
  have hp := (e ⟨0, by simp⟩).property
  simp only [TileRealization, Set.mem_iUnion] at hp
  obtain ⟨x, hx, _⟩ := hp
  exact ⟨x, hx⟩

private abbrev boundaryEdge :=
  BoundaryFootprintInclusion.boundaryEdge

private theorem touchEdge :
    (by
      classical
      exact
        (∀ (U : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges U) → (e ∈
            FootprintEdges U)) → (∀ (U : ProtoTile), ∀ (V : ProtoTile), (U.cells.Nonempty) →
            ((V.cells.Nonempty) → ((TileTouching U V) → ((FootprintEdges U ∩ FootprintEdges
            V).Nonempty)))) ) := by
  classical
  intro boundaryEdge U V hu hv ht
  rcases ht with h | h | h
  · obtain ⟨p, _, hp, _, _, he⟩ := h.2.2.2
    cases p with
    | nil => simp at hp
    | cons a p =>
      cases p with
      | nil => simp at hp
      | cons b p =>
        have h := (he {a, b}).mpr ⟨a, b, [], p, rfl, rfl⟩
        exact ⟨{a, b}, boundaryEdge _ _ h.1, boundaryEdge _ _ h.2⟩
  · exact (hu.ne_empty h.1).elim
  · exact (hv.ne_empty h.1).elim

private theorem edgeMono :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (V : ProtoTile), (U.cells ⊆ V.cells) → (FootprintEdges U ⊆
            FootprintEdges V) ) := by
  classical
  intro U V h
  rintro e ⟨z, hz, he⟩
  exact ⟨z, h hz, he⟩

private theorem abEdge :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
            (BandCircle) → (∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (s : Bool), BandPrototile
            (cfg.firstPredecessor 0) (P 0 s)) → (∀ (Q : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i :
            Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence cfg.firstPredecessor (P (0 : Fin (3
            : ℕ)) true) i s (Q i s)) → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), BandSubtileOccurrence cfg.firstPredecessor (P (0 : Fin (3 : ℕ))
            false) i s (S i s)) → ((LatticeTile (TileCellComplement (P (0 : Fin (3 : ℕ)) true) (Q
            (0 : Fin (3 : ℕ)) false)) ∧ TileTouching (TileCellComplement (P (0 : Fin (3 : ℕ))
            true) (Q (0 : Fin (3 : ℕ)) false)) (Q (0 : Fin (3 : ℕ)) false)) → (
        let O := Q 0 false
        (O.cells ⊆ (P 0 false).cells) → ((Finset GaussianInt) → ((FootprintVertices (Q (0 : Fin
            (3 : ℕ)) false) = FootprintVertices (S (0 : Fin (3 : ℕ)) true) ∧
            BoundaryFootprintVertices (Q (0 : Fin (3 : ℕ)) false) = BoundaryFootprintVertices (S
            (0 : Fin (3 : ℕ)) true) ∧ BoundaryFootprintEdges (Q (0 : Fin (3 : ℕ)) false) =
            BoundaryFootprintEdges (S (0 : Fin (3 : ℕ)) true) ∧ TileRealization (Q (0 : Fin (3 :
            ℕ)) false) = TileRealization (S (0 : Fin (3 : ℕ)) true) ∧ TileCentroid (Q (0 : Fin (3
            : ℕ)) false) = TileCentroid (S (0 : Fin (3 : ℕ)) true)) → (((Q (0 : Fin (3 : ℕ))
            false).cells = ∅ → (cfg.firstPredecessor (1 : Fin (4 : ℕ))).1 = (0 : ℤ)) → ((∀ (U :
            ProtoTile), (LatticeTile U) → (U.cells.Nonempty)) → ((∀ (U : ProtoTile), ∀ (V :
            ProtoTile), (U.cells.Nonempty) → ((V.cells.Nonempty) → ((TileTouching U V) →
            ((FootprintEdges U ∩ FootprintEdges V).Nonempty)))) → ((∀ (U : ProtoTile), ∀ (V :
            ProtoTile), (U.cells ⊆ V.cells) → (FootprintEdges U ⊆ FootprintEdges V)) →
            ((FootprintEdges (TileCellComplement (P 0 true) O) ∩ FootprintEdges (P 0
            false)).Nonempty)))))))))))) ) := by
  classical
  intro q cfg C₀ P hPr Q hQ S hS compQ O hOB R sameObs zero diskNonempty touchEdge edgeMono
  by_cases he : O.cells = ∅
  · have hac := (hQ 0 false).2.2
    have hbc := (hS 0 true).2.2
    rw [← sameObs.2.2.2.2] at hbc
    obtain ⟨F, g, e, h1, h2, _, _, upper, lower⟩ :=
      P4638T1EmptyFordLocalization cfg.firstPredecessor cfg.firstProper
        (P 0 true) (P 0 false) O (hPr true) (hPr false) he (zero he)
        (by simpa [O] using hac) (by simpa [O] using hbc)
    let a := (BandPackingSymmetryTileAction g O).anchor
    have h1' : 0 < (F.q₁ : Int) := by exact_mod_cast h1
    have h2' : 0 < (F.q₂ : Int) := by exact_mod_cast h2
    have hA : a ∈ (BandPackingSymmetryTileAction g (P 0 true)).cells := by
      apply (upper a).mpr
      simp only [a, sub_self]
      change -(F.q₁ : Int) ≤ 0 ∧ 0 < (F.q₂ : Int) ∧
        (0 : Int) ≤ 0 ∧ 0 < ((F.q₁ + F.q₂ : Nat) : Int)
      rw [Nat.cast_add]
      omega
    have hB : a - ⟨0, 1⟩ ∈ (BandPackingSymmetryTileAction g (P 0 false)).cells := by
      apply (lower (a - ⟨0, 1⟩)).mpr
      have hd : a - ⟨0, 1⟩ - a = -(⟨0, 1⟩ : GaussianInt) := by abel
      change -(F.q₂ : Int) ≤ (a - ⟨0, 1⟩ - a).re ∧ _
      rw [hd]
      change -(F.q₂ : Int) ≤ 0 ∧ 0 < (F.q₁ : Int) ∧
        -((F.q₁ + F.q₂ : Nat) : Int) ≤ -1 ∧ (-1 : Int) < 0
      rw [Nat.cast_add]
      omega
    have hcommonEdge : {a, a + 1} ∈
        FootprintEdges (BandPackingSymmetryTileAction g (P 0 true)) ∩
          FootprintEdges (BandPackingSymmetryTileAction g (P 0 false)) := by
      refine ⟨⟨a, hA, Or.inl rfl⟩, ⟨a - ⟨0, 1⟩, hB, Or.inr (Or.inr (Or.inr ?_))⟩⟩
      congr 1 <;> congr 1 <;> abel
    have inj : ∀ g : BandPackingSymmetry, Function.Injective (BandPackingSymmetryVectorAction
        g) := by
      intro g
      induction g with
      | identity => exact fun _ _ h => h
      | shift w => exact fun _ _ h => h
      | negate =>
        intro a b h
        have hx := congrArg Zsqrtd.re h
        have hy := congrArg Zsqrtd.im h
        change -a.im = -b.im at hx
        change a.re = b.re at hy
        exact Zsqrtd.ext hy (neg_injective hx)
      | conjugate =>
        intro a b h
        have hx := congrArg Zsqrtd.re h
        have hy := congrArg Zsqrtd.im h
        change -a.re = -b.re at hx
        change -(-a.im) = -(-b.im) at hy
        exact Zsqrtd.ext (neg_injective hx) (by simpa only [neg_neg] using hy)
      | comp g h ig ih => exact ig.comp ih
    have edges := (BandPackingSymmetryTilingTransport g).2.2.2.2.2.2.2.2.1
    rw [edges, edges] at hcommonEdge
    obtain ⟨f, hf, hfe⟩ := hcommonEdge.1
    obtain ⟨f', hf', hf'e⟩ := hcommonEdge.2
    have hff' : f = f' := Finset.image_injective (inj g) (hfe.trans hf'e.symm)
    have hdel : (TileCellComplement (P 0 true) O).cells = (P 0 true).cells := by
      simp [TileCellComplement, he]
    refine ⟨f, edgeMono _ _ (by rw [hdel]) hf, hff' ▸ hf'⟩
  · obtain ⟨e, heA, heO⟩ := touchEdge _ _ (diskNonempty _ compQ.1)
      (Finset.nonempty_iff_ne_empty.mpr he) compQ.2
    exact ⟨e, heA, edgeMono _ _ hOB heO⟩

private theorem edgeVertex :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges U) → (∀ (x :
            GaussianInt), (x ∈ e) → (x ∈ FootprintVertices U)) ) := by
  classical
  intro U e he x hx
  obtain ⟨z, hz, he⟩ := he
  simp only [FootprintVertices, ite_eq_left (show U.cells.Nonempty from ⟨z, hz⟩),
      Set.mem_ofPred_eq]
  rcases he with h | h | h | h <;> subst e
  all_goals simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  · rcases hx with rfl | rfl
    · exact ⟨_, hz, Or.inl rfl⟩
    · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
  · rcases hx with rfl | rfl
    · exact ⟨_, hz, Or.inl rfl⟩
    · exact ⟨z, hz, Or.inr (Or.inr (Or.inl rfl))⟩
  · rcases hx with rfl | rfl
    · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
    · exact ⟨z, hz, Or.inr (Or.inr (Or.inr rfl))⟩
  · rcases hx with rfl | rfl
    · exact ⟨z, hz, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨z, hz, Or.inr (Or.inr (Or.inr rfl))⟩

private theorem commonVertices :
    (by
      classical
      exact
        (
        (∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3 : ℕ) → Bool → ProtoTile),
        let O := Q 0 false;
        (((FootprintEdges (TileCellComplement (P 0 true) O) ∩
            FootprintEdges (P 0 false)).Nonempty) → ((∀ (U : ProtoTile), ∀ (e : Finset
            GaussianInt), (e ∈ FootprintEdges U) → (∀ (x : GaussianInt), (x ∈ e) → (x ∈
            FootprintVertices U))) → (∃ x y : GaussianInt, x ≠ y ∧ x ∈ FootprintVertices
            (TileCellComplement (P 0 true) O) ∩ FootprintVertices (P 0 false) ∧ y ∈
            FootprintVertices (TileCellComplement (P 0 true) O) ∩ FootprintVertices (P 0
            false)))))) ) := by
  classical
  intro P Q O abEdge edgeVertex
  obtain ⟨e, heA, heB⟩ := abEdge
  have hc : e.card = 2 := by
    obtain ⟨z, _, h⟩ := heA
    rcases h with rfl | rfl | rfl | rfl <;> simp [Zsqrtd.ext_iff]
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < e.card)
  exact ⟨x, y, hxy, ⟨edgeVertex _ _ heA _ hx, edgeVertex _ _ heB _ hx⟩,
    ⟨edgeVertex _ _ heA _ hy, edgeVertex _ _ heB _ hy⟩⟩

private theorem modifiedDisks :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (Q : Fin (3
            : ℕ) → Bool → ProtoTile), (∀ (i : Fin 3), ∀ (s : Bool), LatticeTile (P i s)) →
            ((LatticeTile (TileCellComplement (P (0 : Fin (3 : ℕ)) true) (Q (0 : Fin (3 : ℕ))
            false)) ∧ TileTouching (TileCellComplement (P (0 : Fin (3 : ℕ)) true) (Q (0 : Fin (3
            : ℕ)) false)) (Q (0 : Fin (3 : ℕ)) false)) → (
        let O := Q 0 false
        let u := BandVectors.1 (q 0) (q 1)
        let v := BandVectors.1 (q 0) (q 2)
        ∀ (o : PeriodicSubtileIndex), LatticeTile (ModifiedSubtileOccurrenceInterpretation P O u
            v o))) ) := by
  classical
  intro q P Q pdisks compQ O u v o
  rcases o with ⟨l, m, n⟩
  cases l
  all_goals apply ((TileDiskAreaCovariance _ _).1).mp
  · exact compQ.1
  · exact pdisks 0 false
  · exact pdisks 1 true
  · exact pdisks 1 false
  · exact pdisks 2 true
  · exact pdisks 2 false

private theorem repCard :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (P : Fin (3 : ℕ) → Bool → ProtoTile),
        let u := BandVectors.1 (q 0) (q 1)
        let v := BandVectors.1 (q 0) (q 2)
        let L := AddSubgroup.closure ({u, v} : Set GaussianInt)
        ∀ (R : Finset GaussianInt), (LatticeFundamentalSet (AddSubgroup.closure
            {BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))),
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))}) R) → (∀ (K :
            BandUnmodifiedCoreCertificate P u v L), K.core.latticeReps.card = R.card) ) := by
  classical
  intro q P u v L R hfund K
  have hf : LatticeFundamentalSet L K.core.latticeReps := by
    simpa only [K.lattice_eq] using K.core.lattice_full_rank
  let f : GaussianInt → GaussianInt := fun x => Classical.choose (hfund x)
  have fspec (x : GaussianInt) : f x ∈ R ∧ x - f x ∈ L :=
    (Classical.choose_spec (hfund x)).1
  apply Finset.card_nbij f
  · intro x _
    exact (fspec x).1
  · intro x hx y hy hxy
    have hxyL : x - y ∈ L := by
      have h := L.sub_mem (fspec x).2 (fspec y).2
      rw [hxy] at h
      convert h using 1; abel
    exact (hf x).unique ⟨hx, by simp⟩ ⟨hy, hxyL⟩
  · intro y hy
    obtain ⟨x, hx, _⟩ := hf y
    refine ⟨x, hx.1, ?_⟩
    apply (hfund x).unique (fspec x)
    refine ⟨hy, ?_⟩
    simpa only [neg_sub] using L.neg_mem hx.2

end OrderedLayoutGeometry

namespace OrderedLayoutCertificate

private theorem layoutCertificate :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), (q (0 : Fin (4 : ℕ)) = C₀.1.1) → (∀ (T : ProtoTile), (∀ (D :
            CircleCoordinates), ∀ (U : ProtoTile), BandPrototile D U → D.1.toNat < (q (0 : Fin (4
            : ℕ))).1.toNat → QuarterTurnSymmetric U) → ((∀ (i : Fin 3), (q i.succ).1.toNat < (q
            0).1.toNat) → (∀ (P : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), BandSubtileOccurrence q T i s (P i s)) → ((∀ (x : LatticeCell), x ∈ T.cells ↔
            ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (P i s).cells) → (∀ (Q : Fin (3 : ℕ) → Bool →
            ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence
            cfg.firstPredecessor (P (0 : Fin (3 : ℕ)) true) i s (Q i s)) → ((∀ (x : LatticeCell),
            x ∈ (P (0 : Fin (3 : ℕ)) true).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (Q i
            s).cells) → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), BandSubtileOccurrence cfg.firstPredecessor (P (0 : Fin (3 : ℕ)) false) i s (S
            i s)) → ((∀ (x : LatticeCell), x ∈ (P (0 : Fin (3 : ℕ)) false).cells ↔ ∃ (i : Fin (3
            : ℕ)) (s : Bool), x ∈ (S i s).cells) → ((∀ (i : Fin 3), ∀ (s : Bool), LatticeTile (P
            i s)) → ((LatticeTile (TileCellComplement (P (0 : Fin (3 : ℕ)) true) (Q (0 : Fin (3 :
            ℕ)) false)) ∧ TileTouching (TileCellComplement (P (0 : Fin (3 : ℕ)) true) (Q (0 : Fin
            (3 : ℕ)) false)) (Q (0 : Fin (3 : ℕ)) false)) → ((TouchingTriple (P (0 : Fin (3 : ℕ))
            true) (TileTranslation (P (0 : Fin (3 : ℕ)) false) (BandVectors.1 (q (0 : Fin (4 :
            ℕ))) (q (2 : Fin (4 : ℕ))))) (TileTranslation (P (2 : Fin (3 : ℕ)) true)
            (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))) ∧ TouchingTriple (P (0 :
            Fin (3 : ℕ)) true) (TileTranslation (P (0 : Fin (3 : ℕ)) false) (BandVectors.1 (q (0
            : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))) (P (2 : Fin (3 : ℕ)) false) ∧ TouchingTriple
            (P (0 : Fin (3 : ℕ)) true) (TileTranslation (P (0 : Fin (3 : ℕ)) false)
            (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) + BandVectors.1 (q (0 :
            Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))) (TileTranslation (P (1 : Fin (3 : ℕ)) true)
            (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) + BandVectors.1 (q (0 :
            Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))) ∧ TouchingTriple (P (0 : Fin (3 : ℕ)) true)
            (TileTranslation (P (0 : Fin (3 : ℕ)) false) (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q
            (1 : Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))) (P
            (1 : Fin (3 : ℕ)) false) ∧ TouchingTriple (P (0 : Fin (3 : ℕ)) true) (TileTranslation
            (P (1 : Fin (3 : ℕ)) true) (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ)))
            + BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))) (TileTranslation (P (2
            : Fin (3 : ℕ)) true) (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))) ∧
            TouchingTriple (P (0 : Fin (3 : ℕ)) false) (TileTranslation (P (1 : Fin (3 : ℕ))
            false) (-BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) - BandVectors.1 (q
            (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))) (TileTranslation (P (2 : Fin (3 : ℕ))
            false) (-BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))) ∧ TouchingTriple
            (P (1 : Fin (3 : ℕ)) true) (TileTranslation (P (1 : Fin (3 : ℕ)) false)
            (-BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))))) (TileTranslation (P (2
            : Fin (3 : ℕ)) true) (-BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))))) ∧
            TouchingTriple (P (1 : Fin (3 : ℕ)) true) (TileTranslation (P (1 : Fin (3 : ℕ))
            false) (-BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))))) (P (2 : Fin (3 :
            ℕ)) false)) → (((Q (0 : Fin (3 : ℕ)) false).cells = (S (0 : Fin (3 : ℕ)) true).cells)
            → (((Q (0 : Fin (3 : ℕ)) false).cells = ∅ → (Q (0 : Fin (3 : ℕ)) false).anchor = (S
            (0 : Fin (3 : ℕ)) true).anchor) → ((TouchingTriple (Q (1 : Fin (3 : ℕ)) true) (S (2 :
            Fin (3 : ℕ)) false) (Q (0 : Fin (3 : ℕ)) false)) → ((TouchingTriple (Q (2 : Fin (3 :
            ℕ)) true) (S (1 : Fin (3 : ℕ)) false) (Q (0 : Fin (3 : ℕ)) false)) → ((TouchingTriple
            (Q (1 : Fin (3 : ℕ)) true) (S (2 : Fin (3 : ℕ)) false) (P (1 : Fin (3 : ℕ)) true)) →
            ((TouchingTriple (Q (2 : Fin (3 : ℕ)) true) (S (1 : Fin (3 : ℕ)) false) (P (1 : Fin
            (3 : ℕ)) false)) → ((TouchingTriple (Q (1 : Fin (3 : ℕ)) true) (P (1 : Fin (3 : ℕ))
            true) (P (2 : Fin (3 : ℕ)) false)) → ((TouchingTriple (S (1 : Fin (3 : ℕ)) false) (P
            (1 : Fin (3 : ℕ)) false) (P (2 : Fin (3 : ℕ)) true)) → (
        let O := Q 0 false
        let u := BandVectors.1 (q 0) (q 1)
        let v := BandVectors.1 (q 0) (q 2)
        let L := AddSubgroup.closure ({u, v} : Set GaussianInt)
        (BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) ∈ TilingLattice C₀) →
            ((BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) ∈ TilingLattice C₀) → ((∀
            (w : ↥(TilingLattice C₀)), ∃! mn : ℤ × ℤ, (↑mn.1 : GaussianInt) * BandVectors.1 (q (1
            : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) + (↑mn.2 : GaussianInt) * BandVectors.1 (q (2 :
            Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) = (↑w : GaussianInt)) → ((BandVectors.1 (q (0 :
            Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) ∈ AddSubgroup.closure
            {BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))),
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))}) → ((BandVectors.1 (q (0 :
            Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) ∈ AddSubgroup.closure
            {BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))),
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))}) → ((∀ (z : GaussianInt),
            z ∈ AddSubgroup.closure {BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))),
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))} ↔ ∃ w ∈ TilingLattice C₀,
            z = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * w) → ((∀ (w : ↥(AddSubgroup.closure
            {BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))),
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))})), ∃! mn : ℤ × ℤ, (↑mn.1 :
            GaussianInt) * BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) + (↑mn.2 :
            GaussianInt) * BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))) = (↑w :
            GaussianInt)) → (∀ (R : Finset GaussianInt), (LatticeFundamentalSet
            (AddSubgroup.closure {BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))),
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ)))}) R) → ((R.card =
            C₀.1.1.1.natAbs) → (∀ (K : BandUnmodifiedCoreCertificate P u v L), (K.core.rho
            ((K.faceEquiv.symm : PeriodicSubtileFaceIndex → K.core.plane.Face)
            (⟨SixSubtileFaceLabel.I1, (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileFaceIndex)) ∈
            FootprintVertices (Q (1 : Fin (3 : ℕ)) true) ∩ FootprintVertices (S (2 : Fin (3 : ℕ))
            false)) → ((K.core.rho ((K.faceEquiv.symm : PeriodicSubtileFaceIndex →
            K.core.plane.Face) (⟨SixSubtileFaceLabel.I2, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex)) ∈ FootprintVertices (Q (2 : Fin (3 : ℕ)) true) ∩
            FootprintVertices (S (1 : Fin (3 : ℕ)) false)) → ((K.core.rho ((K.faceEquiv.symm :
            PeriodicSubtileFaceIndex → K.core.plane.Face) (⟨SixSubtileFaceLabel.I3, (0 : ℤ), (0 :
            ℤ)⟩ : PeriodicSubtileFaceIndex)) ∈ FootprintVertices (Q (1 : Fin (3 : ℕ)) true) ∩
            FootprintVertices (P (1 : Fin (3 : ℕ)) true)) → ((TileArea (TileCellComplement (P (0
            : Fin (3 : ℕ)) true) O) + TileArea (P (0 : Fin (3 : ℕ)) false) + TileArea (P (1 : Fin
            (3 : ℕ)) true) + TileArea (P (1 : Fin (3 : ℕ)) false) + TileArea (P (2 : Fin (3 : ℕ))
            true) + TileArea (P (2 : Fin (3 : ℕ)) false) = R.card) → ((∀ (x : LatticeCell), ∃! o
            : PeriodicSubtileIndex, x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v
            o).cells) → ((LatticeTile (TileCellComplement (P 0 false) O) ∧ TileTouching
            (TileCellComplement (P 0 false) O) O) → (∀ [Nonempty (PrecursorBoundaryArcData
            (TileCellComplement (P (0 : Fin (3 : ℕ)) true) (Q (0 : Fin (3 : ℕ)) false))
            (TileCellComplement (P (0 : Fin (3 : ℕ)) false) O) (Q (0 : Fin (3 : ℕ)) false) (S (0
            : Fin (3 : ℕ)) true) (Q (1 : Fin (3 : ℕ)) true) (S (2 : Fin (3 : ℕ)) false) (Q (2 :
            Fin (3 : ℕ)) true) (S (1 : Fin (3 : ℕ)) false))], ((Q (0 : Fin (3 : ℕ)) false).cells
            = ∅ → (cfg.firstPredecessor (1 : Fin (4 : ℕ))).1 = (0 : ℤ)) → ((∀ m n : Int, ∀ x ∈
            FootprintVertices (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v)), ∀ a : GaussianInt, x ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) → a ∈
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells ∨ a ∈
            (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells) →
            ((ExceptionalConnectorSegments (P (0 : Fin (3 : ℕ)) true) (P (0 : Fin (3 : ℕ)) false)
            O (Q (1 : Fin (3 : ℕ)) true) (S (2 : Fin (3 : ℕ)) false) (Q (2 : Fin (3 : ℕ)) true)
            (S (1 : Fin (3 : ℕ)) false) (K.core.rho ((K.faceEquiv.symm : PeriodicSubtileFaceIndex
            → K.core.plane.Face) (⟨SixSubtileFaceLabel.I1, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) (K.core.rho ((K.faceEquiv.symm : PeriodicSubtileFaceIndex →
            K.core.plane.Face) (⟨SixSubtileFaceLabel.I2, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex)))) → (∀ (M : PeriodicTileComplex PeriodicSubtileIndex),
            (M.lattice = L) → ((∀ (o : PeriodicSubtileIndex), M.tile o =
            ModifiedSubtileOccurrenceInterpretation P O u v o) → ((∀ (a : PeriodicSubtileIndex),
            ∀ (b : PeriodicSubtileIndex), M.plane.adjacent a b ↔ AllowedSubtileIncidence a b) →
            (∀ (me : M.plane.Face ≃ PeriodicSubtileFaceIndex), (∀ (f : PeriodicSubtileFaceIndex),
            M.rho ((me.symm : PeriodicSubtileFaceIndex → M.plane.Face) f) = K.core.rho
            ((K.faceEquiv.symm : PeriodicSubtileFaceIndex → K.core.plane.Face) f)) → ((∀ (f :
            M.plane.Face), ∀ (i : Fin (3 : ℕ)), M.plane.faceVertex f i = SixSubtileFaceVertices
            ((me : M.plane.Face → PeriodicSubtileFaceIndex) f) i) → ((∀ (f : M.plane.Face), f ∈
            M.faceOrbitReps ↔ ((me : M.plane.Face → PeriodicSubtileFaceIndex) f).first = (0 : ℤ)
            ∧ ((me : M.plane.Face → PeriodicSubtileFaceIndex) f).second = (0 : ℤ)) → (Nonempty
            (BandOrderedGeneralLayoutCertificate q cfg C₀
            T))))))))))))))))))))))))))))))))))))))))))))) ) := by
  classical
  intro q cfg C₀ hC₀ T hsmallT2 smallParent P hP hPunion Q hQ hQunion S hS hSunion pdisks compQ
      houter hcommon hanchor crossO1 crossO2 cross1 cross2 cross3 cross4 O u v L hin1 hin2
      hincoords hu hv hrot hcoords R hfund hcount K point1 point2 point3 harea hpartition compB
      arcs zero periodicIsolation segments M mlattice mtiles madj me mpoints mvertices mreps
  exact ⟨{
    child_eq := hC₀
    P := P
    Q := Q
    S := S
    O := O
    outer_occurrence := hP
    outer_union := hPunion
    parent_lattice := pdisks
    parent_quarter_turn := fun i s => hsmallT2 _ _ (hP i s).1 (smallParent i)
    plus_occurrence := hQ
    plus_union := hQunion
    minus_occurrence := hS
    minus_union := hSunion
    precursor_eq := rfl
    precursor_cells := hcommon
    precursor_anchor := hanchor
    precursor_complement_lattice := ⟨compQ.1, compB.1⟩
    u := u
    v := v
    period_u := rfl
    period_v := rfl
    L := L
    lattice_eq := rfl
    incoming_mem_first := hin1
    incoming_mem_second := hin2
    incoming_coordinates := hincoords
    lattice_rotation := hrot
    period_u_mem := hu
    period_v_mem := hv
    lattice_coordinates := hcoords
    R := R
    fundamental := hfund
    representative_count := hcount
    unmodified := K
    inner_first := point1
    inner_second := point2
    inner_third := point3
    double_first := cross1
    double_second := cross2
    double_third := cross3
    double_fourth := cross4
    outer_touching := houter
    precursor_first := crossO1
    precursor_second := crossO2
    precursorBoundary := Classical.choice arcs
    precursor_zero_curvature := zero
    exceptionalSegments := segments
    connector := segments.connector
    connector_segmented := rfl
    connector_nodup := segments.connector_nodup
    connector_head := segments.connector_head
    connector_last := segments.connector_last
    connector_raw := segments.connector_raw
    connector_edges := segments.connector_edges
    connector_support := segments.connector_support
    orbit_area := harea
    partition := hpartition
    modified := M
    modified_lattice := mlattice
    modified_tile := mtiles
    modified_adjacency := madj
    modifiedFaceEquivalence := me
    modified_face_points := mpoints
    modified_face_vertices := mvertices
    modified_face_reps := mreps
    precursor_isolated := periodicIsolation }⟩

end OrderedLayoutCertificate

theorem BandOrderedGeneralLayout
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (hC₀ : q 0 = C₀.1.1)
    (T : ProtoTile) (hT : BandPrototile (q 0) T)
    (hsmallT1 : ∀ (q' : Fin 4 → CircleCoordinates) (T' : ProtoTile)
      (S' : Fin 3 → Bool → ProtoTile), ProperBandQuadruple q' →
      BandPrototile (q' 0) T' →
      (∀ i s, BandSubtileOccurrence q' T' i s (S' i s)) →
      (∀ x, x ∈ T'.cells ↔ ∃ i s, x ∈ (S' i s).cells) →
      Int.toNat (q' 0).1 < Int.toNat (q 0).1 →
      LatticeTile T' ∧ TileArea T' = Int.toNat (q' 0).1 ∧
        ∀ i s, LatticeTile (TileCellComplement T' (S' i s)) ∧
          TileTouching (TileCellComplement T' (S' i s)) (S' i s))
    (hsmallT2 : ∀ (D : CircleCoordinates) (U : ProtoTile),
      BandPrototile D U → Int.toNat D.1 < Int.toNat (q 0).1 →
      QuarterTurnSymmetric U)
    (hsmallT4 : ∀ (q' : Fin 4 → CircleCoordinates)
      (T' U : ProtoTile), ProperBandQuadruple q' →
      BandPrototile (q' 0) T' →
      Int.toNat (q' 0).1 < Int.toNat (q 0).1 → 1 < (q' 0).1 →
      ∀ i : Fin 3, BandPrototile (q' i.succ) U →
      TileCentroid U - TileCentroid T' = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q' i.succ) (q' 0)) +
          GaussianRealPoint (BandVectors.1 (q' 0) (q' i.succ))) →
      TouchingTriple T'
        (TileTranslation T' (BandVectors.1 (q' i.succ) (q' 0))) U)
    (hsmallT5 : ∀ (q' : Fin 4 → CircleCoordinates)
      (T' U V : ProtoTile), ProperBandQuadruple q' →
      BandPrototile (q' 0) T' →
      Int.toNat (q' 0).1 < Int.toNat (q 0).1 →
      ∀ i : Fin 3, BandPrototile (q' i.succ) U →
      BandPrototile (q' ((i + 1).succ)) V →
      TileCentroid U - TileCentroid T' = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q' i.succ) (q' 0)) +
          GaussianRealPoint (BandVectors.1 (q' 0) (q' i.succ))) →
      TileCentroid V - TileCentroid T' = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q' ((i + 1).succ)) (q' 0)) -
          GaussianRealPoint (BandVectors.1 (q' 0) (q' ((i + 1).succ)))) →
      TouchingTriple T' U V) :
    Nonempty (BandOrderedGeneralLayoutCertificate q cfg C₀ T) := by
-- BODY
  classical
  have hn := (SemiProperForestClassification q cfg.proper.1).1
  have hqpos : 0 < (q 0).1 := by have := cfg.childLarge; omega
  have smallParent (i : Fin 3) : (q i.succ).1.toNat < (q 0).1.toNat :=
    (Int.toNat_lt_toNat hqpos).mpr (cfg.proper.2 i)
  have parentPos (i : Fin 3) : 0 < (q i.succ).1 :=
    lt_of_le_of_ne (hn i.succ) (Ne.symm (cfg.noLine i.succ))
  have rsmall : (cfg.firstPredecessor 0).1.toNat < (q 0).1.toNat :=
    (Int.toNat_lt_toNat hqpos).mpr cfg.firstSmaller
  have rparents (i : Fin 3) :
      (cfg.firstPredecessor i.succ).1.toNat < (q 0).1.toNat :=
    (Int.toNat_lt_toNat hqpos).mpr ((cfg.firstProper.2 i).trans cfg.firstSmaller)
  have smaller (c : CircleCoordinates) (U : ProtoTile)
      (hU : BandPrototile c U) (hlt : c.1.toNat < (q 0).1.toNat) :=
    P4670T1SmallerGeometry (q 0).1.toNat
      (fun p V S hp hv hs hc hl => (hsmallT1 p V S hp hv hs hc hl).imp_right
        (fun h => h.1)) c U hU hlt
  obtain ⟨P, hP, hPunion⟩ := BandPrototileReindexedDecomposition q cfg.proper T hT
  have hPr (s : Bool) := OrderedLayoutGeometry.hPr q cfg T P hP s
  obtain ⟨Q, hQ, hQunion⟩ := BandPrototileReindexedDecomposition
    cfg.firstPredecessor cfg.firstProper (P 0 true) (hPr true)
  obtain ⟨S, hS, hSunion⟩ := BandPrototileReindexedDecomposition
    cfg.firstPredecessor cfg.firstProper (P 0 false) (hPr false)
  have hQcells (i : Fin 3) (s : Bool) := OrderedLayoutGeometry.hQcells P Q hQunion i s
  have hScells (i : Fin 3) (s : Bool) : (S i s).cells ⊆ (P 0 false).cells :=
      OrderedLayoutGeometry.hScells P S hSunion i s
  have pg (i : Fin 3) (s : Bool) := smaller _ _ (hP i s).1 (smallParent i)
  have pdisks (i : Fin 3) (s : Bool) : LatticeTile (P i s) :=
    (pg i s).2.2 (parentPos i)
  have parea (i : Fin 3) (s : Bool) : TileArea (P i s) = (q i.succ).1.toNat :=
    (pg i s).2.1
  have pne (i : Fin 3) (s : Bool) := OrderedLayoutGeometry.pne q cfg parentPos P parea i s
  have compQ := (hsmallT1 cfg.firstPredecessor (P 0 true) Q cfg.firstProper
    (hPr true) hQ hQunion rsmall).2.2 0 false
  have compS := (hsmallT1 cfg.firstPredecessor (P 0 false) S cfg.firstProper
    (hPr false) hS hSunion rsmall).2.2 0 true
  have qg (i : Fin 3) (s : Bool) := smaller _ _ (hQ i s).1 (rparents i)
  have sg (i : Fin 3) (s : Bool) := smaller _ _ (hS i s).1 (rparents i)
  have rpPos (i : Fin 3) (hi : i = 1 ∨ i = 2) := OrderedLayoutGeometry.rpPos q cfg parentPos i hi
  have qne (i : Fin 3) (s : Bool) (hi : i = 1 ∨ i = 2) := OrderedLayoutGeometry.qne q cfg Q qg
      rpPos i s hi
  have sne (i : Fin 3) (s : Bool) (hi : i = 1 ∨ i = 2) := OrderedLayoutGeometry.sne q cfg S sg
      rpPos i s hi
  have oriented (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
      (hlt : (p 0).1 < (q 0).1) (hlarge : 1 < (p 0).1) := OrderedLayoutGeometry.oriented q
          hsmallT2 hsmallT4 hsmallT5 hqpos p hp hlt hlarge
  have oriR := oriented cfg.firstPredecessor cfg.firstProper cfg.firstSmaller
      (OrderedLayoutGeometry.rlarge q cfg)
  have oriT := oriented cfg.secondPredecessor cfg.secondProper cfg.secondSmaller
      (OrderedLayoutGeometry.tlarge q cfg)
  have outer := OuterLayoutTouching q cfg.firstPredecessor cfg.secondPredecessor
    cfg.proper cfg.firstProper cfg.secondProper cfg.firstChild cfg.firstParentTwo
    cfg.firstParentThree cfg.secondChild cfg.secondParentOne cfg.firstSmaller
    cfg.secondSmaller oriR.1 oriR.2 oriT.1 oriT.2 (TileCentroid T) P
    (fun i s => (hP i s).1) (fun i s => (hP i s).2.2)
  have nonunitA := OrderedLayoutGeometry.nonunitA q cfg P parea
  have nonunitC := OrderedLayoutGeometry.nonunitC q cfg P parea
  have reject (A B C : ProtoTile) (h : OuterTouchingAlternative A B C)
      (ha : TileArea A ≠ 1) : TouchingTriple A B C :=
    h.resolve_right (fun h => ha h.1)
  have houter := And.intro (reject _ _ _ outer.1 nonunitA)
    (And.intro (reject _ _ _ outer.2.1 nonunitA)
    (And.intro (reject _ _ _ outer.2.2.1 nonunitA)
    (And.intro (reject _ _ _ outer.2.2.2.1 nonunitA)
    (And.intro (reject _ _ _ outer.2.2.2.2.1 nonunitA)
    (And.intro (reject _ _ _ outer.2.2.2.2.2.1 (OrderedLayoutGeometry.nonunitB q cfg P parea))
    (And.intro (reject _ _ _ outer.2.2.2.2.2.2.1 nonunitC)
      (reject _ _ _ outer.2.2.2.2.2.2.2 nonunitC)))))))
  obtain ⟨hcommon, hanchor, crossO1, crossO2, cross1, cross2, cross3, cross4⟩ :=
    BandDoubleDecomposition q cfg.firstPredecessor cfg.secondPredecessor cfg.proper
      cfg.firstProper cfg.secondProper cfg.firstChild cfg.firstParentTwo
      cfg.firstParentThree cfg.secondChild cfg.secondParentOne cfg.order12
      cfg.secondLarge cfg.order23 cfg.secondSmaller hsmallT2 hsmallT5
      (fun V U s => oriT.1 V U 0 s) (TileCentroid T) P Q S
      (fun i s => (hP i s).1) (fun i s => (hQ i s).1) (fun i s => (hS i s).1)
      (fun i s => (hP i s).2.2) (fun i s => (hQ i s).2.2)
      (fun i s => (hS i s).2.2)
  let O := Q 0 false
  have hOA : O.cells ⊆ (P 0 true).cells := hQcells 0 false
  have hOB : O.cells ⊆ (P 0 false).cells := by rw [hcommon]; exact hScells 0 true
  have Odisk := OrderedLayoutGeometry.Odisk q cfg Q qg
  let u := BandVectors.1 (q 0) (q 1)
  let v := BandVectors.1 (q 0) (q 2)
  let L := AddSubgroup.closure ({u, v} : Set GaussianInt)
  obtain ⟨hin1, hin2, hincoords, hu, hv, hrot, hcoords, R, hfund, hcount⟩ :=
    TilingLatticeBasis C₀ q cfg.proper hC₀
  obtain ⟨K, point1, point2, point3⟩ := BandUnmodifiedPeriodicCore P Q S u v L R
    hu hv hfund hcoords pdisks hQcells hScells
    (fun i s => (hQ i s).2.1) (fun i s => (hS i s).2.1)
    hcommon hanchor Odisk ⟨crossO1, crossO2⟩ ⟨cross1, cross2, cross3, cross4⟩ houter
  have hcover := BandModifiedCoverage P O u v L K hOB
  have harea := BandModifiedOrbitArea P O R (q 0).1.toNat (q 1).1.toNat
    (q 2).1.toNat (q 3).1.toNat (cfg.firstPredecessor 1).1.toNat hOA
    (parea 0 true) (parea 0 false) (parea 1 true) (parea 1 false)
    (parea 2 true) (parea 2 false) (qg 0 false).2.1 cfg.soddyNat (OrderedLayoutGeometry.hindex q
        cfg C₀ hC₀ hn R hcount)
  have hpartition := BandModifiedCellPartition P O u v L R hu hv hfund hcoords hcover harea
  have hsep := BandOriginalPairSeparation P O u v hOA hOB hpartition
  have compEq : TileCellComplement (P 0 false) (S 0 true) =
      TileCellComplement (P 0 false) O := OrderedLayoutGeometry.compEq P Q S hcommon
  have sameObs := ProtoTileObservableExtensionality (Q 0 false) (S 0 true) hcommon hanchor
  have compB := OrderedLayoutGeometry.compB P Q S compS compEq (OrderedLayoutGeometry.sameTouch Q
      S hcommon hanchor sameObs)
  have central : CentrallyReflectedAt (TileCentroid O)
      (TileCellComplement (P 0 true) O) (TileCellComplement (P 0 false) O) :=
          OrderedLayoutGeometry.central q cfg T P hP Q hQ pne (OrderedLayoutGeometry.ocenter q
              cfg T P hP Q hQ)
  have osym : QuarterTurnSymmetric O := hsmallT2 _ _ (hQ 0 false).1 (rparents 0)
  obtain ⟨isolated, arcs, zero⟩ := IsolatedPrecursorCoverage q cfg.firstPredecessor
    cfg.proper cfg.firstProper cfg.firstChild cfg.firstParentTwo cfg.firstParentThree
    (TileCentroid T) P Q S (fun i s => (hP i s).1) (fun i s => (hQ i s).1)
    (fun i s => (hS i s).1) (fun i s => (hP i s).2.2) (fun i s => (hQ i s).2.2)
    (fun i s => (hS i s).2.2) hQcells hScells (fun i s => (hQ i s).2.1)
    (fun i s => (hS i s).2.1) hcommon hanchor compQ compS
    (by rw [compEq]; exact central) osym
    (fun ho => Odisk (Finset.nonempty_iff_ne_empty.mpr ho))
    (qne 1 true (Or.inl rfl)).ne_empty (sne 2 false (Or.inr rfl)).ne_empty
    (qne 2 true (Or.inr rfl)).ne_empty (sne 1 false (Or.inl rfl)).ne_empty
    crossO1 crossO2 cross1 cross3 (fun h => nonunitC h.2) (OrderedLayoutGeometry.compDisjoint q P
        Q S hsep)
  rw [compEq] at arcs
  have periodicIsolation := OrderedLayoutGeometry.periodicIsolation q P Q isolated
  have ordinary := P4670T1OrdinaryEdges P u v pne (Q 1 true) (S 1 false)
    (qne 1 true (Or.inl rfl)) (sne 1 false (Or.inl rfl))
    (hQcells 1 true) (hScells 1 false) cross3.1 cross4.1 houter
  have abEdge := OrderedLayoutGeometry.abEdge q cfg C₀ P hPr Q hQ S hS compQ hOB R sameObs zero
      (OrderedLayoutGeometry.diskNonempty) (OrderedLayoutGeometry.touchEdge
          (OrderedLayoutGeometry.boundaryEdge)) (OrderedLayoutGeometry.edgeMono)
  obtain ⟨segments⟩ := ExceptionalModifiedABPath (P 0 true) (P 0 false) O (S 0 true)
    (Q 1 true) (S 2 false) (Q 2 true) (S 1 false) _ _ hOA hOB
    (hQcells 1 true) (hScells 2 false) (hQcells 2 true) (hScells 1 false)
    (qne 1 true (Or.inl rfl)) (sne 2 false (Or.inr rfl))
    (qne 2 true (Or.inr rfl)) (sne 1 false (Or.inl rfl)) crossO1 crossO2 point1 point2
    compQ.2 compB.2 central osym isolated arcs
    (OrderedLayoutGeometry.commonVertices P Q abEdge OrderedLayoutGeometry.edgeVertex)
  obtain ⟨M, mlattice, mtiles, madj, me, mpoints, mvertices, mreps⟩ :=
    BandModifiedPeriodicComplex P O u v L K (OrderedLayoutGeometry.modifiedDisks q P Q pdisks
        compQ) hpartition hOA hOB
      (harea.trans (OrderedLayoutGeometry.repCard q P R hfund K).symm) periodicIsolation ordinary
          abEdge
      ⟨segments.connector, segments.connector_head, segments.connector_last,
        segments.connector_raw, segments.connector_edges⟩
  have layoutCertificate :
    Nonempty (BandOrderedGeneralLayoutCertificate q cfg C₀ T) :=
        OrderedLayoutCertificate.layoutCertificate q cfg C₀ hC₀ T hsmallT2 smallParent P hP
        hPunion Q hQ hQunion S hS hSunion pdisks compQ houter hcommon hanchor crossO1 crossO2
        cross1 cross2 cross3 cross4 hin1 hin2 hincoords hu hv hrot hcoords R hfund hcount K
        point1 point2 point3 harea hpartition compB  zero periodicIsolation
        segments M mlattice mtiles madj me mpoints mvertices mreps
  exact layoutCertificate


end ApollonianSuperharmonic

end
