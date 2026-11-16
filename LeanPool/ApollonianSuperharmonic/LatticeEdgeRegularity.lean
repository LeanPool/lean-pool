/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandCircle
public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.CurvatureOneBandPrototileSingleton
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.OpenLatticeEdge
public import LeanPool.ApollonianSuperharmonic.P4456T2DiamondNoChord
public import LeanPool.ApollonianSuperharmonic.P4456T2MissingEdge
public import LeanPool.ApollonianSuperharmonic.P4456T2OrderedNoChord
public import LeanPool.ApollonianSuperharmonic.P4456T2PackingNoChord

-- [TABLET NODE: LatticeEdgeRegularity]

/-!
# LatticeEdgeRegularity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem LatticeEdgeRegularity (C : BandCircle) (T : ProtoTile)
    (hT : BandPrototile C.1.1 T) (hlat : LatticeTile T) :
    (∀ x y, FourNeighborAdjacent x y →
      x ∈ BoundaryFootprintVertices T → y ∈ BoundaryFootprintVertices T →
      ¬ OpenLatticeEdge x y ⊆ interior (TileRealization T)) ∧
    (∀ x, x ∈ FootprintVertices T → ∀ y, y ∈ FootprintVertices T →
      FourNeighborAdjacent x y → ({x, y} : Finset GaussianInt) ∈ FootprintEdges T) ∧
    ∀ x, x ∈ FootprintVertices T →
      (GaussianRealPoint x ∈ interior (TileRealization T) ↔
        x ∉ BoundaryFootprintVertices T) := by
-- BODY
  classical
  have uniform : ∀ n : Nat, ∀ (D : CircleCoordinates) (U : ProtoTile),
      Int.toNat D.1 = n → 0 < D.1 → BandPrototile D U → LatticeTile U →
      ∀ x y, FourNeighborAdjacent x y →
        x ∈ BoundaryFootprintVertices U → y ∈ BoundaryFootprintVertices U →
        ¬ OpenLatticeEdge x y ⊆ interior (TileRealization U) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro D U hn hpositive hproto hdisk
      cases hproto with
      | line w a hw => simp at hpositive
      | unit z a anchor =>
        exact (P4456T2SquareEdges 1 (by omega) a ⟨{a}, anchor⟩
          (by simp [FordTile, FordCellDomain, TileTranslation, GaussianTranslation,
            Zsqrtd.ext_iff])).1
      | @decompose q hq S U hS hunion hfoot hcent =>
        have hchild : BandPrototile (q 0) U :=
          BandPrototile.decompose hq hS hunion hfoot hcent
        obtain ⟨r, g, hregime⟩ := BandRegimeClassification q hq
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let q' := BandPackingSymmetryQuadrupleAction g qr
        let U' := BandPackingSymmetryTileAction g U
        have hrot : ProperBandQuadruple qr :=
          (BandParentRotationOccurrenceCovariance q hq r U hchild S
            (fun i s => ⟨hS i s, hfoot i s, hcent i s⟩) hunion).1
        have hproper : ProperBandQuadruple q' :=
          BandPackingSymmetryProperCovariance g qr hrot
        have hzero : q' 0 = BandPackingSymmetryCircleAction g (q 0) := by
          simp [q', qr, BandPackingSymmetryQuadrupleAction]
        have hcurv : (q' 0).1 = (q 0).1 := by
          rw [hzero]
          exact (BandPackingSymmetryCovariance g).1 _
        have hproto' : BandPrototile (q' 0) U' := by
          rw [hzero]
          exact ((BandPackingSymmetryCovariance g).2.1 _ _).mp hchild
        have hdisk' : LatticeTile U' :=
          ((BandPackingSymmetryTilingTransport g).1 U).mp hdisk
        apply (P4456T2PackingNoChord g U).mpr
        change (∀ x y, FourNeighborAdjacent x y →
          x ∈ BoundaryFootprintVertices U' → y ∈ BoundaryFootprintVertices U' →
          ¬ OpenLatticeEdge x y ⊆ interior (TileRealization U'))
        change Xor (∃ P : FordFareyParameter, 1 < P.q ∧ q' = FordRecursiveQuadruple P)
          (Xor (∃ K : DiamondParameter, 1 < K.1 ∧ q' = DiamondRecursiveQuadruple K)
            (Nonempty (BandOrderedGeneralConfiguration q'))) at hregime
        rcases hregime with ⟨⟨P, hP, heq⟩, _⟩ | ⟨hrest, _⟩
        · have hcanonical : BandPrototile (q' 0) (FordTile P.q) := by
            simpa [heq, FordRecursiveQuadruple] using
              (FordTileRecursiveIdentification P).1
          obtain ⟨w, hw, _⟩ := BandPrototileTranslationNormalForm _ U'
            (FordTile P.q) hproto' hcanonical
          exact (P4456T2SquareEdges P.q (by omega) w U' hw).1
        · rcases hrest with ⟨⟨K, hK, heq⟩, _⟩ | ⟨⟨cfg⟩, _⟩
          · have hcanonical : BandPrototile (q' 0) (DiamondTile K.1) := by
              simpa [heq] using (DiamondTileRecursiveIdentification K).1
            obtain ⟨w, hw, _⟩ := BandPrototileTranslationNormalForm _ U'
              (DiamondTile K.1) hproto' hcanonical
            exact P4456T2DiamondNoChord K.1 (by omega) w U' hw
          · have hpos' : 0 < (q' 0).1 := (ProperBandCurvatureStructure q' hproper).1
            let C' : BandCircle :=
              ⟨⟨q' 0, Or.inl hpos', ⟨q', hproper.1, 0, rfl⟩⟩, hpos'⟩
            obtain ⟨layout⟩ := BandOrderedGeneralLayout q' cfg C' rfl U' hproto'
              (by
                intro p V W hp hV hW hcover _
                have h := BandTileSimultaneousInduction p hp V hV
                exact ⟨h.1, h.2.1, h.2.2.1 W hW hcover⟩)
              (by
                intro E V hV _
                cases hV with
                | line w a hw => simp [QuarterTurnSymmetric, TileRealization]
                | unit z a anchor =>
                  intro p
                  simp only [TileRealization, Finset.mem_singleton,
                    Set.iUnion_iUnion_eq_left]
                  have hc : TileCentroid (⟨{a}, anchor⟩ : ProtoTile) =
                      ((a.re : Real) + 1 / 2, (a.im : Real) + 1 / 2) := by
                    simp [TileCentroid]
                  simp only [hc, ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
                  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;>
                    constructor <;> constructor <;> dsimp at * <;> linarith
                | @decompose p hp W V hW hu hf hc =>
                  exact (BandTileSimultaneousInduction p hp V
                    (BandPrototile.decompose hp hW hu hf hc)).2.2.2.1)
              (by
                intro p V W hp hV _ hlarge i hW hc
                exact (BandTileSimultaneousInduction p hp V hV).2.2.2.2.2.1
                  hlarge i W hW hc)
              (by
                intro p V W Z hp hV _ i hW hZ hc hd
                exact (BandTileSimultaneousInduction p hp V hV).2.2.2.2.2.2.1
                  i W Z hW hZ hc hd)
            apply P4456T2OrderedNoChord q' cfg C' U' hdisk' layout
            intro i s
            have hnonneg := (ProperBandCurvatureStructure q' hproper).2.1 i
            have hnonzero := cfg.noLine i.succ
            have hparentpos : 0 < (q' i.succ).1 := by omega
            have hless : Int.toNat (q' i.succ).1 < n := by
              have hh := hproper.2 i
              rw [hcurv] at hh
              omega
            exact ih _ hless _ _ rfl hparentpos
              (layout.outer_occurrence i s).1 (layout.parent_lattice i s)
  have hno := uniform _ C.1.1 T rfl C.2 hT hlat
  refine ⟨hno, ?_, ?_⟩
  · by_cases hunit : C.1.1.1 = 1
    · obtain ⟨a, ha⟩ := CurvatureOneBandPrototileSingleton C T hunit hT
      have hz : (⟨0, 0⟩ : GaussianInt) = 0 := by ext <;> rfl
      exact (P4456T2SquareEdges 1 (by omega) a T
        (by simpa [FordTile, FordCellDomain, TileTranslation, GaussianTranslation,
            hz]
          using ha)).2
    · rcases BandGenealogy C with hc | ⟨q, hq, hqC, hsmall, _⟩
      · exact (hunit hc).elim
      have hp : ProperBandQuadruple q := ⟨hq, by simpa [hqC] using hsmall⟩
      have hproto : BandPrototile (q 0) T := by simpa [hqC] using hT
      have hlarge : 1 < (q 0).1 := by rw [hqC]; have := C.2; omega
      apply P4456T2MissingEdge C q hp hqC T hproto hlarge
      intro u
      exact uniform _ C.1.1 (TileTranslation T (u : GaussianInt)) rfl C.2
        (BandPrototileTranslation _ T _ hT) ((TileDiskAreaCovariance T u).1.mp hlat)
  · intro x hx
    have hne := (LatticeTileFourNeighborConnected T hlat).1
    have hlocal := P4456T2VertexInterior T hne x hx
    exact hlocal.1.trans hlocal.2.symm

end ApollonianSuperharmonic

end
