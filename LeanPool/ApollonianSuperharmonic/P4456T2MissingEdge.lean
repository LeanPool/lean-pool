/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.LatticeFootprintIncidence
public import LeanPool.ApollonianSuperharmonic.BandPrototileNonempty
public import LeanPool.ApollonianSuperharmonic.TileTranslationProperties

public import LeanPool.ApollonianSuperharmonic.P4456T2BandGraphTriangle
public import LeanPool.ApollonianSuperharmonic.BandRegularTranslatePeriodicComplex
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent

-- [TABLET NODE: P4456T2MissingEdge]

/-!
# P4456T2MissingEdge

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace MissingEdgeGeometry

private theorem adjacent_ne (x y : GaussianInt) (hxy : FourNeighborAdjacent x y) : x ≠ y := by
  intro heq
  subst y
  simp only [FourNeighborAdjacent] at hxy
  rcases hxy with h | h | h | h
  · have hr := congrArg Zsqrtd.re h
    simp only [Zsqrtd.re_add, Zsqrtd.re_one] at hr
    omega
  · have hr := congrArg Zsqrtd.re h
    simp only [Zsqrtd.re_sub, Zsqrtd.re_one] at hr
    omega
  · have hi := congrArg Zsqrtd.im h
    simp only [Zsqrtd.im_add] at hi
    omega
  · have hi := congrArg Zsqrtd.im h
    simp only [Zsqrtd.im_sub] at hi
    omega

private theorem hzwT :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (z : GaussianInt), ∀ (w :
            GaussianInt), (∀ (U : ProtoTile), ({x, y} ∈ FootprintEdges U ↔ z ∈ U.cells ∨ w ∈
            U.cells) ∧ ({x, y} ∈ BoundaryFootprintEdges U ↔ z ∈ U.cells ∧ w ∉ U.cells ∨ z ∉
            U.cells ∧ w ∈ U.cells) ∧ (z ∈ U.cells ∨ w ∈ U.cells → x ∈ FootprintVertices U ∧ y ∈
            FootprintVertices U ∧ ∀ (t : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (((1 : ℝ) - (↑t :
            ℝ)) * (↑x.re : ℝ) + (↑t : ℝ) * (↑y.re : ℝ), ((1 : ℝ) - (↑t : ℝ)) * (↑x.im : ℝ) + (↑t
            : ℝ) * (↑y.im : ℝ)) ∈ TileRealization U) ∧ (z ∈ U.cells ∧ w ∈ U.cells →
            OpenLatticeEdge x y ⊆ interior (TileRealization U)) ∧ ((∀ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ U.cells) → z ∈ U.cells ∧ w ∈ U.cells)) → ((({x, y} :
            Finset GaussianInt) ∉ FootprintEdges T) → (z ∉ T.cells ∧ w ∉ T.cells)) ) := by
  classical
  intro T x y z w hedgeFacts hedgeT
  have hh : ¬ (z ∈ T.cells ∨ w ∈ T.cells) := fun h =>
    hedgeT ((hedgeFacts T).1.mpr h)
  exact not_or.mp hh

private abbrev incident_of_footprint :=
    ApollonianSuperharmonic.LatticeFootprintIncidence.incidentCell

private theorem hmissingA :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)),
            (P.tile 0 = T) → ((∀ (x : LatticeCell), ∃! a : ↥(TilingLattice C), x ∈ (P.tile
            a).cells) → (∀ (a : ↥(TilingLattice C)), (a ≠ 0) → ((∀ (U : ProtoTile), ∀ (v :
            GaussianInt), (U.cells.Nonempty) → ((v ∈ FootprintVertices U) → (∃ j : Fin 4,
            LatticeVertexIncidentCell v j ∈ U.cells))) → ((T.cells.Nonempty) → (∀ (v :
            GaussianInt), (v ∈ FootprintVertices T) → (∃ j : Fin 4, LatticeVertexIncidentCell v j
            ∉ (P.tile a).cells)))))) ) := by
  classical
  intro C T P hzero hindexed a ha0 incident_of_footprint hTne v hv
  obtain ⟨j, hj⟩ := incident_of_footprint T v hTne hv
  refine ⟨j, ?_⟩
  intro hja
  have hzeroCell : LatticeVertexIncidentCell v j ∈ (P.tile 0).cells := by
    simpa [hzero] using hj
  have heq := (hindexed (LatticeVertexIncidentCell v j)).unique hzeroCell hja
  exact ha0 heq.symm

private theorem habEdge :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), ∀ (x : GaussianInt),
            ∀ (y : GaussianInt), ∀ (z : GaussianInt), ∀ (w : GaussianInt), (∀ (U : ProtoTile),
            ({x, y} ∈ FootprintEdges U ↔ z ∈ U.cells ∨ w ∈ U.cells) ∧ ({x, y} ∈
            BoundaryFootprintEdges U ↔ z ∈ U.cells ∧ w ∉ U.cells ∨ z ∉ U.cells ∧ w ∈ U.cells) ∧
            (z ∈ U.cells ∨ w ∈ U.cells → x ∈ FootprintVertices U ∧ y ∈ FootprintVertices U ∧ ∀ (t
            : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), (((1 : ℝ) - (↑t : ℝ)) * (↑x.re : ℝ) + (↑t :
            ℝ) * (↑y.re : ℝ), ((1 : ℝ) - (↑t : ℝ)) * (↑x.im : ℝ) + (↑t : ℝ) * (↑y.im : ℝ)) ∈
            TileRealization U) ∧ (z ∈ U.cells ∧ w ∈ U.cells → OpenLatticeEdge x y ⊆ interior
            (TileRealization U)) ∧ ((∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈
            U.cells) → z ∈ U.cells ∧ w ∈ U.cells)) → (∀ (a : ↥(TilingLattice C)), ∀ (b :
            ↥(TilingLattice C)), (z ∈ (P.tile a).cells) → ((w ∈ (P.tile b).cells) →
            ((FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty))) ) := by
  classical
  intro C P x y z w hedgeFacts a b hza hwb
  refine ⟨{x, y}, ?_⟩
  constructor
  · exact (hedgeFacts (P.tile a)).1.mpr (Or.inl hza)
  · exact (hedgeFacts (P.tile b)).1.mpr (Or.inr hwb)

private theorem hzeroaEdge :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (P : PeriodicTileComplex ↥(TilingLattice C)), ∀
            (x : GaussianInt), (x ∈ FootprintVertices T) → (∀ (y : GaussianInt), (y ∈
            FootprintVertices T) → ((P.tile 0 = T) → (∀ (a : ↥(TilingLattice C)), (a ≠ 0) → ((x ∈
            FootprintVertices (P.tile a)) → ((y ∈ FootprintVertices (P.tile a)) → ((x ≠ y) → ((∀
            (a : ↥(TilingLattice C)), ∀ (b : ↥(TilingLattice C)), a ≠ b → ((FootprintEdges
            (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty ↔ P.plane.adjacent a b) ∧
            ((FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty → SimpleGridPath
            (CommonFootprintEdgeVertices (P.tile a) (P.tile b)) (FootprintEdges (P.tile a) ∩
            FootprintEdges (P.tile b)) ∧ FootprintVertices (P.tile a) ∩ FootprintVertices (P.tile
            b) = CommonFootprintEdgeVertices (P.tile a) (P.tile b)) ∧ (¬(FootprintEdges (P.tile
            a) ∩ FootprintEdges (P.tile b)).Nonempty → FootprintVertices (P.tile a) ∩
            FootprintVertices (P.tile b) = ∅ ∨ (FootprintVertices (P.tile a) ∩ FootprintVertices
            (P.tile b)).Subsingleton)) → ((FootprintEdges (P.tile 0) ∩ FootprintEdges (P.tile
            a)).Nonempty)))))))) ) := by
  classical
  intro C T P x hx y hy hzero a ha0 hxa hya hneqxy hclass
  by_contra hn
  have hsmall := (hclass 0 a (Ne.symm ha0)).2.2 hn
  rcases hsmall with hempty | hsub
  · have hxI : x ∈ FootprintVertices (P.tile 0) ∩ FootprintVertices (P.tile a) :=
      ⟨by simpa [hzero] using hx, hxa⟩
    simp [hempty] at hxI
  · have hxI : x ∈ FootprintVertices (P.tile 0) ∩ FootprintVertices (P.tile a) :=
      ⟨by simpa [hzero] using hx, hxa⟩
    have hyI : y ∈ FootprintVertices (P.tile 0) ∩ FootprintVertices (P.tile a) :=
      ⟨by simpa [hzero] using hy, hya⟩
    exact hneqxy (hsub hxI hyI)

private abbrev hzerobEdge :=
  ApollonianSuperharmonic.MissingEdgeGeometry.hzeroaEdge

end MissingEdgeGeometry

theorem P4456T2MissingEdge (C : BandCircle)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hqC : q 0 = C.1.1) (T : ProtoTile) (hT : BandPrototile (q 0) T)
    (hlarge : 1 < (q 0).1)
    (hnochord : ∀ u : TilingLattice C, ∀ x y,
      FourNeighborAdjacent x y →
      x ∈ BoundaryFootprintVertices (TileTranslation T (u : GaussianInt)) →
      y ∈ BoundaryFootprintVertices (TileTranslation T (u : GaussianInt)) →
      ¬ OpenLatticeEdge x y ⊆
        interior (TileRealization (TileTranslation T (u : GaussianInt)))) :
    ∀ x, x ∈ FootprintVertices T → ∀ y, y ∈ FootprintVertices T →
      FourNeighborAdjacent x y → ({x, y} : Finset GaussianInt) ∈ FootprintEdges T := by
-- BODY
  obtain ⟨P, hL, htile, hadj, hposition, hvertices, hedges, hfaces, ⟨chart⟩⟩ :=
    BandRegularTranslatePeriodicComplex C q hq hqC T hT
  suffices hlocal :
      (∀ a b c, a ≠ b → b ≠ c → c ≠ a →
        P.plane.adjacent a b → P.plane.adjacent b c → P.plane.adjacent c a →
        TouchingTriple (P.tile a) (P.tile b) (P.tile c)) →
      ∀ x, x ∈ FootprintVertices T → ∀ y, y ∈ FootprintVertices T →
        FourNeighborAdjacent x y →
          ({x, y} : Finset GaussianInt) ∈ FootprintEdges T by
    exact hlocal (P4456T2BandGraphTriangle q hq T hT hlarge P chart)
  intro htriangles
  classical
  intro x hx y hy hxy
  by_contra hnot
  have hzero : P.tile 0 = T := by
    rw [htile 0]
    exact TileTranslationProperties.zero T
  have hindexed := PeriodicTileIndexedMultiplicityOne P
  obtain ⟨z, w, hform⟩ := (P4397T1UnitEdgeCells.1 x y hxy)
  have hedgeFacts := P4397T1UnitEdgeCells.2 x y z w hform
  have hedgeT : ({x, y} : Finset GaussianInt) ∉ FootprintEdges T := hnot
  have hzwT : z ∉ T.cells ∧ w ∉ T.cells := MissingEdgeGeometry.hzwT T x y z w hedgeFacts hedgeT
  obtain ⟨a, ha, _⟩ := hindexed z
  obtain ⟨b, hb, _⟩ := hindexed w
  have notZeroOfCell (u : TilingLattice C) (c : GaussianInt)
      (hnot : c ∉ T.cells) (hmem : c ∈ (P.tile u).cells) : u ≠ 0 := by
    intro heq
    subst u
    exact hnot (by simpa [hzero] using hmem)
  have ha0 : a ≠ 0 := notZeroOfCell a z hzwT.1 ha
  have hb0 : b ≠ 0 := notZeroOfCell b w hzwT.2 hb
  have hza : z ∈ (P.tile a).cells := ha
  have hwb : w ∈ (P.tile b).cells := hb
  have hxa : x ∈ FootprintVertices (P.tile a) := by
    exact ((hedgeFacts (P.tile a)).2.2.1 (Or.inl hza)).1
  have hya : y ∈ FootprintVertices (P.tile a) := by
    exact ((hedgeFacts (P.tile a)).2.2.1 (Or.inl hza)).2.1
  have hxb : x ∈ FootprintVertices (P.tile b) := by
    exact ((hedgeFacts (P.tile b)).2.2.1 (Or.inr hwb)).1
  have hyb : y ∈ FootprintVertices (P.tile b) := by
    exact ((hedgeFacts (P.tile b)).2.2.1 (Or.inr hwb)).2.1
  have incident_of_footprint (U : ProtoTile) (v : GaussianInt)
      (hne : U.cells.Nonempty) (hv : v ∈ FootprintVertices U) :
      ∃ j : Fin 4, LatticeVertexIncidentCell v j ∈ U.cells :=
          MissingEdgeGeometry.incident_of_footprint U v hne hv
  have hnonemptyA : (P.tile a).cells.Nonempty := ⟨z, ha⟩
  have hnonemptyB : (P.tile b).cells.Nonempty := ⟨w, hb⟩
  have hTne : T.cells.Nonempty := BandPrototileNonempty.positive (q 0) T (by omega) hT
  have hmissT (v : GaussianInt) (hv : v = x ∨ v = y) :
      ∃ j : Fin 4, LatticeVertexIncidentCell v j ∉ T.cells := by
    rcases hform with ⟨hor, hw⟩ | ⟨hor, hw⟩
    · rcases hor with ⟨hx0, hy0⟩ | ⟨hy0, hx0⟩
      · rcases hv with rfl | rfl
        · refine ⟨1, ?_⟩
          simpa [LatticeVertexIncidentCell, hx0, sub_eq_add_neg] using hzwT.1
        · refine ⟨2, ?_⟩
          simpa [LatticeVertexIncidentCell, hy0, sub_eq_add_neg, add_assoc,
            add_comm, add_left_comm] using hzwT.1
      · rcases hv with rfl | rfl
        · refine ⟨2, ?_⟩
          simpa [LatticeVertexIncidentCell, hx0, sub_eq_add_neg, add_assoc,
            add_comm, add_left_comm] using hzwT.1
        · refine ⟨1, ?_⟩
          simpa [LatticeVertexIncidentCell, hy0, sub_eq_add_neg] using hzwT.1
    · rcases hor with ⟨hx0, hy0⟩ | ⟨hy0, hx0⟩
      · rcases hv with rfl | rfl
        · refine ⟨1, ?_⟩
          simpa [LatticeVertexIncidentCell, hx0, hw, sub_eq_add_neg, add_assoc,
            add_comm, add_left_comm] using hzwT.2
        · refine ⟨0, ?_⟩
          simpa [LatticeVertexIncidentCell, hy0, hw] using hzwT.2
      · rcases hv with rfl | rfl
        · refine ⟨0, ?_⟩
          simpa [LatticeVertexIncidentCell, hx0, hw] using hzwT.2
        · refine ⟨1, ?_⟩
          simpa [LatticeVertexIncidentCell, hy0, hx0, hw, sub_eq_add_neg, add_assoc,
            add_comm, add_left_comm] using hzwT.2
  have hmissingA (v : GaussianInt) (hv : v ∈ FootprintVertices T) :
      ∃ j : Fin 4, LatticeVertexIncidentCell v j ∉ (P.tile a).cells :=
          MissingEdgeGeometry.hmissingA C T P hzero hindexed a ha0 incident_of_footprint hTne v hv
  have hmissingB (v : GaussianInt) (hv : v ∈ FootprintVertices T) :
      ∃ j : Fin 4, LatticeVertexIncidentCell v j ∉ (P.tile b).cells :=
          MissingEdgeGeometry.hmissingA C T P hzero hindexed b hb0 incident_of_footprint hTne v hv
  have hboundA_x : x ∈ BoundaryFootprintVertices (P.tile a) :=
    P3161T2IncidentBoundary (P.tile a) x
      (incident_of_footprint (P.tile a) x hnonemptyA hxa) (hmissingA x hx)
  have hboundA_y : y ∈ BoundaryFootprintVertices (P.tile a) :=
    P3161T2IncidentBoundary (P.tile a) y
      (incident_of_footprint (P.tile a) y hnonemptyA hya) (hmissingA y hy)
  have hboundB_x : x ∈ BoundaryFootprintVertices (P.tile b) :=
    P3161T2IncidentBoundary (P.tile b) x
      (incident_of_footprint (P.tile b) x hnonemptyB hxb) (hmissingB x hx)
  have hboundB_y : y ∈ BoundaryFootprintVertices (P.tile b) :=
    P3161T2IncidentBoundary (P.tile b) y
      (incident_of_footprint (P.tile b) y hnonemptyB hyb) (hmissingB y hy)
  have hneqxy : x ≠ y := MissingEdgeGeometry.adjacent_ne x y hxy
  have hclass := (PeriodicTileIntersectionClassification P).1
  have habEdge : (FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty :=
      MissingEdgeGeometry.habEdge C P x y z w hedgeFacts a b hza hwb
  have hzeroaEdge : (FootprintEdges (P.tile 0) ∩ FootprintEdges (P.tile a)).Nonempty :=
      MissingEdgeGeometry.hzeroaEdge C T P x hx y hy hzero a ha0 hxa hya hneqxy hclass
  have hzerobEdge : (FootprintEdges (P.tile 0) ∩ FootprintEdges (P.tile b)).Nonempty :=
      MissingEdgeGeometry.hzerobEdge C T P x hx y hy hzero b hb0 hxb hyb hneqxy hclass
  have habneq : a ≠ b := by
    intro heq
    subst b
    have hboth : z ∈ (P.tile a).cells ∧ w ∈ (P.tile a).cells := ⟨ha, hb⟩
    have hzw : z ≠ w := by
      rcases hform with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · intro hh
        have hr := congrArg Zsqrtd.re hh
        norm_num at hr
      · intro hh
        have hi := congrArg Zsqrtd.im hh
        norm_num at hi
    have hsingleZ : ({x, y} : Finset GaussianInt) ∈
        FootprintEdges (⟨{z}, z⟩ : ProtoTile) := by
      exact (hedgeFacts (⟨{z}, z⟩ : ProtoTile)).1.mpr (Or.inl (by simp))
    have hsingleW : ({x, y} : Finset GaussianInt) ∈
        FootprintEdges (⟨{w}, w⟩ : ProtoTile) := by
      exact (hedgeFacts (⟨{w}, w⟩ : ProtoTile)).1.mpr (Or.inr (by simp))
    have hinside := (P4456T2EdgeInterior (P.tile a) x y z w hxy hzw
      hsingleZ hsingleW).2 hboth
    have hchord := hnochord a x y hxy
      (by simpa [htile] using hboundA_x)
      (by simpa [htile] using hboundA_y)
    have hinside' : OpenLatticeEdge x y ⊆
        interior (TileRealization (TileTranslation T (a : GaussianInt))) := by
      simpa [htile] using hinside
    exact hchord hinside'
  have habAdj : P.plane.adjacent a b := (hclass a b habneq).1.mp habEdge
  have h0aAdj : P.plane.adjacent 0 a :=
    (hclass 0 a (Ne.symm ha0)).1.mp hzeroaEdge
  have h0bAdj : P.plane.adjacent 0 b :=
    (hclass 0 b (Ne.symm hb0)).1.mp hzerobEdge
  have htriple := htriangles 0 a b (Ne.symm ha0) habneq hb0 h0aAdj habAdj
      ((P.plane.adjacent_symmetric 0 b).mp h0bAdj)
  obtain ⟨_, _, _, v, hv, hvuniq⟩ := htriple
  have hxcommon : x ∈ BoundaryFootprintVertices (P.tile 0) ∧
      x ∈ BoundaryFootprintVertices (P.tile a) ∧ x ∈ BoundaryFootprintVertices (P.tile b) :=
          ⟨by simpa [hzero] using (P3161T2IncidentBoundary T x
            (incident_of_footprint T x hTne hx) (hmissT x (Or.inl rfl))),
            hboundA_x, hboundB_x⟩
  have hycommon : y ∈ BoundaryFootprintVertices (P.tile 0) ∧
      y ∈ BoundaryFootprintVertices (P.tile a) ∧ y ∈ BoundaryFootprintVertices (P.tile b) :=
          ⟨by simpa [hzero] using (P3161T2IncidentBoundary T y
            (incident_of_footprint T y hTne hy) (hmissT y (Or.inr rfl))),
            hboundA_y, hboundB_y⟩
  have hvx := hvuniq x hxcommon
  have hvy := hvuniq y hycommon
  exact hneqxy (hvx.trans hvy.symm)

end ApollonianSuperharmonic

end
