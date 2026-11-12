/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.CentrallyReflectedAt
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.PrecursorBoundaryArcData
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport
public import LeanPool.ApollonianSuperharmonic.P4651T1GridHalfTurnTransport
public import LeanPool.ApollonianSuperharmonic.P4651T1FreeBoundaryHalfTurn
public import LeanPool.ApollonianSuperharmonic.P4651T1ContactEdgeSeparation
public import LeanPool.ApollonianSuperharmonic.P4651T1CycleComplementaryArcs

-- [TABLET NODE: P4638T1AntipodalContactArcs]

/-!
# P4638T1AntipodalContactArcs

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4638T1AntipodalContactArcs :
    ∀ (Dplus : ProtoTile), ∀ (Dminus : ProtoTile), ∀ (O : ProtoTile), ∀ (O' : ProtoTile), ∀ (X :
        ProtoTile), ∀ (Y : ProtoTile), ∀ (U : ProtoTile), ∀ (V : ProtoTile), (O.cells.Nonempty) →
        ((LatticeTile O) → ((LatticeTile Dplus) → ((LatticeTile Dminus) → ((TileTouching Dplus O)
        → ((TileTouching Dminus O) → ((Disjoint Dplus.cells Dminus.cells) →
        ((CentrallyReflectedAt (TileCentroid O) Dplus Dminus) → ((QuarterTurnSymmetric O) →
        ((O.cells = O'.cells) → ((O.cells = ∅ → O.anchor = O'.anchor) → ((X.cells.Nonempty) →
        ((Y.cells.Nonempty) → ((U.cells.Nonempty) → ((V.cells.Nonempty) → ((TouchingTriple X Y O)
        → ((TouchingTriple U V O) → ((X.cells ⊆ Dplus.cells) → ((Y.cells ⊆ Dminus.cells) →
        ((U.cells ⊆ Dplus.cells) → ((V.cells ⊆ Dminus.cells) → ((CentrallyReflectedAt
        (TileCentroid O) X V) → ((CentrallyReflectedAt (TileCentroid O) Y U) → (Nonempty
        (PrecursorBoundaryArcData Dplus Dminus O O' X Y U V) ∧
      ∀ e ∈ BoundaryFootprintEdges O,
        e ∈ BoundaryFootprintEdges Dplus ∨ e ∈ BoundaryFootprintEdges
            Dminus))))))))))))))))))))))) := by
  intro Dplus Dminus O O' X Y U V hO hOL hplus hminus htplus htminus hdisjoint hreflect hsym
      hcells hanchor hX hY hU hV hfirst hsecond hXsub hYsub hUsub hVsub hXV hYU
-- BODY
  classical
  have positive_touch (S T : ProtoTile) (hS : S.cells.Nonempty)
      (hT : T.cells.Nonempty) (ht : TileTouching S T) :
      Disjoint S.cells T.cells ∧
        SimpleGridPath (BoundaryFootprintVertices S ∩ BoundaryFootprintVertices T)
          (BoundaryFootprintEdges S ∩ BoundaryFootprintEdges T) := by
    rcases ht with ⟨_, _, hd, hp⟩ | ⟨hs, _⟩ | ⟨ht, _⟩
    · exact ⟨hd, hp⟩
    · simp [hs] at hS
    · simp [ht] at hT
  have hDp : Dplus.cells.Nonempty := hX.mono hXsub
  have hDm : Dminus.cells.Nonempty := hY.mono hYsub
  obtain ⟨hdp, hpathp⟩ := positive_touch Dplus O hDp hO htplus
  obtain ⟨hdm, hpathm⟩ := positive_touch Dminus O hDm hO htminus
  obtain ⟨growp, growm, hsep⟩ :=
    P4651T1ContactEdgeSeparation Dplus Dminus O hdp hdm hdisjoint
  obtain ⟨u, hu, _⟩ := QuarterTurnSymmetricCenteredTransport O hsym
  let w := u + GaussianQuarterTurn u
  have hw : GaussianRealPoint w =
      (2 * (TileCentroid O).1, 2 * (TileCentroid O).2) := by
    have hx := congrArg Prod.fst hu
    have hy := congrArg Prod.snd hu
    dsimp [GaussianRealPoint] at hx hy
    change (((u.re + -u.im : Int) : Real), ((u.im + u.re : Int) : Real)) = _
    push_cast
    exact Prod.ext (by linarith) (by linarith)
  have hself : CentrallyReflectedAt (TileCentroid O) O O := by
    let H : Real × Real → Real × Real := fun p =>
      (2 * (TileCentroid O).1 - p.1, 2 * (TileCentroid O).2 - p.2)
    have hH (p : Real × Real) : H (H p) = p := by
      ext <;> dsimp [H] <;> ring
    have hmem (p : Real × Real) (hp : p ∈ TileRealization O) :
        H p ∈ TileRealization O := by
      have h := (hsym _).mp ((hsym p).mp hp)
      convert h using 1; dsimp [H]; ring
    change TileRealization O = H '' TileRealization O
    ext p
    constructor
    · intro hp
      exact ⟨H p, hmem p hp, hH p⟩
    · rintro ⟨q, hq, rfl⟩
      exact hmem q hq
  let r : GaussianInt → GaussianInt := fun z => w - z
  have hinv : Function.Involutive r := by
    intro z
    dsimp [r]
    abel
  have hinj : Function.Injective r := hinv.injective
  obtain ⟨_, heO, hvO⟩ := P4651T1GridHalfTurnTransport
    (TileCentroid O) w hw O O hO hO hself
  obtain ⟨_, _, hvD⟩ := P4651T1GridHalfTurnTransport
    (TileCentroid O) w hw Dplus Dminus hDp hDm hreflect
  obtain ⟨_, _, hvXV⟩ := P4651T1GridHalfTurnTransport
    (TileCentroid O) w hw X V hX hV hXV
  obtain ⟨_, _, hvYU⟩ := P4651T1GridHalfTurnTransport
    (TileCentroid O) w hw Y U hY hU hYU
  obtain ⟨hfreeV, hfreeE⟩ :=
    P4651T1FreeBoundaryHalfTurn O hO hOL hsym w hw hself
  have image_inter (A B : Set GaussianInt) :
      r '' (A ∩ B) = r '' A ∩ r '' B := by
    ext z
    constructor
    · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, ⟨x, hy, rfl⟩⟩
    · rintro ⟨⟨x, hx, hxr⟩, ⟨y, hy, hyr⟩⟩
      have hxy : x = y := hinj (hxr.trans hyr.symm)
      subst y
      exact ⟨x, ⟨hx, hy⟩, hxr⟩
  have hcontact :
      r '' (BoundaryFootprintVertices Dplus ∩ BoundaryFootprintVertices O) =
        BoundaryFootprintVertices Dminus ∩ BoundaryFootprintVertices O := by
    rw [image_inter, ← hvD, ← hvO]
  obtain ⟨a, ha, hau⟩ := hfirst.2.2.2
  have first_transition (x : GaussianInt) :
      x ∈ BoundaryFootprintVertices X ∧ x ∈ BoundaryFootprintVertices Y ∧
        x ∈ BoundaryFootprintVertices O ↔ x = a := by
    exact ⟨fun hx => hau x hx, fun hx => hx.symm ▸ ha⟩
  -- Identify the second supplied labelled junction by exact boundary transport.
  have hra : r a ∈ BoundaryFootprintVertices U ∧
      r a ∈ BoundaryFootprintVertices V ∧ r a ∈ BoundaryFootprintVertices O := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hvYU]
      exact ⟨a, ha.2.1, rfl⟩
    · rw [hvXV]
      exact ⟨a, ha.1, rfl⟩
    · rw [hvO]
      exact ⟨a, ha.2.2, rfl⟩
  have second_transition (x : GaussianInt) :
      x ∈ BoundaryFootprintVertices U ∧ x ∈ BoundaryFootprintVertices V ∧
        x ∈ BoundaryFootprintVertices O ↔ x = r a := by
    obtain ⟨b, hb, hbu⟩ := hsecond.2.2.2
    have hab : r a = b := hbu _ hra
    exact ⟨fun hx => (hbu x hx).trans hab.symm, fun hx => hx.symm ▸ hra⟩
  have lift_vertex (S D : ProtoTile) (hD : D.cells.Nonempty)
      (hpath : SimpleGridPath
        (BoundaryFootprintVertices S ∩ BoundaryFootprintVertices O)
        (BoundaryFootprintEdges S ∩ BoundaryFootprintEdges O))
      (hgrow : BoundaryFootprintEdges S ∩ BoundaryFootprintEdges O ⊆
        BoundaryFootprintEdges D ∩ BoundaryFootprintEdges O)
      (hx : a ∈ BoundaryFootprintVertices S ∩ BoundaryFootprintVertices O) :
      a ∈ BoundaryFootprintVertices D ∩ BoundaryFootprintVertices O := by
    obtain ⟨e, hae, he⟩ := SimpleGridPathVertexIncidentEdge _ _ hpath a hx
    have hg := hgrow he
    refine ⟨?_, hx.2⟩
    simp only [BoundaryFootprintVertices, ite_eq_left hD, Set.mem_ofPred_eq]
    exact ⟨e, hg.1, hae⟩
  have hpathXO : SimpleGridPath
      (BoundaryFootprintVertices X ∩ BoundaryFootprintVertices O)
      (BoundaryFootprintEdges X ∩ BoundaryFootprintEdges O) := by
    simpa only [Set.inter_comm] using
      (positive_touch O X hO hX hfirst.2.2.1).2
  have hpathYO := (positive_touch Y O hY hO hfirst.2.1).2
  have hap := lift_vertex X Dplus hDp hpathXO (growp X hXsub) ⟨ha.1, ha.2.2⟩
  have ham := lift_vertex Y Dminus hDm hpathYO (growm Y hYsub) ⟨ha.2.1, ha.2.2⟩
  obtain ⟨⟨p, q, hpN, hqN, hph, hpl, hqh, hql, hpS, hqS,
      hpstep, hqstep, hunion, hinter⟩, hcover⟩ :=
    P4651T1CycleComplementaryArcs
      (BoundaryFootprintVertices O)
      (BoundaryFootprintVertices Dplus ∩ BoundaryFootprintVertices O)
      (BoundaryFootprintVertices Dminus ∩ BoundaryFootprintVertices O)
      (BoundaryFootprintEdges O)
      (BoundaryFootprintEdges Dplus ∩ BoundaryFootprintEdges O)
      (BoundaryFootprintEdges Dminus ∩ BoundaryFootprintEdges O)
      r a (LatticeTileGridStructure O hOL).2.2 hpathp hpathm
      Set.inter_subset_right Set.inter_subset_right
      Set.inter_subset_right Set.inter_subset_right hinv hvO.symm heO.symm
      hfreeV hfreeE hcontact hsep ⟨hap, ham⟩
  have real_action (z : GaussianInt) : GaussianRealPoint (r z) =
      (2 * (TileCentroid O).1 - (GaussianRealPoint z).1,
        2 * (TileCentroid O).2 - (GaussianRealPoint z).2) := by
    have hx := congrArg Prod.fst hw
    have hy := congrArg Prod.snd hw
    dsimp [GaussianRealPoint] at hx hy
    change (((w.re - z.re : Int) : Real), ((w.im - z.im : Int) : Real)) = _
    push_cast
    exact Prod.ext (by dsimp [GaussianRealPoint]; linarith)
      (by dsimp [GaussianRealPoint]; linarith)
  have hrealcontact :
      (fun z : GaussianInt =>
        (2 * (TileCentroid O).1 - (GaussianRealPoint z).1,
          2 * (TileCentroid O).2 - (GaussianRealPoint z).2)) ''
          (p.toFinset : Set GaussianInt) =
        GaussianRealPoint '' (q.toFinset : Set GaussianInt) := by
    simp_rw [← real_action]
    rw [← Set.image_image, hpS, hqS, hcontact]
  refine ⟨⟨{
    precursor_cells := hcells
    precursor_anchor := hanchor
    first_touching := hfirst
    second_touching := hsecond
    first_plus_child := hXsub
    first_minus_child := hYsub
    second_plus_child := hUsub
    second_minus_child := hVsub
    a := a
    b := r a
    first_transition := first_transition
    second_transition := second_transition
    branch := Or.inl ⟨hO, p, q, hpN, hqN, hph, hpl, hqh, hql, hpS, hqS,
      hpstep, hqstep, hunion, hinter, real_action a, hrealcontact⟩
  }⟩, ?_⟩
  intro e he
  exact (hcover e he).imp And.left And.left

end ApollonianSuperharmonic

end
