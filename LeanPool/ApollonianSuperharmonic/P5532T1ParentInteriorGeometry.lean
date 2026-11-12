/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4339T1PrecursorSupportGeometry
public import LeanPool.ApollonianSuperharmonic.LatticeEdgeRegularity

-- [TABLET NODE: P5532T1ParentInteriorGeometry]

/-!
# P5532T1ParentInteriorGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5532T1ParentInteriorGeometry :
    ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
        BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
        BandOrderedGeneralLayoutCertificate q cfg C T), ∀ (h : PartialOdometer), ∀ (hs : Fin 3 →
        Bool → PartialOdometer), ∀ (k : PartialOdometer), (LatticeTile T) → (((h.domain : Set
        GaussianInt) = FootprintVertices T) → ((∀ i, ∀ s, ((hs i s).domain : Set GaussianInt) =
        FootprintVertices (cert.P i s)) → (((k.domain : Set GaussianInt) = FootprintVertices
        cert.O) → (
    let D := h.domain.filter fun x =>
      @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)
    let A := fun a : Fin 3 × Bool => (hs a.1 a.2).domain.filter fun x =>
      @decide (x ∉ BoundaryFootprintVertices (cert.P a.1 a.2)) (Classical.propDecidable _)
    let I := k.domain.filter fun x =>
      @decide (x ∉ BoundaryFootprintVertices cert.O) (Classical.propDecidable _)
    (∀ a, A a ⊆ D) ∧
    (∀ a, ∀ b, a ≠ b → A a ∩ A b = if a.1 = 0 ∧ b.1 = 0 then I else ∅) ∧
    (∀ a, ∀ b, ∀ x ∈ A a, x ∉ A b → ∀ y ∈ A b, y ∉ A a →
      ¬ FourNeighborAdjacent x y) ∧
    Finset.univ.biUnion A = D.filter (fun x =>
      @decide (∃ i s, x ∈ (hs i s).domain ∧
        x ∉ BoundaryFootprintVertices (cert.P i s)) (Classical.propDecidable _)))))) := by
  intro C q cfg T cert h hs k hlat hdom hsdom hkdom
-- BODY
  classical
  let D := h.domain.filter fun x =>
    @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)
  let A := fun a : Fin 3 × Bool => (hs a.1 a.2).domain.filter fun x =>
    @decide (x ∉ BoundaryFootprintVertices (cert.P a.1 a.2)) (Classical.propDecidable _)
  let I := k.domain.filter fun x =>
    @decide (x ∉ BoundaryFootprintVertices cert.O) (Classical.propDecidable _)
  have full (V : ProtoTile) (x : GaussianInt) :
      (x ∈ FootprintVertices V ∧ x ∉ BoundaryFootprintVertices V) ↔
        ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ V.cells := by
    by_cases hne : V.cells.Nonempty
    · constructor
      · rintro ⟨hx, hnb⟩
        exact (P4456T2VertexInterior V hne x hx).2.mp hnb
      · intro hall
        have hxcell : x ∈ V.cells := by simpa [LatticeVertexIncidentCell] using hall 0
        have hx : x ∈ FootprintVertices V := by
          simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
          exact ⟨x, hxcell, Or.inl rfl⟩
        exact ⟨hx, (P4456T2VertexInterior V hne x hx).2.mpr hall⟩
    · have hempty : V.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [FootprintVertices, BoundaryFootprintVertices,
        hempty, Finset.notMem_empty]
      simp
  have domainFull (V : ProtoTile) (l : PartialOdometer)
      (hd : (l.domain : Set GaussianInt) = FootprintVertices V) (x : GaussianInt) :
      x ∈ l.domain.filter (fun x => @decide (x ∉ BoundaryFootprintVertices V)
        (Classical.propDecidable _)) ↔
        ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ V.cells := by
    simp only [Finset.mem_filter, decide_eq_true_eq]
    have hmem : x ∈ l.domain ↔ x ∈ FootprintVertices V := by
      change x ∈ (l.domain : Set GaussianInt) ↔ _
      rw [hd]
    rw [hmem]
    exact full V x
  have hD (x : GaussianInt) : x ∈ D ↔
      ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells := domainFull T h hdom x
  have hA (a : Fin 3 × Bool) (x : GaussianInt) : x ∈ A a ↔
      ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P a.1 a.2).cells :=
    domainFull _ _ (hsdom a.1 a.2) x
  have hI (x : GaussianInt) : x ∈ I ↔
      ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ cert.O.cells :=
    domainFull _ _ hkdom x
  obtain ⟨_, _, hOband, hOdisk, _, _, hpairCells, hdis⟩ :=
    P4339T1PrecursorSupportGeometry C q cfg T cert
  have cellsPair (a b : Fin 3 × Bool) (hab : a ≠ b)
      (hz : a.1 = 0 ∧ b.1 = 0) :
      (cert.P a.1 a.2).cells ∩ (cert.P b.1 b.2).cells = cert.O.cells := by
    rcases a with ⟨a, s⟩
    rcases b with ⟨b, t⟩
    obtain ⟨rfl, rfl⟩ := hz
    cases s <;> cases t
    · exact (hab rfl).elim
    · simpa only [Finset.inter_comm] using hpairCells
    · exact hpairCells
    · exact (hab rfl).elim
  have contained : ∀ a, A a ⊆ D := by
    intro a x hx
    apply (hD x).mpr
    intro j
    exact (cert.outer_union _).mpr ⟨a.1, a.2, (hA a x).mp hx j⟩
  have pair : ∀ a b, a ≠ b → A a ∩ A b = if a.1 = 0 ∧ b.1 = 0 then I else ∅ := by
    intro a b hab
    by_cases hz : a.1 = 0 ∧ b.1 = 0
    · rw [ite_eq_left hz]
      have hc := cellsPair a b hab hz
      ext x
      simp only [Finset.mem_inter, hA, hI]
      constructor
      · rintro ⟨ha, hb⟩ j
        rw [← hc]
        exact Finset.mem_inter.mpr ⟨ha j, hb j⟩
      · intro hall
        constructor <;> intro j
        · exact (Finset.mem_inter.mp (hc ▸ hall j)).1
        · exact (Finset.mem_inter.mp (hc ▸ hall j)).2
    · rw [ite_eq_right hz]
      have hd := hdis a.1 a.2 b.1 b.2 hab hz
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hx
      exact Finset.disjoint_left.mp hd ((hA a x).mp ha 0) ((hA b x).mp hb 0)
  have cross : ∀ a b, ∀ x ∈ A a, x ∉ A b → ∀ y ∈ A b, y ∉ A a →
      ¬ FourNeighborAdjacent x y := by
    intro a b x hx hxnot y hy hynot hxy
    have hab : a ≠ b := by rintro rfl; exact hxnot hx
    obtain ⟨z, w, hform⟩ := P4397T1UnitEdgeCells.1 x y hxy
    have fa := P4397T1UnitEdgeCells.2 x y z w hform (cert.P a.1 a.2)
    have fb := P4397T1UnitEdgeCells.2 y x z w (by
      rcases hform with ⟨hh, heq⟩ | ⟨hh, heq⟩
      · exact Or.inl ⟨hh.elim Or.inr Or.inl, heq⟩
      · exact Or.inr ⟨hh.elim Or.inr Or.inl, heq⟩) (cert.P b.1 b.2)
    have za := fa.2.2.2.2 ((hA a x).mp hx)
    have zb := fb.2.2.2.2 ((hA b y).mp hy)
    by_cases hz : a.1 = 0 ∧ b.1 = 0
    · have hc := cellsPair a b hab hz
      have zO : z ∈ cert.O.cells := by
        rw [← hc]
        exact Finset.mem_inter.mpr ⟨za.1, zb.1⟩
      have wO : w ∈ cert.O.cells := by
        rw [← hc]
        exact Finset.mem_inter.mpr ⟨za.2, zb.2⟩
      have hOne : cert.O.cells.Nonempty := ⟨z, zO⟩
      have hlatO : LatticeTile cert.O := hOdisk hOne
      have fo := P4397T1UnitEdgeCells.2 x y z w hform cert.O
      have hfootO := fo.2.2.1 (Or.inl zO)
      have hxb : x ∈ BoundaryFootprintVertices cert.O := by
        by_contra hn
        have hxI := (hI x).mpr ((full cert.O x).mp ⟨hfootO.1, hn⟩)
        have hxpair : x ∈ A a ∩ A b := by rw [pair a b hab, ite_eq_left hz]; exact hxI
        exact hxnot (Finset.mem_inter.mp hxpair).2
      have hyb : y ∈ BoundaryFootprintVertices cert.O := by
        by_contra hn
        have hyI := (hI y).mpr ((full cert.O y).mp ⟨hfootO.2.1, hn⟩)
        have hypair : y ∈ A a ∩ A b := by rw [pair a b hab, ite_eq_left hz]; exact hyI
        exact hynot (Finset.mem_inter.mp hypair).1
      have hposO : 0 < (cfg.firstPredecessor 1).1 := by
        have positive (c : CircleCoordinates) (V : ProtoTile)
            (hb : BandPrototile c V) (hne : V.cells.Nonempty) : 0 < c.1 := by
          cases hb with
          | line w x hw => simp at hne
          | unit z x anchor => norm_num
          | decompose hp hS hc hf hce =>
            exact (ProperBandCurvatureStructure _ hp).1
        exact positive _ _ hOband hOne
      let CO : BandCircle :=
        ⟨⟨cfg.firstPredecessor 1, Or.inl hposO,
          cfg.firstPredecessor, cfg.firstProper.1, 1, rfl⟩, hposO⟩
      exact (LatticeEdgeRegularity CO cert.O hOband hlatO).1 x y hxy hxb hyb
        (fo.2.2.2.1 ⟨zO, wO⟩)
    · exact Finset.disjoint_left.mp (hdis a.1 a.2 b.1 b.2 hab hz) za.1 zb.1
  refine ⟨contained, pair, cross, ?_⟩
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨a, hx⟩
    have hxA : x ∈ A a := by
      simpa only [A, Finset.mem_filter, decide_eq_true_eq] using hx
    refine ⟨?_, a.1, a.2, ?_⟩
    · simpa only [D, Finset.mem_filter, decide_eq_true_eq] using contained a hxA
    · exact hx
  · rintro ⟨hx, i, s, his⟩
    exact ⟨(i, s), his⟩

end ApollonianSuperharmonic

end
