/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.LatticeFootprintIncidence
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintInclusion

public import LeanPool.ApollonianSuperharmonic.PrecursorBoundaryArcData
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathVertexIncidentEdge
public import LeanPool.ApollonianSuperharmonic.P3102T2CommonEdgeSectorTransition
public import LeanPool.ApollonianSuperharmonic.FootprintVertices

-- [TABLET NODE: P4638T1ContactStarCoverage]

/-!
# P4638T1ContactStarCoverage

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ContactStarGeometry

private def canonicalEdgeAt (y : GaussianInt) : Fin 4 → Finset GaussianInt :=
  ![{y, y + ⟨0, 1⟩}, {y - 1, y}, {y - ⟨0, 1⟩, y}, {y, y + 1}]

private theorem boundaryEdgeOfCross (T : ProtoTile) (y : GaussianInt) (j : Fin 4)
      (hcross : (LatticeVertexIncidentCell y j ∈ T.cells ∧
          LatticeVertexIncidentCell y (j + 1) ∉ T.cells) ∨
        (LatticeVertexIncidentCell y j ∉ T.cells ∧
          LatticeVertexIncidentCell y (j + 1) ∈ T.cells)) :
      canonicalEdgeAt y j ∈ BoundaryFootprintEdges T := by
  classical
  fin_cases j
  · rcases hcross with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · change y ∈ T.cells at hl
      change y - 1 ∉ T.cells at hr
      change {y, y + ⟨0, 1⟩} ∈ BoundaryFootprintEdges T
      exact ⟨y, Or.inr ⟨rfl, Or.inl ⟨hl, hr⟩⟩⟩
    · change y ∉ T.cells at hl
      change y - 1 ∈ T.cells at hr
      change {y, y + ⟨0, 1⟩} ∈ BoundaryFootprintEdges T
      exact ⟨y, Or.inr ⟨rfl, Or.inr ⟨hl, hr⟩⟩⟩
  · rcases hcross with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · change y - 1 ∈ T.cells at hl
      change y - 1 - ⟨0, 1⟩ ∉ T.cells at hr
      change {y - 1, y} ∈ BoundaryFootprintEdges T
      refine ⟨y - 1, Or.inl ⟨by ext z; simp [], Or.inl ⟨hl, hr⟩⟩⟩
    · change y - 1 ∉ T.cells at hl
      change y - 1 - ⟨0, 1⟩ ∈ T.cells at hr
      change {y - 1, y} ∈ BoundaryFootprintEdges T
      refine ⟨y - 1, Or.inl ⟨by ext z; simp [], Or.inr ⟨hl, hr⟩⟩⟩
  · rcases hcross with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · change y - 1 - ⟨0, 1⟩ ∈ T.cells at hl
      change y - ⟨0, 1⟩ ∉ T.cells at hr
      change {y - ⟨0, 1⟩, y} ∈ BoundaryFootprintEdges T
      refine ⟨y - ⟨0, 1⟩, Or.inr ⟨by ext z; simp [sub_add_cancel], Or.inr ⟨hr, ?_⟩⟩⟩
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hl
    · change y - 1 - ⟨0, 1⟩ ∉ T.cells at hl
      change y - ⟨0, 1⟩ ∈ T.cells at hr
      change {y - ⟨0, 1⟩, y} ∈ BoundaryFootprintEdges T
      refine ⟨y - ⟨0, 1⟩, Or.inr ⟨by ext z; simp [sub_add_cancel], Or.inl ⟨hr, ?_⟩⟩⟩
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hl
  · rcases hcross with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · change y - ⟨0, 1⟩ ∈ T.cells at hl
      change y ∉ T.cells at hr
      change {y, y + 1} ∈ BoundaryFootprintEdges T
      refine ⟨y, Or.inl ⟨rfl, Or.inr ⟨hr, ?_⟩⟩⟩
      simpa using hl
    · change y - ⟨0, 1⟩ ∉ T.cells at hl
      change y ∈ T.cells at hr
      change {y, y + 1} ∈ BoundaryFootprintEdges T
      exact ⟨y, Or.inl ⟨rfl, Or.inl ⟨hr, hl⟩⟩⟩

end ContactStarGeometry

namespace ContactStarCases

private theorem hdisjPlusO :
    (by
      classical
      exact
        ∀ (Dplus : ProtoTile), ∀ (O : ProtoTile), (Finset.Nonempty O.cells) → ((TileTouching
            Dplus O) → ((Dplus.cells.Nonempty) → (Disjoint Dplus.cells O.cells))) ) := by
  classical
  intro Dplus O hO htplus hDplus
  rcases htplus with ⟨_, _, hd, _⟩ | ⟨hE, _⟩ | ⟨hE, _⟩
  · exact hd
  · exact (Finset.not_nonempty_iff_eq_empty.mpr hE hDplus).elim
  · exact (Finset.not_nonempty_iff_eq_empty.mpr hE hO).elim

private abbrev hdisjMinusO :=
  ApollonianSuperharmonic.ContactStarCases.hdisjPlusO

private theorem hpathPlusO :
    (by
      classical
      exact
        ∀ (Dplus : ProtoTile), ∀ (O : ProtoTile), (Finset.Nonempty O.cells) → ((TileTouching
            Dplus O) → ((Dplus.cells.Nonempty) → (SimpleGridPath (BoundaryFootprintVertices Dplus
            ∩ BoundaryFootprintVertices O) (BoundaryFootprintEdges Dplus ∩ BoundaryFootprintEdges
            O)))) ) := by
  classical
  intro Dplus O hO htplus hDplus
  rcases htplus with ⟨_, _, _, hp⟩ | ⟨hE, _⟩ | ⟨hE, _⟩
  · exact hp
  · exact (Finset.not_nonempty_iff_eq_empty.mpr hE hDplus).elim
  · exact (Finset.not_nonempty_iff_eq_empty.mpr hE hO).elim

private abbrev hpathMinusO :=
  ApollonianSuperharmonic.ContactStarCases.hpathPlusO

private abbrev boundaryEdgeFootprint :=
  BoundaryFootprintInclusion.boundaryEdge

private theorem edgeAt_eq :
    (by
      classical
      exact
        let edgeAt (y : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{y, y + ⟨0, 1⟩}, {y - 1, y},
            {y - ⟨0, 1⟩, y}, {y, y + 1}]
        let offsetAt : Fin 4 → GaussianInt := ![⟨0, 1⟩, -1, -⟨0, 1⟩, 1]
        ∀ (y : GaussianInt), ∀ (i : Fin (4 : ℕ)), edgeAt y i = {y, y + offsetAt i} ) := by
  classical
  intro edgeAt offsetAt y i
  fin_cases i <;> ext z <;> simp [edgeAt, offsetAt, sub_eq_add_neg,
    or_comm]

private theorem offsetAt_injective :
    (by
      classical
      exact
        let offsetAt : Fin 4 → GaussianInt := ![⟨0, 1⟩, -1, -⟨0, 1⟩, 1]
        ∀ (i : Fin (4 : ℕ)), ∀ (j : Fin (4 : ℕ)), offsetAt i = offsetAt j → i = j ) := by
  classical
  intro offsetAt i j h
  fin_cases i <;> fin_cases j <;>
    simp [offsetAt, Zsqrtd.ext_iff] at h ⊢

private theorem edgeAt_injective :
    (by
      classical
      exact
        let edgeAt (y : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{y, y + ⟨0, 1⟩}, {y - 1, y},
            {y - ⟨0, 1⟩, y}, {y, y + 1}]
        let offsetAt : Fin 4 → GaussianInt := ![⟨0, 1⟩, -1, -⟨0, 1⟩, 1]
        (∀ (y : GaussianInt), ∀ (i : Fin 4), edgeAt y i = {y, y + offsetAt i}) → ((∀ (i : Fin 4),
            ∀ (j : Fin 4), (offsetAt i = offsetAt j) → (i = j)) → (∀ (y : GaussianInt), ∀ (i :
            Fin (4 : ℕ)), ∀ (j : Fin (4 : ℕ)), edgeAt y i = edgeAt y j → i = j)) ) := by
  classical
  intro edgeAt offsetAt edgeAt_eq offsetAt_injective y i j h
  rw [edgeAt_eq y i, edgeAt_eq y j] at h
  have hm : y + offsetAt i ∈ ({y, y + offsetAt j} : Finset GaussianInt) := by
    rw [← h]
    simp
  have heq : y + offsetAt i = y ∨ y + offsetAt i = y + offsetAt j := by
    simpa using hm
  rcases heq with heq | heq
  · have hz : offsetAt i = 0 := by
      have h' : y + offsetAt i = y + 0 := by simpa using heq
      have := add_left_cancel h'
      simpa using this
    fin_cases i <;> simp [offsetAt, Zsqrtd.ext_iff] at hz
  · exact offsetAt_injective i j (add_left_cancel heq)

private theorem edgeCross :
    (by
      classical
      exact
        ∀ (Dplus : ProtoTile), ∀ (Dminus : ProtoTile), ∀ (O : ProtoTile), (∀ e ∈
            BoundaryFootprintEdges O, e ∈ BoundaryFootprintEdges Dplus ∨ e ∈
            BoundaryFootprintEdges Dminus) → ((Disjoint Dplus.cells O.cells) → ((Disjoint
            Dminus.cells O.cells) → ((∀ (T : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈
            BoundaryFootprintEdges T) → (e ∈ FootprintEdges T)) → (
        let edgeAt (y : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{y, y + ⟨0, 1⟩}, {y - 1, y},
            {y - ⟨0, 1⟩, y}, {y, y + 1}]
        (∀ (y : GaussianInt), ∀ (i : Fin 4), ∀ (j : Fin 4), (edgeAt y i = edgeAt y j) → (i = j))
            → (∀ (y : GaussianInt), ∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell y j ∈ O.cells
            ∧ LatticeVertexIncidentCell y (j + (1 : Fin (4 : ℕ))) ∉ O.cells ∨
            LatticeVertexIncidentCell y j ∉ O.cells ∧ LatticeVertexIncidentCell y (j + (1 : Fin
            (4 : ℕ))) ∈ O.cells → ((LatticeVertexIncidentCell y j ∈ Dplus.cells ∨
            LatticeVertexIncidentCell y j ∈ Dminus.cells) ∨ LatticeVertexIncidentCell y (j + (1 :
            Fin (4 : ℕ))) ∈ Dplus.cells ∨ LatticeVertexIncidentCell y (j + (1 : Fin (4 : ℕ))) ∈
            Dminus.cells) ∧ ∃ (e : Finset GaussianInt), y ∈ e ∧ e ∈ BoundaryFootprintEdges O ∧ (e
            ∈ BoundaryFootprintEdges Dplus ∨ e ∈ BoundaryFootprintEdges Dminus)))))) ) := by
  classical
  intro Dplus Dminus O hedges hdisjPlusO hdisjMinusO boundaryEdgeFootprint edgeAt
      edgeAt_injective y j hcross
  have heO : edgeAt y j ∈ BoundaryFootprintEdges O :=
    ContactStarGeometry.boundaryEdgeOfCross O y j hcross
  have heD := hedges (edgeAt y j) heO
  rcases heD with heD | heD
  · have hfoot : edgeAt y j ∈ FootprintEdges O ∩ FootprintEdges Dplus :=
      ⟨boundaryEdgeFootprint O _ heO, boundaryEdgeFootprint Dplus _ heD⟩
    have hcontact : ∃ e, y ∈ e ∧ e ∈ BoundaryFootprintEdges O ∧
        (e ∈ BoundaryFootprintEdges Dplus ∨ e ∈ BoundaryFootprintEdges Dminus) :=
      ⟨edgeAt y j, by fin_cases j <;> simp [edgeAt], heO, Or.inl heD⟩
    rcases P3102T2CommonEdgeSectorTransition O Dplus y (edgeAt y j)
        hdisjPlusO.symm (by fin_cases j <;> simp [edgeAt]) hfoot with
      ⟨k, hk, hkocc⟩
    have hk' : edgeAt y k = edgeAt y j := by
      change edgeAt y j = edgeAt y k at hk
      exact hk.symm
    have hkj : k = j := edgeAt_injective y k j hk'
    subst k
    rcases hkocc with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · exact ⟨Or.inr (Or.inl hsecond), hcontact⟩
    · exact ⟨Or.inl (Or.inl hfirst), hcontact⟩
  · have hfoot : edgeAt y j ∈ FootprintEdges O ∩ FootprintEdges Dminus :=
      ⟨boundaryEdgeFootprint O _ heO, boundaryEdgeFootprint Dminus _ heD⟩
    have hcontact : ∃ e, y ∈ e ∧ e ∈ BoundaryFootprintEdges O ∧
        (e ∈ BoundaryFootprintEdges Dplus ∨ e ∈ BoundaryFootprintEdges Dminus) :=
      ⟨edgeAt y j, by fin_cases j <;> simp [edgeAt], heO, Or.inr heD⟩
    rcases P3102T2CommonEdgeSectorTransition O Dminus y (edgeAt y j)
        hdisjMinusO.symm (by fin_cases j <;> simp [edgeAt]) hfoot with
      ⟨k, hk, hkocc⟩
    have hk' : edgeAt y k = edgeAt y j := by
      change edgeAt y j = edgeAt y k at hk
      exact hk.symm
    have hkj : k = j := edgeAt_injective y k j hk'
    subst k
    rcases hkocc with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · exact ⟨Or.inr (Or.inr hsecond), hcontact⟩
    · exact ⟨Or.inl (Or.inr hfirst), hcontact⟩

private theorem boundaryVertexOfCross :
    (by
      classical
      exact
        let edgeAt (y : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{y, y + ⟨0, 1⟩}, {y - 1, y},
            {y - ⟨0, 1⟩, y}, {y, y + 1}]
        (∀ (T : ProtoTile), ∀ (y : GaussianInt), ∀ (j : Fin 4), ((LatticeVertexIncidentCell y j ∈
            T.cells ∧ LatticeVertexIncidentCell y (j + 1) ∉ T.cells) ∨ (LatticeVertexIncidentCell
            y j ∉ T.cells ∧ LatticeVertexIncidentCell y (j + 1) ∈ T.cells)) → (edgeAt y j ∈
            BoundaryFootprintEdges T)) → (∀ (T : ProtoTile), ∀ (y : GaussianInt), ∀ (j : Fin (4 :
            ℕ)), LatticeVertexIncidentCell y j ∈ T.cells ∧ LatticeVertexIncidentCell y (j + (1 :
            Fin (4 : ℕ))) ∉ T.cells ∨ LatticeVertexIncidentCell y j ∉ T.cells ∧
            LatticeVertexIncidentCell y (j + (1 : Fin (4 : ℕ))) ∈ T.cells → y ∈
            BoundaryFootprintVertices T) ) := by
  classical
  intro edgeAt boundaryEdgeOfCross T y j hcross
  have hne : T.cells.Nonempty := by
    rcases hcross with ⟨h, _⟩ | ⟨_, h⟩
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  unfold BoundaryFootprintVertices
  rw [ite_eq_left hne]
  exact ⟨edgeAt y j, boundaryEdgeOfCross T y j hcross,
    by fin_cases j <;> simp [edgeAt]⟩

private abbrev incident :=
  LatticeFootprintIncidence.incidentCell

private theorem coverLeft :
    (by
      classical
      exact
        ∀ (Dplus : ProtoTile), ∀ (Dminus : ProtoTile), ∀ (O : ProtoTile), (Disjoint Dplus.cells
            O.cells) → ((Disjoint Dminus.cells O.cells) → ((∀ (y : GaussianInt), ∀ (j : Fin 4),
            ((LatticeVertexIncidentCell y j ∈ O.cells ∧ LatticeVertexIncidentCell y (j + 1) ∉
            O.cells) ∨ (LatticeVertexIncidentCell y j ∉ O.cells ∧ LatticeVertexIncidentCell y (j
            + 1) ∈ O.cells)) → (((LatticeVertexIncidentCell y j ∈ Dplus.cells ∨
            LatticeVertexIncidentCell y j ∈ Dminus.cells) ∨ (LatticeVertexIncidentCell y (j + 1)
            ∈ Dplus.cells ∨ LatticeVertexIncidentCell y (j + 1) ∈ Dminus.cells)) ∧ ∃ e, y ∈ e ∧ e
            ∈ BoundaryFootprintEdges O ∧ (e ∈ BoundaryFootprintEdges Dplus ∨ e ∈
            BoundaryFootprintEdges Dminus))) → (∀ (y : GaussianInt), ∀ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell y j ∈ O.cells ∧ LatticeVertexIncidentCell y (j + (1 : Fin
            (4 : ℕ))) ∉ O.cells ∨ LatticeVertexIncidentCell y j ∉ O.cells ∧
            LatticeVertexIncidentCell y (j + (1 : Fin (4 : ℕ))) ∈ O.cells →
            LatticeVertexIncidentCell y j ∉ O.cells → LatticeVertexIncidentCell y j ∈ Dplus.cells
            ∨ LatticeVertexIncidentCell y j ∈ Dminus.cells))) ) := by
  classical
  intro Dplus Dminus O hdisjPlusO hdisjMinusO edgeCross y j hcross hnot
  rcases hcross with hcase | hcase
  · exact (hnot hcase.1).elim
  · rcases (edgeCross y j (Or.inr hcase)).1 with hleft | hright
    · exact hleft
    · rcases hright with hplus | hminus
      · exact (Finset.disjoint_left.mp hdisjPlusO hplus hcase.2).elim
      · exact (Finset.disjoint_left.mp hdisjMinusO hminus hcase.2).elim

private theorem coverRight :
    (by
      classical
      exact
        ∀ (Dplus : ProtoTile), ∀ (Dminus : ProtoTile), ∀ (O : ProtoTile), (Disjoint Dplus.cells
            O.cells) → ((Disjoint Dminus.cells O.cells) → ((∀ (y : GaussianInt), ∀ (j : Fin 4),
            ((LatticeVertexIncidentCell y j ∈ O.cells ∧ LatticeVertexIncidentCell y (j + 1) ∉
            O.cells) ∨ (LatticeVertexIncidentCell y j ∉ O.cells ∧ LatticeVertexIncidentCell y (j
            + 1) ∈ O.cells)) → (((LatticeVertexIncidentCell y j ∈ Dplus.cells ∨
            LatticeVertexIncidentCell y j ∈ Dminus.cells) ∨ (LatticeVertexIncidentCell y (j + 1)
            ∈ Dplus.cells ∨ LatticeVertexIncidentCell y (j + 1) ∈ Dminus.cells)) ∧ ∃ e, y ∈ e ∧ e
            ∈ BoundaryFootprintEdges O ∧ (e ∈ BoundaryFootprintEdges Dplus ∨ e ∈
            BoundaryFootprintEdges Dminus))) → (∀ (y : GaussianInt), ∀ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell y j ∈ O.cells ∧ LatticeVertexIncidentCell y (j + (1 : Fin
            (4 : ℕ))) ∉ O.cells ∨ LatticeVertexIncidentCell y j ∉ O.cells ∧
            LatticeVertexIncidentCell y (j + (1 : Fin (4 : ℕ))) ∈ O.cells →
            LatticeVertexIncidentCell y (j + (1 : Fin (4 : ℕ))) ∉ O.cells →
            LatticeVertexIncidentCell y (j + (1 : Fin (4 : ℕ))) ∈ Dplus.cells ∨
            LatticeVertexIncidentCell y (j + (1 : Fin (4 : ℕ))) ∈ Dminus.cells))) ) := by
  classical
  intro Dplus Dminus O hdisjPlusO hdisjMinusO edgeCross y j hcross hnot
  rcases hcross with hcase | hcase
  · rcases (edgeCross y j (Or.inl hcase)).1 with hleft | hright
    · rcases hleft with hplus | hminus
      · exact (Finset.disjoint_left.mp hdisjPlusO hplus hcase.1).elim
      · exact (Finset.disjoint_left.mp hdisjMinusO hminus hcase.1).elim
    · exact hright
  · exact (hnot hcase.2).elim

private theorem noCheckerboardDiagonal :
    (by
      classical
      exact
        ∀ (T : ProtoTile), NoCheckerboardCellVertex (↑T.cells : Set LatticeCell) → ∀ (y :
            GaussianInt), ∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell y (j + (1 : Fin (4 :
            ℕ))) ∈ T.cells → LatticeVertexIncidentCell y (j + (3 : Fin (4 : ℕ))) ∈ T.cells →
            LatticeVertexIncidentCell y j ∉ T.cells → LatticeVertexIncidentCell y (j + (2 : Fin
            (4 : ℕ))) ∈ T.cells ) := by
  classical
  intro T hT y j hside1 hside3 hcenter
  by_contra hdiag
  unfold NoCheckerboardCellVertex at hT
  fin_cases j
  · exact (hT y) (Or.inr ⟨by simpa [LatticeVertexIncidentCell] using hside1,
      by simpa [LatticeVertexIncidentCell] using hside3,
      by simpa [LatticeVertexIncidentCell] using hcenter,
      by simpa [LatticeVertexIncidentCell] using hdiag⟩)
  · exact (hT y) (Or.inl ⟨by simpa [LatticeVertexIncidentCell] using hside3,
      by simpa [LatticeVertexIncidentCell] using hside1,
      by simpa [LatticeVertexIncidentCell] using hcenter,
      by simpa [LatticeVertexIncidentCell] using hdiag⟩)
  · exact (hT y) (Or.inr ⟨by simpa [LatticeVertexIncidentCell] using hside3,
      by simpa [LatticeVertexIncidentCell] using hside1,
      by simpa [LatticeVertexIncidentCell] using hdiag,
      by simpa [LatticeVertexIncidentCell] using hcenter⟩)
  · exact (hT y) (Or.inl ⟨by simpa [LatticeVertexIncidentCell] using hside1,
      by simpa [LatticeVertexIncidentCell] using hside3,
      by simpa [LatticeVertexIncidentCell] using hdiag,
      by simpa [LatticeVertexIncidentCell] using hcenter⟩)

private theorem mixedCornerContradiction :
    (by
      classical
      exact
        ∀ (Dplus : ProtoTile), ∀ (Dminus : ProtoTile), ∀ (O : ProtoTile), (Disjoint Dplus.cells
            Dminus.cells) → ((Disjoint Dplus.cells O.cells) → ((Disjoint Dminus.cells O.cells) →
            ((∀ (T : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges T) → (e
            ∈ FootprintEdges T)) → (∀ (J : ProtoTile), ∀ (K : ProtoTile), Finset.Nonempty J.cells
            → Finset.Nonempty K.cells → J.cells ⊆ Dplus.cells → K.cells ⊆ Dminus.cells →
            TileTouching J K → ∀ (y : GaussianInt), ∀ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell y j ∈ O.cells → LatticeVertexIncidentCell y (j + (1 : Fin
            (4 : ℕ))) ∈ Dplus.cells ∧ LatticeVertexIncidentCell y (j + (3 : Fin (4 : ℕ))) ∈
            Dminus.cells ∨ LatticeVertexIncidentCell y (j + (1 : Fin (4 : ℕ))) ∈ Dminus.cells ∧
            LatticeVertexIncidentCell y (j + (3 : Fin (4 : ℕ))) ∈ Dplus.cells →
            LatticeVertexIncidentCell y (j + (2 : Fin (4 : ℕ))) ∉ Dplus.cells →
            LatticeVertexIncidentCell y (j + (2 : Fin (4 : ℕ))) ∉ Dminus.cells → y ∈
            BoundaryFootprintVertices J → y ∈ BoundaryFootprintVertices K → False)))) ) := by
  classical
  intro Dplus Dminus O hdisjoint hdisjPlusO hdisjMinusO boundaryEdgeFootprint J K hJne hKne hJsub
      hKsub hJK y j hcenter hassign hdiagPlus hdiagMinus hyJ hyK
  have hdisjJK : Disjoint J.cells K.cells := by
    rcases hJK with ⟨_, _, hd, _⟩ | ⟨hE, _⟩ | ⟨hE, _⟩
    · exact hd
    · exact (Finset.not_nonempty_iff_eq_empty.mpr hE hJne).elim
    · exact (Finset.not_nonempty_iff_eq_empty.mpr hE hKne).elim
  have hpathJK : SimpleGridPath
      (BoundaryFootprintVertices J ∩ BoundaryFootprintVertices K)
      (BoundaryFootprintEdges J ∩ BoundaryFootprintEdges K) := by
    rcases hJK with ⟨_, _, _, hp⟩ | ⟨hE, _⟩ | ⟨hE, _⟩
    · exact hp
    · exact (Finset.not_nonempty_iff_eq_empty.mpr hE hJne).elim
    · exact (Finset.not_nonempty_iff_eq_empty.mpr hE hKne).elim
  have hyJK : y ∈ BoundaryFootprintVertices J ∩ BoundaryFootprintVertices K :=
    ⟨hyJ, hyK⟩
  obtain ⟨e, hye, heJK⟩ := SimpleGridPathVertexIncidentEdge _ _ hpathJK y hyJK
  have heFoot : e ∈ FootprintEdges J ∩ FootprintEdges K :=
    ⟨boundaryEdgeFootprint J e heJK.1, boundaryEdgeFootprint K e heJK.2⟩
  obtain ⟨k, hk, hkocc⟩ := P3102T2CommonEdgeSectorTransition J K y e
    hdisjJK hye heFoot
  have noAdjacent (k : Fin 4) :
      ¬ ((LatticeVertexIncidentCell y k ∈ J.cells ∧
            LatticeVertexIncidentCell y (k + 1) ∈ K.cells) ∨
          (LatticeVertexIncidentCell y k ∈ K.cells ∧
            LatticeVertexIncidentCell y (k + 1) ∈ J.cells)) :=
    (by
    have hJcenter : LatticeVertexIncidentCell y j ∉ J.cells := by
      intro h
      exact (Finset.disjoint_left.mp hdisjPlusO (hJsub h) hcenter).elim
    have hKcenter : LatticeVertexIncidentCell y j ∉ K.cells := by
      intro h
      exact (Finset.disjoint_left.mp hdisjMinusO (hKsub h) hcenter).elim
    have hJdiag : LatticeVertexIncidentCell y (j + 2) ∉ J.cells :=
      fun h => hdiagPlus (hJsub h)
    have hKdiag : LatticeVertexIncidentCell y (j + 2) ∉ K.cells :=
      fun h => hdiagMinus (hKsub h)
    rcases hassign with ⟨h1plus, h3minus⟩ | ⟨h1minus, h3plus⟩
    · have hJother : LatticeVertexIncidentCell y (j + 3) ∉ J.cells := by
        intro h
        exact (Finset.disjoint_left.mp hdisjoint (hJsub h) h3minus).elim
      have hKother : LatticeVertexIncidentCell y (j + 1) ∉ K.cells := by
        intro h
        exact (Finset.disjoint_left.mp hdisjoint.symm (hKsub h) h1plus).elim
      clear hJsub hKsub hcenter hdiagPlus hdiagMinus hdisjoint hJne hKne hJK hdisjJK hpathJK
          hyJK e hye heJK heFoot hk hkocc h1plus h3minus
      fin_cases j <;> (fin_cases k <;> intro hp <;>
        rcases hp with ⟨hJL, hKR⟩ | ⟨hKL, hJR⟩ <;> first
        | exact hJcenter (by simpa [LatticeVertexIncidentCell] using hJL)
        | exact hJcenter (by simpa [LatticeVertexIncidentCell] using hJR)
        | exact hKcenter (by simpa [LatticeVertexIncidentCell] using hKL)
        | exact hKcenter (by simpa [LatticeVertexIncidentCell] using hKR)
        | exact hJdiag (by simpa [LatticeVertexIncidentCell] using hJL)
        | exact hJdiag (by simpa [LatticeVertexIncidentCell] using hJR)
        | exact hKdiag (by simpa [LatticeVertexIncidentCell] using hKL)
        | exact hKdiag (by simpa [LatticeVertexIncidentCell] using hKR)
        )
    · have hJother : LatticeVertexIncidentCell y (j + 1) ∉ J.cells := by
        intro h
        exact (Finset.disjoint_left.mp hdisjoint (hJsub h) h1minus).elim
      have hKother : LatticeVertexIncidentCell y (j + 3) ∉ K.cells := by
        intro h
        exact (Finset.disjoint_left.mp hdisjoint.symm (hKsub h) h3plus).elim
      clear hJsub hKsub hcenter hdiagPlus hdiagMinus hdisjoint hJne hKne hJK hdisjJK hpathJK
          hyJK e hye heJK heFoot hk hkocc h1minus h3plus
      fin_cases j <;> (fin_cases k <;> intro hp <;>
        rcases hp with ⟨hJL, hKR⟩ | ⟨hKL, hJR⟩ <;> first
        | exact hJcenter (by simpa [LatticeVertexIncidentCell] using hJL)
        | exact hJcenter (by simpa [LatticeVertexIncidentCell] using hJR)
        | exact hKcenter (by simpa [LatticeVertexIncidentCell] using hKL)
        | exact hKcenter (by simpa [LatticeVertexIncidentCell] using hKR)
        | exact hJdiag (by simpa [LatticeVertexIncidentCell] using hJL)
        | exact hJdiag (by simpa [LatticeVertexIncidentCell] using hJR)
        | exact hKdiag (by simpa [LatticeVertexIncidentCell] using hKL)
        | exact hKdiag (by simpa [LatticeVertexIncidentCell] using hKR)
        )
    )
  exact noAdjacent k (by
    rcases hkocc with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · exact Or.inl ⟨hfirst, hsecond⟩
    · exact Or.inr ⟨hfirst, hsecond⟩)

private theorem cornerRescue :
    (by
      classical
      exact
        ∀ (Dplus : ProtoTile), ∀ (Dminus : ProtoTile), ∀ (O : ProtoTile), ∀ (O' : ProtoTile), ∀
            (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (U : ProtoTile), ∀ (V : ProtoTile),
            (Finset.Nonempty O.cells) → ((Finset.Nonempty X.cells) → ((Finset.Nonempty Y.cells) →
            ((Finset.Nonempty U.cells) → ((Finset.Nonempty V.cells) → ((PrecursorBoundaryArcData
            Dplus Dminus O O' X Y U V) → ((NoCheckerboardCellVertex (Dplus.cells : Set
            LatticeCell)) → ((NoCheckerboardCellVertex (Dminus.cells : Set LatticeCell)) →
            ((Disjoint Dplus.cells O.cells) → ((Disjoint Dminus.cells O.cells) → ((∀ (T :
            ProtoTile), ∀ (y : GaussianInt), ∀ (j : Fin 4), ((LatticeVertexIncidentCell y j ∈
            T.cells ∧ LatticeVertexIncidentCell y (j + 1) ∉ T.cells) ∨ (LatticeVertexIncidentCell
            y j ∉ T.cells ∧ LatticeVertexIncidentCell y (j + 1) ∈ T.cells)) → (y ∈
            BoundaryFootprintVertices T)) → ((∀ (y : GaussianInt), ∀ (j : Fin 4),
            ((LatticeVertexIncidentCell y j ∈ O.cells ∧ LatticeVertexIncidentCell y (j + 1) ∉
            O.cells) ∨ (LatticeVertexIncidentCell y j ∉ O.cells ∧ LatticeVertexIncidentCell y (j
            + 1) ∈ O.cells)) → ((LatticeVertexIncidentCell y j ∉ O.cells) →
            (LatticeVertexIncidentCell y j ∈ Dplus.cells ∨ LatticeVertexIncidentCell y j ∈
            Dminus.cells))) → ((∀ (y : GaussianInt), ∀ (j : Fin 4), ((LatticeVertexIncidentCell y
            j ∈ O.cells ∧ LatticeVertexIncidentCell y (j + 1) ∉ O.cells) ∨
            (LatticeVertexIncidentCell y j ∉ O.cells ∧ LatticeVertexIncidentCell y (j + 1) ∈
            O.cells)) → ((LatticeVertexIncidentCell y (j + 1) ∉ O.cells) →
            (LatticeVertexIncidentCell y (j + 1) ∈ Dplus.cells ∨ LatticeVertexIncidentCell y (j +
            1) ∈ Dminus.cells))) → ((∀ (T : ProtoTile), (NoCheckerboardCellVertex (T.cells : Set
            LatticeCell)) → (∀ (y : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell y (j
            + 1) ∈ T.cells) → ((LatticeVertexIncidentCell y (j + 3) ∈ T.cells) →
            ((LatticeVertexIncidentCell y j ∉ T.cells) → (LatticeVertexIncidentCell y (j + 2) ∈
            T.cells))))) → ((∀ (J : ProtoTile), ∀ (K : ProtoTile), (J.cells.Nonempty) →
            ((K.cells.Nonempty) → ((J.cells ⊆ Dplus.cells) → ((K.cells ⊆ Dminus.cells) →
            ((TileTouching J K) → (∀ (y : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell
            y j ∈ O.cells) → (((LatticeVertexIncidentCell y (j + 1) ∈ Dplus.cells ∧
            LatticeVertexIncidentCell y (j + 3) ∈ Dminus.cells) ∨ (LatticeVertexIncidentCell y (j
            + 1) ∈ Dminus.cells ∧ LatticeVertexIncidentCell y (j + 3) ∈ Dplus.cells)) →
            ((LatticeVertexIncidentCell y (j + 2) ∉ Dplus.cells) → ((LatticeVertexIncidentCell y
            (j + 2) ∉ Dminus.cells) → ((y ∈ BoundaryFootprintVertices J) → ((y ∈
            BoundaryFootprintVertices K) → (False)))))))))))) → (∀ (y : GaussianInt), ∀ (j : Fin
            (4 : ℕ)), LatticeVertexIncidentCell y j ∈ O.cells → LatticeVertexIncidentCell y (j +
            (2 : Fin (4 : ℕ))) ∉ O.cells → LatticeVertexIncidentCell y (j + (1 : Fin (4 : ℕ))) ∉
            O.cells → LatticeVertexIncidentCell y (j + (3 : Fin (4 : ℕ))) ∉ O.cells →
            LatticeVertexIncidentCell y (j + (2 : Fin (4 : ℕ))) ∈ Dplus.cells ∨
            LatticeVertexIncidentCell y (j + (2 : Fin (4 : ℕ))) ∈ Dminus.cells))))))))))))))) )
            := by
  classical
  intro Dplus Dminus O O' X Y U V hO hX hY hU hV data hcheckPlus hcheckMinus hdisjPlusO
      hdisjMinusO boundaryVertexOfCross coverLeft coverRight noCheckerboardDiagonal
      mixedCornerContradiction y j hcenter hdiagO hside1O hside3O
  by_cases hdiagPlus : LatticeVertexIncidentCell y (j + 2) ∈ Dplus.cells
  · exact Or.inl hdiagPlus
  by_cases hdiagMinus : LatticeVertexIncidentCell y (j + 2) ∈ Dminus.cells
  · exact Or.inr hdiagMinus
  have hOafter : LatticeVertexIncidentCell y (j + 3 + 1) ∈ O.cells := by
    fin_cases j <;> simpa [LatticeVertexIncidentCell] using hcenter
  have hcross1 : (LatticeVertexIncidentCell y j ∈ O.cells ∧
      LatticeVertexIncidentCell y (j + 1) ∉ O.cells) := ⟨hcenter, hside1O⟩
  have hcross3 : (LatticeVertexIncidentCell y (j + 3) ∉ O.cells ∧
      LatticeVertexIncidentCell y (j + 3 + 1) ∈ O.cells) := ⟨hside3O, hOafter⟩
  have hs1 := coverRight y j (Or.inl hcross1) hside1O
  have hs3 := coverLeft y (j + 3) (Or.inr hcross3) hside3O
  have hOvertex := boundaryVertexOfCross O y j (Or.inl hcross1)
  rcases hs1 with hs1p | hs1m <;> rcases hs3 with hs3p | hs3m
  · exact Or.inl (noCheckerboardDiagonal Dplus hcheckPlus y j hs1p hs3p
      (fun h => (Finset.disjoint_left.mp hdisjPlusO h hcenter).elim))
  · exfalso
    rcases data.branch with hpos | hzero
    · rcases hpos with ⟨_, ⟨plusArc, minusArc, hfields⟩⟩
      rcases hfields with ⟨_, _, _, _, _, _, hplusEq, hminusEq, _, _, _,
        hintersection, _, _⟩
      have hcenterPlusNot : LatticeVertexIncidentCell y j ∉ Dplus.cells := by
        intro h
        exact (Finset.disjoint_left.mp hdisjPlusO h hcenter).elim
      have hwrapPlusNot : LatticeVertexIncidentCell y (j + 3 + 1) ∉ Dplus.cells := by
        intro h
        have hcenter' : LatticeVertexIncidentCell y (j + 3 + 1) ∈ O.cells := by
          fin_cases j <;> simpa [LatticeVertexIncidentCell] using hcenter
        exact (Finset.disjoint_left.mp hdisjPlusO h hcenter').elim
      have hwrapMinusNot : LatticeVertexIncidentCell y (j + 3 + 1) ∉ Dminus.cells := by
        intro h
        have hcenter' : LatticeVertexIncidentCell y (j + 3 + 1) ∈ O.cells := by
          fin_cases j <;> simpa [LatticeVertexIncidentCell] using hcenter
        exact (Finset.disjoint_left.mp hdisjMinusO h hcenter').elim
      have hplusVertex : y ∈ BoundaryFootprintVertices Dplus :=
        boundaryVertexOfCross Dplus y j (Or.inr ⟨hcenterPlusNot, hs1p⟩)
      have hminusVertex : y ∈ BoundaryFootprintVertices Dminus := by
        have hcrossM : LatticeVertexIncidentCell y (j + 3) ∈ Dminus.cells ∧
            LatticeVertexIncidentCell y (j + 3 + 1) ∉ Dminus.cells :=
          ⟨hs3m, hwrapMinusNot⟩
        exact boundaryVertexOfCross Dminus y (j + 3) (Or.inl hcrossM)
      have hplusArc : y ∈ (plusArc.toFinset : Set GaussianInt) := by
        rw [hplusEq]
        exact ⟨hplusVertex, hOvertex⟩
      have hminusArc : y ∈ (minusArc.toFinset : Set GaussianInt) := by
        rw [hminusEq]
        exact ⟨hminusVertex, hOvertex⟩
      have hlabels : y = data.a ∨ y = data.b := by
        have hmem : y ∈ (plusArc.toFinset : Set GaussianInt) ∩
            (minusArc.toFinset : Set GaussianInt) := ⟨hplusArc, hminusArc⟩
        rw [hintersection] at hmem
        simpa using hmem
      rcases hlabels with hya | hyb
      · have htr := (data.first_transition y).mpr hya
        have hXvertex := htr.1
        have hYvertex := htr.2.1
        exact mixedCornerContradiction X Y hX hY data.first_plus_child
          data.first_minus_child data.first_touching.1 y j hcenter
          (Or.inl ⟨hs1p, hs3m⟩) hdiagPlus hdiagMinus hXvertex hYvertex
      · have htr := (data.second_transition y).mpr hyb
        have hUvertex := htr.1
        have hVvertex := htr.2.1
        exact mixedCornerContradiction U V hU hV data.second_plus_child
          data.second_minus_child data.second_touching.1 y j hcenter
          (Or.inl ⟨hs1p, hs3m⟩) hdiagPlus hdiagMinus hUvertex hVvertex
    · exact (Finset.not_nonempty_iff_eq_empty.mpr hzero.1 hO).elim
  · exfalso
    rcases data.branch with hpos | hzero
    · rcases hpos with ⟨_, ⟨plusArc, minusArc, hfields⟩⟩
      rcases hfields with ⟨_, _, _, _, _, _, hplusEq, hminusEq, _, _, _,
        hintersection, _, _⟩
      have hcenterMinusNot : LatticeVertexIncidentCell y j ∉ Dminus.cells := by
        intro h
        exact (Finset.disjoint_left.mp hdisjMinusO h hcenter).elim
      have hwrapMinusNot : LatticeVertexIncidentCell y (j + 3 + 1) ∉ Dminus.cells := by
        intro h
        have hcenter' : LatticeVertexIncidentCell y (j + 3 + 1) ∈ O.cells := by
          fin_cases j <;> simpa [LatticeVertexIncidentCell] using hcenter
        exact (Finset.disjoint_left.mp hdisjMinusO h hcenter').elim
      have hwrapPlusNot : LatticeVertexIncidentCell y (j + 3 + 1) ∉ Dplus.cells := by
        intro h
        have hcenter' : LatticeVertexIncidentCell y (j + 3 + 1) ∈ O.cells := by
          fin_cases j <;> simpa [LatticeVertexIncidentCell] using hcenter
        exact (Finset.disjoint_left.mp hdisjPlusO h hcenter').elim
      have hminusVertex : y ∈ BoundaryFootprintVertices Dminus :=
        boundaryVertexOfCross Dminus y j (Or.inr ⟨hcenterMinusNot, hs1m⟩)
      have hplusVertex : y ∈ BoundaryFootprintVertices Dplus := by
        have hcrossP : LatticeVertexIncidentCell y (j + 3) ∈ Dplus.cells ∧
            LatticeVertexIncidentCell y (j + 3 + 1) ∉ Dplus.cells :=
          ⟨hs3p, hwrapPlusNot⟩
        exact boundaryVertexOfCross Dplus y (j + 3) (Or.inl hcrossP)
      have hplusArc : y ∈ (plusArc.toFinset : Set GaussianInt) := by
        rw [hplusEq]
        exact ⟨hplusVertex, hOvertex⟩
      have hminusArc : y ∈ (minusArc.toFinset : Set GaussianInt) := by
        rw [hminusEq]
        exact ⟨hminusVertex, hOvertex⟩
      have hlabels : y = data.a ∨ y = data.b := by
        have hmem : y ∈ (plusArc.toFinset : Set GaussianInt) ∩
            (minusArc.toFinset : Set GaussianInt) := ⟨hplusArc, hminusArc⟩
        rw [hintersection] at hmem
        simpa using hmem
      rcases hlabels with hya | hyb
      · have htr := (data.first_transition y).mpr hya
        exact mixedCornerContradiction X Y hX hY data.first_plus_child
          data.first_minus_child data.first_touching.1 y j hcenter
          (Or.inr ⟨hs1m, hs3p⟩) hdiagPlus hdiagMinus htr.1 htr.2.1
      · have htr := (data.second_transition y).mpr hyb
        exact mixedCornerContradiction U V hU hV data.second_plus_child
          data.second_minus_child data.second_touching.1 y j hcenter
          (Or.inr ⟨hs1m, hs3p⟩) hdiagPlus hdiagMinus htr.1 htr.2.1
    · exact (Finset.not_nonempty_iff_eq_empty.mpr hzero.1 hO).elim
  · exact Or.inr (noCheckerboardDiagonal Dminus hcheckMinus y j hs1m hs3m
      (fun h => (Finset.disjoint_left.mp hdisjMinusO h hcenter).elim))

private theorem singletonCorner :
    (by
      classical
      exact
        ∀ (y : GaussianInt), ∀ (j : Fin (4 : ℕ)), y ∈ FootprintVertices
            (⟨{LatticeVertexIncidentCell y j}, LatticeVertexIncidentCell y j⟩ : ProtoTile) ) := by
  classical
  intro y j
  simp only [FootprintVertices, Finset.singleton_nonempty, ite_true,
    Set.mem_ofPred_eq]
  refine ⟨LatticeVertexIncidentCell y j, Finset.mem_singleton_self _, ?_⟩
  fin_cases j <;> simp [LatticeVertexIncidentCell, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc]

private theorem ha :
    (by
      classical
      exact
        ∀ (y : GaussianInt), ∀ (a : GaussianInt), (y ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile))
            → (∃ j : Fin 4, a = LatticeVertexIncidentCell y j) ) := by
  classical
  intro y a hya
  simp only [FootprintVertices, Finset.singleton_nonempty, ite_true,
    Set.mem_ofPred_eq] at hya
  rcases hya with ⟨c, hc, h⟩
  simp only [Finset.mem_singleton] at hc
  rw [hc] at h
  clear hc c
  rcases h with h0 | h1 | h2 | h3
  · exact ⟨0, by simpa [LatticeVertexIncidentCell] using h0.symm⟩
  · exact ⟨1, by rw [h1]; simp [LatticeVertexIncidentCell]⟩
  · exact ⟨3, by rw [h2]; simp [LatticeVertexIncidentCell]⟩
  · exact ⟨2, by rw [h3]; simp [LatticeVertexIncidentCell, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc]⟩

private theorem coverAt :
    (by
      classical
      exact
        ∀ (Dplus : ProtoTile), ∀ (Dminus : ProtoTile), ∀ (O : ProtoTile), (∀ (y : GaussianInt), ∀
            (j : Fin 4), ((LatticeVertexIncidentCell y j ∈ O.cells ∧ LatticeVertexIncidentCell y
            (j + 1) ∉ O.cells) ∨ (LatticeVertexIncidentCell y j ∉ O.cells ∧
            LatticeVertexIncidentCell y (j + 1) ∈ O.cells)) → ((LatticeVertexIncidentCell y j ∉
            O.cells) → (LatticeVertexIncidentCell y j ∈ Dplus.cells ∨ LatticeVertexIncidentCell y
            j ∈ Dminus.cells))) → ((∀ (y : GaussianInt), ∀ (j : Fin 4),
            ((LatticeVertexIncidentCell y j ∈ O.cells ∧ LatticeVertexIncidentCell y (j + 1) ∉
            O.cells) ∨ (LatticeVertexIncidentCell y j ∉ O.cells ∧ LatticeVertexIncidentCell y (j
            + 1) ∈ O.cells)) → ((LatticeVertexIncidentCell y (j + 1) ∉ O.cells) →
            (LatticeVertexIncidentCell y (j + 1) ∈ Dplus.cells ∨ LatticeVertexIncidentCell y (j +
            1) ∈ Dminus.cells))) → ((∀ (y : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell y j ∈ O.cells) → ((LatticeVertexIncidentCell y (j + 2) ∉
            O.cells) → ((LatticeVertexIncidentCell y (j + 1) ∉ O.cells) →
            ((LatticeVertexIncidentCell y (j + 3) ∉ O.cells) → (LatticeVertexIncidentCell y (j +
            2) ∈ Dplus.cells ∨ LatticeVertexIncidentCell y (j + 2) ∈ Dminus.cells))))) → (∀ (y :
            GaussianInt), ∀ (jo : Fin (4 : ℕ)), (LatticeVertexIncidentCell y jo ∈ O.cells) → (∀
            (i : Fin (4 : ℕ)), LatticeVertexIncidentCell y i ∈ O.cells ∨
            LatticeVertexIncidentCell y i ∈ Dplus.cells ∨ LatticeVertexIncidentCell y i ∈
            Dminus.cells)))) ) := by
  classical
  intro Dplus Dminus O coverLeft coverRight cornerRescue y jo hjo i
  by_cases hiO : LatticeVertexIncidentCell y i ∈ O.cells
  · exact Or.inl hiO
  · fin_cases jo
    · fin_cases i
      · exact (hiO (by simpa [LatticeVertexIncidentCell] using hjo)).elim
      · right
        have hc := coverRight y 0
          (Or.inl ⟨by simpa [LatticeVertexIncidentCell] using hjo,
            by simpa [LatticeVertexIncidentCell] using hiO⟩)
          (by simpa [LatticeVertexIncidentCell] using hiO)
        simpa [LatticeVertexIncidentCell] using hc
      · by_cases hs1 : LatticeVertexIncidentCell y 1 ∈ O.cells
        · right
          have hc := coverRight y 1
            (Or.inl ⟨by simpa [LatticeVertexIncidentCell] using hs1,
              by simpa [LatticeVertexIncidentCell] using hiO⟩)
            (by simpa [LatticeVertexIncidentCell] using hiO)
          simpa [LatticeVertexIncidentCell] using hc
        · by_cases hs3 : LatticeVertexIncidentCell y 3 ∈ O.cells
          · right
            have hc := coverLeft y 2
              (Or.inr ⟨by simpa [LatticeVertexIncidentCell] using hiO,
                by simpa [LatticeVertexIncidentCell] using hs3⟩)
              (by simpa [LatticeVertexIncidentCell] using hiO)
            simpa [LatticeVertexIncidentCell] using hc
          · right
            have hc := cornerRescue y 0 (by simpa [LatticeVertexIncidentCell] using hjo)
              (by simpa [LatticeVertexIncidentCell] using hiO)
              (by simpa [LatticeVertexIncidentCell] using hs1)
              (by simpa [LatticeVertexIncidentCell] using hs3)
            simpa [LatticeVertexIncidentCell] using hc
      · right
        have hc := coverLeft y 3
          (Or.inr ⟨by simpa [LatticeVertexIncidentCell] using hiO,
            by simpa [LatticeVertexIncidentCell] using hjo⟩)
          (by simpa [LatticeVertexIncidentCell] using hiO)
        simpa [LatticeVertexIncidentCell] using hc
    · fin_cases i
      · right
        have hc := coverLeft y 0
          (Or.inr ⟨by simpa [LatticeVertexIncidentCell] using hiO,
            by simpa [LatticeVertexIncidentCell] using hjo⟩)
          (by simpa [LatticeVertexIncidentCell] using hiO)
        simpa [LatticeVertexIncidentCell] using hc
      · exact (hiO (by simpa [LatticeVertexIncidentCell] using hjo)).elim
      · right
        have hc := coverRight y 1
          (Or.inl ⟨by simpa [LatticeVertexIncidentCell] using hjo,
            by simpa [LatticeVertexIncidentCell] using hiO⟩)
          (by simpa [LatticeVertexIncidentCell] using hiO)
        simpa [LatticeVertexIncidentCell] using hc
      · by_cases hs1 : LatticeVertexIncidentCell y 2 ∈ O.cells
        · right
          have hc := coverRight y 2
            (Or.inl ⟨by simpa [LatticeVertexIncidentCell] using hs1,
              by simpa [LatticeVertexIncidentCell] using hiO⟩)
            (by simpa [LatticeVertexIncidentCell] using hiO)
          simpa [LatticeVertexIncidentCell] using hc
        · by_cases hs3 : LatticeVertexIncidentCell y 0 ∈ O.cells
          · right
            have hc := coverLeft y 3
              (Or.inr ⟨by simpa [LatticeVertexIncidentCell] using hiO,
                by simpa [LatticeVertexIncidentCell] using hs3⟩)
              (by simpa [LatticeVertexIncidentCell] using hiO)
            simpa [LatticeVertexIncidentCell] using hc
          · right
            have hc := cornerRescue y 1 (by simpa [LatticeVertexIncidentCell] using hjo)
              (by simpa [LatticeVertexIncidentCell] using hiO)
              (by simpa [LatticeVertexIncidentCell] using hs1)
              (by simpa [LatticeVertexIncidentCell] using hs3)
            simpa [LatticeVertexIncidentCell] using hc
    · fin_cases i
      · by_cases hs1 : LatticeVertexIncidentCell y 3 ∈ O.cells
        · right
          have hc := coverRight y 3
            (Or.inl ⟨by simpa [LatticeVertexIncidentCell] using hs1,
              by simpa [LatticeVertexIncidentCell] using hiO⟩)
            (by simpa [LatticeVertexIncidentCell] using hiO)
          simpa [LatticeVertexIncidentCell] using hc
        · by_cases hs3 : LatticeVertexIncidentCell y 1 ∈ O.cells
          · right
            have hc := coverLeft y 0
              (Or.inr ⟨by simpa [LatticeVertexIncidentCell] using hiO,
                by simpa [LatticeVertexIncidentCell] using hs3⟩)
              (by simpa [LatticeVertexIncidentCell] using hiO)
            simpa [LatticeVertexIncidentCell] using hc
          · right
            have hc := cornerRescue y 2 (by simpa [LatticeVertexIncidentCell] using hjo)
              (by simpa [LatticeVertexIncidentCell] using hiO)
              (by simpa [LatticeVertexIncidentCell] using hs1)
              (by simpa [LatticeVertexIncidentCell] using hs3)
            simpa [LatticeVertexIncidentCell] using hc
      · right
        have hc := coverLeft y 1
          (Or.inr ⟨by simpa [LatticeVertexIncidentCell] using hiO,
            by simpa [LatticeVertexIncidentCell] using hjo⟩)
          (by simpa [LatticeVertexIncidentCell] using hiO)
        simpa [LatticeVertexIncidentCell] using hc
      · exact (hiO (by simpa [LatticeVertexIncidentCell] using hjo)).elim
      · right
        have hc := coverRight y 2
          (Or.inl ⟨by simpa [LatticeVertexIncidentCell] using hjo,
            by simpa [LatticeVertexIncidentCell] using hiO⟩)
          (by simpa [LatticeVertexIncidentCell] using hiO)
        simpa [LatticeVertexIncidentCell] using hc
    · fin_cases i
      · right
        have hc := coverRight y 3
          (Or.inl ⟨by simpa [LatticeVertexIncidentCell] using hjo,
            by simpa [LatticeVertexIncidentCell] using hiO⟩)
          (by simpa [LatticeVertexIncidentCell] using hiO)
        simpa [LatticeVertexIncidentCell] using hc
      · by_cases hs1 : LatticeVertexIncidentCell y 0 ∈ O.cells
        · right
          have hc := coverRight y 0
            (Or.inl ⟨by simpa [LatticeVertexIncidentCell] using hs1,
              by simpa [LatticeVertexIncidentCell] using hiO⟩)
            (by simpa [LatticeVertexIncidentCell] using hiO)
          simpa [LatticeVertexIncidentCell] using hc
        · by_cases hs3 : LatticeVertexIncidentCell y 2 ∈ O.cells
          · right
            have hc := coverLeft y 1
              (Or.inr ⟨by simpa [LatticeVertexIncidentCell] using hiO,
                by simpa [LatticeVertexIncidentCell] using hs3⟩)
              (by simpa [LatticeVertexIncidentCell] using hiO)
            simpa [LatticeVertexIncidentCell] using hc
          · right
            have hc := cornerRescue y 3 (by simpa [LatticeVertexIncidentCell] using hjo)
              (by simpa [LatticeVertexIncidentCell] using hiO)
              (by simpa [LatticeVertexIncidentCell] using hs1)
              (by simpa [LatticeVertexIncidentCell] using hs3)
            simpa [LatticeVertexIncidentCell] using hc
      · right
        have hc := coverLeft y 2
          (Or.inr ⟨by simpa [LatticeVertexIncidentCell] using hiO,
            by simpa [LatticeVertexIncidentCell] using hjo⟩)
          (by simpa [LatticeVertexIncidentCell] using hiO)
        simpa [LatticeVertexIncidentCell] using hc
      · exact (hiO (by simpa [LatticeVertexIncidentCell] using hjo)).elim

end ContactStarCases

theorem P4638T1ContactStarCoverage (Dplus Dminus O O' X Y U V : ProtoTile)
    (hO : O.cells.Nonempty) (hOL : LatticeTile O)
    (hplus : LatticeTile Dplus) (hminus : LatticeTile Dminus)
    (htplus : TileTouching Dplus O) (htminus : TileTouching Dminus O)
    (hdisjoint : Disjoint Dplus.cells Dminus.cells)
    (hX : X.cells.Nonempty) (hY : Y.cells.Nonempty)
    (hU : U.cells.Nonempty) (hV : V.cells.Nonempty)
    (data : PrecursorBoundaryArcData Dplus Dminus O O' X Y U V)
    (hedges : ∀ e ∈ BoundaryFootprintEdges O,
      e ∈ BoundaryFootprintEdges Dplus ∨ e ∈ BoundaryFootprintEdges Dminus) :
    ∀ y ∈ FootprintVertices O, ∀ a : GaussianInt,
      y ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) →
        a ∈ O.cells ∨ a ∈ Dplus.cells ∨ a ∈ Dminus.cells := by
-- BODY
  classical
  have hDplus : Dplus.cells.Nonempty :=
    (LatticeTileGridStructure Dplus hplus).1.1
  have hDminus : Dminus.cells.Nonempty :=
    (LatticeTileGridStructure Dminus hminus).1.1
  have hcheckO : NoCheckerboardCellVertex (O.cells : Set LatticeCell) :=
    (LatticeTileGridStructure O hOL).2.1
  have hcheckPlus : NoCheckerboardCellVertex (Dplus.cells : Set LatticeCell) :=
    (LatticeTileGridStructure Dplus hplus).2.1
  have hcheckMinus : NoCheckerboardCellVertex (Dminus.cells : Set LatticeCell) :=
    (LatticeTileGridStructure Dminus hminus).2.1
  have hdisjPlusO := ContactStarCases.hdisjPlusO Dplus O hO htplus hDplus
  have hdisjMinusO := ContactStarCases.hdisjMinusO Dminus O hO htminus hDminus
  have hpathPlusO := ContactStarCases.hpathPlusO Dplus O hO htplus hDplus
  have hpathMinusO := ContactStarCases.hpathMinusO Dminus O hO htminus hDminus
  have boundaryEdgeFootprint (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) := ContactStarCases.boundaryEdgeFootprint T e he
  let edgeAt (y : GaussianInt) : Fin 4 → Finset GaussianInt :=
    ![{y, y + ⟨0, 1⟩}, {y - 1, y},
      {y - ⟨0, 1⟩, y}, {y, y + 1}]
  let offsetAt : Fin 4 → GaussianInt := ![⟨0, 1⟩, -1, -⟨0, 1⟩, 1]
  have edgeAt_eq (y : GaussianInt) (i : Fin 4) := ContactStarCases.edgeAt_eq y i
  have offsetAt_injective (i j : Fin 4) (h : offsetAt i = offsetAt j) :=
      ContactStarCases.offsetAt_injective i j h
  have edgeAt_injective (y : GaussianInt) (i j : Fin 4)
      (h : edgeAt y i = edgeAt y j) := ContactStarCases.edgeAt_injective edgeAt_eq
          offsetAt_injective y i j h
  have edgeCross (y : GaussianInt) (j : Fin 4)
      (hcross : (LatticeVertexIncidentCell y j ∈ O.cells ∧
          LatticeVertexIncidentCell y (j + 1) ∉ O.cells) ∨
        (LatticeVertexIncidentCell y j ∉ O.cells ∧
          LatticeVertexIncidentCell y (j + 1) ∈ O.cells)) := ContactStarCases.edgeCross Dplus
              Dminus O hedges hdisjPlusO hdisjMinusO boundaryEdgeFootprint edgeAt_injective y j
              hcross
  have boundaryEdgeOfCross (T : ProtoTile) (y : GaussianInt) (j : Fin 4)
      (hcross : (LatticeVertexIncidentCell y j ∈ T.cells ∧
          LatticeVertexIncidentCell y (j + 1) ∉ T.cells) ∨
        (LatticeVertexIncidentCell y j ∉ T.cells ∧
          LatticeVertexIncidentCell y (j + 1) ∈ T.cells)) :=
              ContactStarGeometry.boundaryEdgeOfCross T y j hcross
  have boundaryVertexOfCross (T : ProtoTile) (y : GaussianInt) (j : Fin 4)
      (hcross : (LatticeVertexIncidentCell y j ∈ T.cells ∧
          LatticeVertexIncidentCell y (j + 1) ∉ T.cells) ∨
        (LatticeVertexIncidentCell y j ∉ T.cells ∧
          LatticeVertexIncidentCell y (j + 1) ∈ T.cells)) :=
              ContactStarCases.boundaryVertexOfCross boundaryEdgeOfCross T y j hcross
  have incident (T : ProtoTile) (y : GaussianInt)
      (hne : T.cells.Nonempty) (hy : y ∈ FootprintVertices T) := ContactStarCases.incident T y
          hne hy
  have coverLeft (y : GaussianInt) (j : Fin 4)
      (hcross : (LatticeVertexIncidentCell y j ∈ O.cells ∧
          LatticeVertexIncidentCell y (j + 1) ∉ O.cells) ∨
        (LatticeVertexIncidentCell y j ∉ O.cells ∧
          LatticeVertexIncidentCell y (j + 1) ∈ O.cells))
      (hnot : LatticeVertexIncidentCell y j ∉ O.cells) := ContactStarCases.coverLeft Dplus Dminus
          O hdisjPlusO hdisjMinusO edgeCross y j hcross hnot
  have coverRight (y : GaussianInt) (j : Fin 4)
      (hcross : (LatticeVertexIncidentCell y j ∈ O.cells ∧
          LatticeVertexIncidentCell y (j + 1) ∉ O.cells) ∨
        (LatticeVertexIncidentCell y j ∉ O.cells ∧
          LatticeVertexIncidentCell y (j + 1) ∈ O.cells))
      (hnot : LatticeVertexIncidentCell y (j + 1) ∉ O.cells) := ContactStarCases.coverRight Dplus
          Dminus O hdisjPlusO hdisjMinusO edgeCross y j hcross hnot
  have noCheckerboardDiagonal (T : ProtoTile)
      (hT : NoCheckerboardCellVertex (T.cells : Set LatticeCell))
      (y : GaussianInt) (j : Fin 4)
      (hside1 : LatticeVertexIncidentCell y (j + 1) ∈ T.cells)
      (hside3 : LatticeVertexIncidentCell y (j + 3) ∈ T.cells)
      (hcenter : LatticeVertexIncidentCell y j ∉ T.cells) :=
          ContactStarCases.noCheckerboardDiagonal T hT y j hside1 hside3 hcenter
  have mixedCornerContradiction (J K : ProtoTile)
      (hJne : J.cells.Nonempty) (hKne : K.cells.Nonempty)
      (hJsub : J.cells ⊆ Dplus.cells) (hKsub : K.cells ⊆ Dminus.cells)
      (hJK : TileTouching J K) (y : GaussianInt) (j : Fin 4)
      (hcenter : LatticeVertexIncidentCell y j ∈ O.cells)
      (hassign : (LatticeVertexIncidentCell y (j + 1) ∈ Dplus.cells ∧
          LatticeVertexIncidentCell y (j + 3) ∈ Dminus.cells) ∨
        (LatticeVertexIncidentCell y (j + 1) ∈ Dminus.cells ∧
          LatticeVertexIncidentCell y (j + 3) ∈ Dplus.cells))
      (hdiagPlus : LatticeVertexIncidentCell y (j + 2) ∉ Dplus.cells)
      (hdiagMinus : LatticeVertexIncidentCell y (j + 2) ∉ Dminus.cells)
      (hyJ : y ∈ BoundaryFootprintVertices J)
      (hyK : y ∈ BoundaryFootprintVertices K) := ContactStarCases.mixedCornerContradiction Dplus
          Dminus O hdisjoint hdisjPlusO hdisjMinusO boundaryEdgeFootprint J K hJne hKne hJsub
          hKsub hJK y j hcenter hassign hdiagPlus hdiagMinus hyJ hyK
  have cornerRescue (y : GaussianInt) (j : Fin 4)
      (hcenter : LatticeVertexIncidentCell y j ∈ O.cells)
      (hdiagO : LatticeVertexIncidentCell y (j + 2) ∉ O.cells)
      (hside1O : LatticeVertexIncidentCell y (j + 1) ∉ O.cells)
      (hside3O : LatticeVertexIncidentCell y (j + 3) ∉ O.cells) := ContactStarCases.cornerRescue
          Dplus Dminus O O' X Y U V hO hX hY hU hV data hcheckPlus hcheckMinus hdisjPlusO
          hdisjMinusO boundaryVertexOfCross coverLeft coverRight noCheckerboardDiagonal
          mixedCornerContradiction y j hcenter hdiagO hside1O hside3O
  have singletonCorner (y : GaussianInt) (j : Fin 4) := ContactStarCases.singletonCorner y j
  intro y hy a hya
  obtain ⟨jo, hjo⟩ := incident O y hO hy
  have ha := ContactStarCases.ha y a hya
  have coverAt (i : Fin 4) := ContactStarCases.coverAt Dplus Dminus O coverLeft coverRight
      cornerRescue y jo hjo i
  rcases ha with ⟨i, hai⟩
  rw [hai]
  exact coverAt i

end ApollonianSuperharmonic

end
