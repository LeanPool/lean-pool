/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AffineTriangularComplexChart
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.OppositeRoutedCommonEdgeOutsideCellUnique

-- [TABLET NODE: AffineTriangularNoFourfoldCellOwners]

/-!
# AffineTriangularNoFourfoldCellOwners

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem AffineTriangularNoFourfoldCellOwners {ι : Type}
    (P : PeriodicTileComplex ι) (tileAt : (Int × Int) → ProtoTile)
    (chart : AffineTriangularComplexChart P tileAt)
    (x : GaussianInt) (a0 a1 a2 a3 : ι)
    (h0 : x ∈ (P.tile a0).cells)
    (h1 : x - 1 ∈ (P.tile a1).cells)
    (h2 : x - 1 - ⟨0, 1⟩ ∈ (P.tile a2).cells)
    (h3 : x - ⟨0, 1⟩ ∈ (P.tile a3).cells) :
    a0 = a1 ∨ a0 = a2 ∨ a0 = a3 ∨
      a1 = a2 ∨ a1 = a3 ∨ a2 = a3 := by
-- BODY
  classical
  by_contra h
  push Not at h
  obtain ⟨hne01, hne02, hne03, hne12, hne13, hne23⟩ := h
  have classification := (PeriodicTileIntersectionClassification P).1
  have absent (a b : ι) (hne : a ≠ b) (y : GaussianInt)
      (hy : y ∈ (P.tile b).cells) : y ∉ (P.tile a).cells := by
    intro ha
    exact hne ((PeriodicTileIndexedMultiplicityOne P y).unique ha hy)
  have cell_disjoint (a b : ι) (hne : a ≠ b) :
      Disjoint (P.tile a).cells (P.tile b).cells := by
    apply Finset.disjoint_left.mpr
    intro y ha hb
    exact absent a b hne y hb ha
  have vertical_adj (a b : ι) (hne : a ≠ b) (y : GaussianInt)
      (ha : y ∈ (P.tile a).cells)
      (hb : y - 1 ∈ (P.tile b).cells) : P.plane.adjacent a b := by
    apply (classification a b hne).1.mp
    refine ⟨{y, y + ⟨0, 1⟩}, ?_, ?_⟩
    · exact ⟨y, ha, Or.inr (Or.inl rfl)⟩
    · refine ⟨y - 1, hb, Or.inr (Or.inr (Or.inl ?_))⟩
      simp
  have horizontal_adj (a b : ι) (hne : a ≠ b) (y : GaussianInt)
      (ha : y ∈ (P.tile a).cells)
      (hb : y - ⟨0, 1⟩ ∈ (P.tile b).cells) : P.plane.adjacent a b := by
    apply (classification a b hne).1.mp
    refine ⟨{y, y + 1}, ?_, ?_⟩
    · exact ⟨y, ha, Or.inl rfl⟩
    · refine ⟨y - ⟨0, 1⟩, hb, Or.inr (Or.inr (Or.inr ?_))⟩
      have : y - ⟨0, 1⟩ + 1 + ⟨0, 1⟩ = y + 1 := by abel
      simp only [sub_add_cancel, this]
  have hadj01 := vertical_adj a0 a1 hne01 x h0 h1
  have hadj12 := horizontal_adj a1 a2 hne12 (x - 1) h1 h2
  have hadj32 : P.plane.adjacent a3 a2 := by
    apply vertical_adj a3 a2 hne23.symm (x - ⟨0, 1⟩) h3
    have : x - ⟨0, 1⟩ - 1 = x - 1 - ⟨0, 1⟩ := by abel
    simpa only [this] using h2
  have hadj23 := (P.plane.adjacent_symmetric a3 a2).mp hadj32
  have hadj03 := horizontal_adj a0 a3 hne03 x h0 h3
  have hadj30 := (P.plane.adjacent_symmetric a0 a3).mp hadj03
  -- Every simple four-cycle of triangular-lattice steps has a diagonal chord.
  have chord (p0 p1 p2 p3 : Int × Int)
      (h02 : p0 ≠ p2) (h13 : p1 ≠ p3)
      (h01 : TriangularLatticeAdjacent p0 p1)
      (h12 : TriangularLatticeAdjacent p1 p2)
      (h23 : TriangularLatticeAdjacent p2 p3)
      (h30 : TriangularLatticeAdjacent p3 p0) :
      TriangularLatticeAdjacent p0 p2 ∨ TriangularLatticeAdjacent p1 p3 := by
    let step : Fin 6 → Int × Int := ![(1, 0), (0, 1), (-1, -1),
      (-1, 0), (0, -1), (1, 1)]
    have step_of_adj (u v : Int × Int) (h : TriangularLatticeAdjacent u v) :
        ∃ i, v - u = step i := by
      rcases h with h | h | h | h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
      · exact ⟨4, h⟩
      · exact ⟨5, h⟩
    have certificate : ∀ i j k : Fin 6,
        TriangularLatticeAdjacent (step i + step j + step k) 0 →
        step i + step j ≠ 0 → step j + step k ≠ 0 →
        TriangularLatticeAdjacent 0 (step i + step j) ∨
          TriangularLatticeAdjacent 0 (step j + step k) := by
      unfold TriangularLatticeAdjacent
      decide +kernel
    have translate_adj (u v w : Int × Int) :
        TriangularLatticeAdjacent u v ↔
          TriangularLatticeAdjacent (u - w) (v - w) := by
      unfold TriangularLatticeAdjacent
      have : (v - w) - (u - w) = v - u := by abel
      rw [this]
    obtain ⟨i, hi⟩ := step_of_adj p0 p1 h01
    obtain ⟨j, hj⟩ := step_of_adj p1 p2 h12
    obtain ⟨k, hk⟩ := step_of_adj p2 p3 h23
    have hsum02 : p2 - p0 = step i + step j := by
      rw [← hi, ← hj]
      abel
    have hsum13 : p3 - p1 = step j + step k := by
      rw [← hj, ← hk]
      abel
    have hsum03 : p3 - p0 = step i + step j + step k := by
      rw [← hi, ← hj, ← hk]
      abel
    have hclose : TriangularLatticeAdjacent (step i + step j + step k) 0 := by
      simpa only [sub_self, hsum03] using (translate_adj p3 p0 p0).mp h30
    have hn02 : step i + step j ≠ 0 := by
      rw [← hsum02]
      exact sub_ne_zero.mpr h02.symm
    have hn13 : step j + step k ≠ 0 := by
      rw [← hsum13]
      exact sub_ne_zero.mpr h13.symm
    rcases certificate i j k hclose hn02 hn13 with h | h
    · left
      apply (translate_adj p0 p2 p0).mpr
      simpa only [sub_self, hsum02] using h
    · right
      apply (translate_adj p1 p3 p1).mpr
      simpa only [sub_self, hsum13] using h
  have chart_adj (a b : ι) : P.plane.adjacent a b ↔
      TriangularLatticeAdjacent (chart.vertexEquiv.symm a) (chart.vertexEquiv.symm b) := by
    simpa using chart.adjacent_iff (chart.vertexEquiv.symm a) (chart.vertexEquiv.symm b)
  have hchord : P.plane.adjacent a0 a2 ∨ P.plane.adjacent a1 a3 := by
    have hc := chord (chart.vertexEquiv.symm a0) (chart.vertexEquiv.symm a1)
      (chart.vertexEquiv.symm a2) (chart.vertexEquiv.symm a3)
      (fun he => hne02 (chart.vertexEquiv.symm.injective he))
      (fun he => hne13 (chart.vertexEquiv.symm.injective he))
      ((chart_adj a0 a1).mp hadj01) ((chart_adj a1 a2).mp hadj12)
      ((chart_adj a2 a3).mp hadj23) ((chart_adj a3 a0).mp hadj30)
    exact hc.imp (chart_adj a0 a2).mpr (chart_adj a1 a3).mpr
  have vertex_of_cell (a : ι) (y : GaussianInt) (hy : y ∈ (P.tile a).cells)
      (hx : x = y ∨ x = y + 1 ∨ x = y + ⟨0, 1⟩ ∨
        x = y + 1 + ⟨0, 1⟩) : x ∈ FootprintVertices (P.tile a) := by
    rw [FootprintVertices, ite_eq_left ⟨y, hy⟩]
    exact ⟨y, hy, hx⟩
  have hv0 : x ∈ FootprintVertices (P.tile a0) :=
    vertex_of_cell a0 x h0 (Or.inl rfl)
  have hv1 : x ∈ FootprintVertices (P.tile a1) := by
    apply vertex_of_cell a1 (x - 1) h1
    exact Or.inr (Or.inl (by simp))
  have hv2 : x ∈ FootprintVertices (P.tile a2) := by
    apply vertex_of_cell a2 (x - 1 - ⟨0, 1⟩) h2
    exact Or.inr (Or.inr (Or.inr (by abel)))
  have hv3 : x ∈ FootprintVertices (P.tile a3) := by
    apply vertex_of_cell a3 (x - ⟨0, 1⟩) h3
    exact Or.inr (Or.inr (Or.inl (by simp)))
  have common_edge_at_vertex (a b : ι) (hne : a ≠ b)
      (hadj : P.plane.adjacent a b)
      (ha : x ∈ FootprintVertices (P.tile a))
      (hb : x ∈ FootprintVertices (P.tile b)) :
      ∃ e ∈ FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b), x ∈ e := by
    have hnonempty := (classification a b hne).1.mpr hadj
    have hv := ((classification a b hne).2.1 hnonempty).2
    have hx : x ∈ FootprintVertices (P.tile a) ∩ FootprintVertices (P.tile b) := ⟨ha, hb⟩
    rw [hv] at hx
    exact hx
  rcases hchord with hadj02 | hadj13
  · obtain ⟨e, he, hxe⟩ := common_edge_at_vertex a0 a2 hne02 hadj02 hv0 hv2
    have hE : LatticeVertexIncidentCell x 0 ∈ (P.tile a0).cells := by
      simpa [LatticeVertexIncidentCell] using h0
    have hF : LatticeVertexIncidentCell x (0 + 2) ∈ (P.tile a2).cells := by
      simpa [LatticeVertexIncidentCell] using h2
    have heq := OppositeRoutedCommonEdgeOutsideCellUnique (P.tile a0) (P.tile a2)
      x 0 e (cell_disjoint a0 a2 hne02) hxe he hE hF 1 3
      (by simpa [LatticeVertexIncidentCell] using absent a0 a1 hne01 (x - 1) h1)
      (by simpa [LatticeVertexIncidentCell] using absent a2 a1 hne12.symm (x - 1) h1)
      (by simpa [LatticeVertexIncidentCell] using absent a0 a3 hne03 (x - ⟨0, 1⟩) h3)
      (by simpa [LatticeVertexIncidentCell] using absent a2 a3 hne23 (x - ⟨0, 1⟩) h3)
    have hre := congrArg Zsqrtd.re heq
    simp [LatticeVertexIncidentCell] at hre
  · obtain ⟨e, he, hxe⟩ := common_edge_at_vertex a1 a3 hne13 hadj13 hv1 hv3
    have hE : LatticeVertexIncidentCell x 1 ∈ (P.tile a1).cells := by
      simpa [LatticeVertexIncidentCell] using h1
    have hF : LatticeVertexIncidentCell x (1 + 2) ∈ (P.tile a3).cells := by
      simpa [LatticeVertexIncidentCell] using h3
    have heq := OppositeRoutedCommonEdgeOutsideCellUnique (P.tile a1) (P.tile a3)
      x 1 e (cell_disjoint a1 a3 hne13) hxe he hE hF 0 2
      (by simpa [LatticeVertexIncidentCell] using absent a1 a0 hne01.symm x h0)
      (by simpa [LatticeVertexIncidentCell] using absent a3 a0 hne03.symm x h0)
      (by simpa [LatticeVertexIncidentCell] using absent a1 a2 hne12 (x - 1 - ⟨0, 1⟩) h2)
      (by simpa [LatticeVertexIncidentCell] using absent a3 a2 hne23.symm (x - 1 - ⟨0, 1⟩) h2)
    have hre := congrArg Zsqrtd.re heq
    simp [LatticeVertexIncidentCell] at hre
    omega

end ApollonianSuperharmonic

end
