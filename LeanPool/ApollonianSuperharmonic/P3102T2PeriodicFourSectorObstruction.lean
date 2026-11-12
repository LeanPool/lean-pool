/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3102T2CommonEdgeSectorTransition
public import LeanPool.ApollonianSuperharmonic.PeriodicTileAdjacentContactRegularity
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathPointTrichotomy

-- [TABLET NODE: P3102T2PeriodicFourSectorObstruction]

/-!
# P3102T2PeriodicFourSectorObstruction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3102T2PeriodicFourSectorObstruction
    {ι : Type} (P : PeriodicTileComplex ι)
    (hregular : PeriodicTileAdjacentContactRegularity P)
    (hpartition : ∀ c : LatticeCell, ∃! a : ι, c ∈ (P.tile a).cells)
    (x : GaussianInt) (owner : Fin 4 → ι)
    (howner : ∀ j, LatticeVertexIncidentCell x j ∈ (P.tile (owner j)).cells)
    (hinjective : Function.Injective owner)
    (f g : P.plane.Face)
    (hf : (∃ i, P.plane.faceVertex f i = owner 0) ∧
      (∃ i, P.plane.faceVertex f i = owner 1))
    (hg : (∃ i, P.plane.faceVertex g i = owner 0) ∧
      (∃ i, P.plane.faceVertex g i = owner 1))
    (hpath : SimpleGridPathBetween
      (CommonFootprintEdgeVertices (P.tile (owner 0)) (P.tile (owner 1)))
      (FootprintEdges (P.tile (owner 0)) ∩ FootprintEdges (P.tile (owner 1)))
      (P.rho f) (P.rho g)) : False := by
-- BODY
  classical
  have hdisjoint (a b : ι) (hab : a ≠ b) :
      Disjoint (P.tile a).cells (P.tile b).cells := by
    rw [Finset.disjoint_left]
    intro c ha hb
    exact hab ((hpartition c).unique ha hb)
  have hraw (j : Fin 4) : x ∈ FootprintVertices (P.tile (owner j)) := by
    have hne : (P.tile (owner j)).cells.Nonempty := ⟨_, howner j⟩
    simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq]
    refine ⟨LatticeVertexIncidentCell x j, howner j, ?_⟩
    fin_cases j <;> simp [LatticeVertexIncidentCell, Zsqrtd.ext_iff]
  let edgeAt : Fin 4 → Finset GaussianInt :=
    ![{x, x + ⟨0, 1⟩}, {x - 1, x}, {x - ⟨0, 1⟩, x}, {x, x + 1}]
  have transition (r s : Fin 4) (hrs : r ≠ s) (e : Finset GaussianInt)
      (hxe : x ∈ e)
      (he : e ∈ FootprintEdges (P.tile (owner r)) ∩
        FootprintEdges (P.tile (owner s))) :
      ∃ k : Fin 4, e = edgeAt k ∧
        ((k = r ∧ k + 1 = s) ∨ (k = s ∧ k + 1 = r)) := by
    obtain ⟨k, hek, h | h⟩ := P3102T2CommonEdgeSectorTransition
      _ _ x e (hdisjoint _ _ (hinjective.ne hrs)) hxe he
    · exact ⟨k, hek, Or.inl
        ⟨hinjective ((hpartition _).unique (howner k) h.1),
          hinjective ((hpartition _).unique (howner (k + 1)) h.2)⟩⟩
    · exact ⟨k, hek, Or.inr
        ⟨hinjective ((hpartition _).unique (howner k) h.1),
          hinjective ((hpartition _).unique (howner (k + 1)) h.2)⟩⟩
  have he0 : edgeAt 0 ∈ FootprintEdges (P.tile (owner 0)) ∩
      FootprintEdges (P.tile (owner 1)) := by
    constructor
    · refine ⟨x, howner 0, Or.inr (Or.inl rfl)⟩
    · refine ⟨x - 1, howner 1, Or.inr (Or.inr (Or.inl ?_))⟩
      simp [edgeAt]
  have unique_edge (e : Finset GaussianInt) (hxe : x ∈ e)
      (he : e ∈ FootprintEdges (P.tile (owner 0)) ∩
        FootprintEdges (P.tile (owner 1))) : e = edgeAt 0 := by
    obtain ⟨k, hek, h | h⟩ := transition 0 1 (by decide +kernel) e hxe he
    · simpa [h.1] using hek
    · have hk : k = 1 := h.1
      have hbad := h.2
      simp [hk] at hbad
  have hincident : ∃ e : Finset GaussianInt, x ∈ e ∧
      e ∈ FootprintEdges (P.tile (owner 0)) ∩ FootprintEdges (P.tile (owner 1)) :=
    ⟨edgeAt 0, by simp [edgeAt], he0⟩
  have hendpoint : x = P.rho f ∨ x = P.rho g := by
    rcases SimpleGridPathPointTrichotomy _ _ _ _ x hpath hincident with
      h | h | ⟨e, e', hne, hxe, hxe', he, he'⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact (hne ((unique_edge e hxe he).trans (unique_edge e' hxe' he').symm)).elim
  obtain ⟨F, hF, hxF⟩ : ∃ F : P.plane.Face,
      ((∃ i, P.plane.faceVertex F i = owner 0) ∧
        (∃ i, P.plane.faceVertex F i = owner 1)) ∧ x = P.rho F := by
    rcases hendpoint with h | h
    · exact ⟨f, hf, h⟩
    · exact ⟨g, hg, h⟩
  obtain ⟨i, hi⟩ := hF.1
  obtain ⟨j, hj⟩ := hF.2
  have hij : i ≠ j := by
    intro h
    subst j
    exact (hinjective.ne (by decide +kernel : (0 : Fin 4) ≠ 1)) (hi.symm.trans hj)
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  let t := P.plane.faceVertex F k
  have ht0 : t ≠ owner 0 := by
    intro h
    exact hki (P.plane.face_vertices_distinct F (h.trans hi.symm))
  have ht1 : t ≠ owner 1 := by
    intro h
    exact hkj (P.plane.face_vertices_distinct F (h.trans hj.symm))
  have hxt : x ∈ FootprintVertices (P.tile t) := by
    rw [hxF]
    exact P.rho_common F k
  have htne : (P.tile t).cells.Nonempty :=
    (LatticeTileGridStructure _ (P.tiles_are_disks t)).1.1
  have htincident : ∃ r : Fin 4, LatticeVertexIncidentCell x r ∈ (P.tile t).cells := by
    simp only [FootprintVertices, htne, ite_true, Set.mem_ofPred_eq] at hxt
    obtain ⟨c, hc, h | h | h | h⟩ := hxt
    · exact ⟨0, by simpa [LatticeVertexIncidentCell, h] using hc⟩
    · refine ⟨1, ?_⟩
      simpa [LatticeVertexIncidentCell, h] using hc
    · refine ⟨3, ?_⟩
      simpa [LatticeVertexIncidentCell, h] using hc
    · refine ⟨2, ?_⟩
      simpa [LatticeVertexIncidentCell, h, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc] using hc
  obtain ⟨r, hr⟩ := htincident
  have htr : t = owner r := (hpartition _).unique hr (howner r)
  have hadj0 : P.plane.adjacent (owner 0) t := by
    rw [← hi]
    exact P.plane.face_edges F i k (Ne.symm hki)
  have hadj1 : P.plane.adjacent (owner 1) t := by
    rw [← hj]
    exact P.plane.face_edges F j k (Ne.symm hkj)
  have opposite_not_adjacent (s : Fin 4) (hrs : s ≠ r)
      (hnotconsecutive : ∀ z : Fin 4,
        ¬ ((z = s ∧ z + 1 = r) ∨ (z = r ∧ z + 1 = s))) :
      ¬ P.plane.adjacent (owner s) t := by
    intro hadj
    have hxcommon : x ∈ CommonFootprintEdgeVertices (P.tile (owner s)) (P.tile t) := by
      rw [← hregular.adjacent_raw_eq_edge_vertices _ _ hadj]
      exact ⟨hraw s, hxt⟩
    obtain ⟨e, he, hxe⟩ := hxcommon
    rw [htr] at he
    obtain ⟨z, _, hz⟩ := transition s r hrs e hxe he
    exact hnotconsecutive z hz
  fin_cases r
  · exact ht0 htr
  · exact ht1 htr
  · exact opposite_not_adjacent 0 (by decide +kernel)
      (by intro z; fin_cases z <;> decide +kernel) hadj0
  · exact opposite_not_adjacent 1 (by decide +kernel)
      (by intro z; fin_cases z <;> decide +kernel) hadj1

end ApollonianSuperharmonic

end
