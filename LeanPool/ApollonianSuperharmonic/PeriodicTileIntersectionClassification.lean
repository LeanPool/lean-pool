/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FinitePatchTopology
public import LeanPool.ApollonianSuperharmonic.LatticeTileDiskUnionInterface
public import LeanPool.ApollonianSuperharmonic.PeriodicTileAdjacentContactRegularity
public import LeanPool.ApollonianSuperharmonic.PeriodicTileContactRoutingRigidity
public import LeanPool.ApollonianSuperharmonic.PeriodicTileMultiplicityOne
public import LeanPool.ApollonianSuperharmonic.P3963T1DeletedPairExteriorConnected
public import LeanPool.ApollonianSuperharmonic.P3963T1EdgeFreeDiskCorners
public import LeanPool.ApollonianSuperharmonic.SimpleGridPath

-- [TABLET NODE: PeriodicTileIntersectionClassification]

/-!
# PeriodicTileIntersectionClassification

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem PeriodicTileIntersectionClassification {ι : Type}
    (P : PeriodicTileComplex ι) :
    (∀ a b : ι, a ≠ b →
      (((FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty ↔
          P.plane.adjacent a b) ∧
        ((FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)).Nonempty →
          SimpleGridPath
              (CommonFootprintEdgeVertices (P.tile a) (P.tile b))
              (FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)) ∧
            FootprintVertices (P.tile a) ∩ FootprintVertices (P.tile b) =
              CommonFootprintEdgeVertices (P.tile a) (P.tile b)) ∧
        (¬ (FootprintEdges (P.tile a) ∩
              FootprintEdges (P.tile b)).Nonempty →
          FootprintVertices (P.tile a) ∩ FootprintVertices (P.tile b) = ∅ ∨
            (FootprintVertices (P.tile a) ∩
              FootprintVertices (P.tile b)).Subsingleton))) ∧
      PeriodicTileAdjacentContactRegularity P := by
-- BODY
  classical
  have hindexed := PeriodicTileIndexedMultiplicityOne P
  have adjacentInterface : ∀ a b, P.plane.adjacent a b →
      SimpleGridPath
          (CommonFootprintEdgeVertices (P.tile a) (P.tile b))
          (FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)) ∧
        FootprintVertices (P.tile a) ∩ FootprintVertices (P.tile b) =
          CommonFootprintEdgeVertices (P.tile a) (P.tile b) := by
    intro a b hab
    have hne : a ≠ b := by
      intro h
      subst b
      exact P.plane.adjacent_irreflexive a hab
    let K : FiniteInducedTilePatch P.plane P.tile := {
      indices := {a, b}
      unionTile := { cells := (P.tile a).cells ∪ (P.tile b).cells, anchor := 0 }
      nonempty := by simp
      tile_injective := by
        intro c hc d hd heq
        obtain ⟨x, hx⟩ := (LatticeTileGridStructure _ (P.tiles_are_disks c)).1.1
        apply (hindexed x).unique hx
        simpa [heq] using hx
      exact_union := by
        intro x
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (hx | hx)
          · exact ⟨a, Or.inl rfl, hx⟩
          · exact ⟨b, Or.inr rfl, hx⟩
        · rintro ⟨c, hc, hx⟩
          rcases hc with rfl | rfl
          · exact Or.inl hx
          · exact Or.inr hx
      induced_connected := by
        intro c hc d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
        rcases hc with hc | hc <;> rcases hd with hd | hd
        all_goals rw [hc, hd]
        · exact ⟨[a], by simp, by simp, by simp,
            List.isChain_iff_forall_rel_of_append_cons_cons.mp
              (List.isChain_singleton a)⟩
        · exact ⟨[a, b], by simp, by simp, by simp,
            List.isChain_iff_forall_rel_of_append_cons_cons.mp
              (List.isChain_pair.mpr hab)⟩
        · exact ⟨[b, a], by simp, by simp, by simp,
            List.isChain_iff_forall_rel_of_append_cons_cons.mp
              (List.isChain_pair.mpr ((P.plane.adjacent_symmetric a b).mp hab))⟩
        · exact ⟨[b], by simp, by simp, by simp,
            List.isChain_iff_forall_rel_of_append_cons_cons.mp
              (List.isChain_singleton b)⟩
      complement_connected := by
        exact P.plane.three_connected {a, b} (by
          have hcard := Finset.card_insert_le a ({b} : Finset ι)
          simp only [Finset.card_singleton] at hcard
          omega) }
    have hK : LatticeTile K.unionTile :=
      FinitePatchTopology P.plane P.tile (PeriodicTileMultiplicityOne P)
        hindexed (fun c d _ h => P.adjacent_has_common_edge c d h) K
    have hdisjoint : Disjoint (P.tile a).cells (P.tile b).cells := by
      apply Finset.disjoint_left.mpr
      intro x hxa hxb
      exact hne ((hindexed x).unique hxa hxb)
    have hinterface := LatticeTileDiskUnionInterface (P.tile a) (P.tile b) K.unionTile
      (P.tiles_are_disks a) (P.tiles_are_disks b) hK hdisjoint
      (fun x => by simp [K]) (P.adjacent_has_common_edge a b hab)
    obtain ⟨x, y, p, hpnodup, hplen, hphead, hplast, hpvertices, hpsteps, hpedges⟩ :=
      hinterface.2.1
    exact ⟨⟨p, hpnodup, hplen, hpvertices, hpsteps, hpedges⟩, hinterface.1⟩
  obtain ⟨_, hadjacency, _⟩ := PeriodicTileContactRoutingRigidity P
  constructor
  · intro a b hab
    refine ⟨hadjacency a b hab, ?_, ?_⟩
    · intro hedge
      exact adjacentInterface a b ((hadjacency a b hab).mp hedge)
    · intro hedge
      right
      have hdisjoint : Disjoint (P.tile a).cells (P.tile b).cells := by
        exact Finset.disjoint_left.mpr
          (fun x hxa hxb => hab ((hindexed x).unique hxa hxb))
      exact P3963T1EdgeFreeDiskCorners (P.tile a) (P.tile b)
        (P.tiles_are_disks a) (P.tiles_are_disks b) hdisjoint hedge
        (P3963T1DeletedPairExteriorConnected P a b)
  · exact ⟨fun a b hab => (adjacentInterface a b hab).2⟩

end ApollonianSuperharmonic

end
