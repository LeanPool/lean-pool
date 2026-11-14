/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ExactTileTiling
public import LeanPool.ApollonianSuperharmonic.FiniteConnectedCellSetNoCheckerboard
public import LeanPool.ApollonianSuperharmonic.FiniteInducedTilePatch
public import LeanPool.ApollonianSuperharmonic.FinitePolyominoDiskCriterion
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.P3350T1GraphCellUnionConnected

-- [TABLET NODE: FinitePatchTopology]

/-!
# FinitePatchTopology

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FinitePatchTopology {ι : Type}
    (G : PlaneTriangulation ι) (tile : ι → ProtoTile)
    (hexact : ExactTileTiling (Set.range tile))
    (hindexed : ∀ x : LatticeCell, ∃! a : ι, x ∈ (tile a).cells)
    (hadjacency : ∀ a b, a ≠ b → G.adjacent a b →
      (FootprintEdges (tile a) ∩ FootprintEdges (tile b)).Nonempty)
    (K : FiniteInducedTilePatch G tile) :
    LatticeTile K.unionTile := by
-- BODY
  have cellConnected : ∀ a, FourNeighborConnected ((tile a).cells : Set LatticeCell) := by
    intro a
    have htile : LatticeTile (tile a) := hexact.1 (tile a) ⟨a, rfl⟩
    exact (LatticeTileGridStructure (tile a) htile).1
  have cellDisjoint : ∀ a b, a ≠ b → Disjoint (tile a).cells (tile b).cells := by
    intro a b hab
    apply Finset.disjoint_left.2
    intro x hx hy
    exact hab ((hindexed x).unique hx hy)
  have insideUnion : {x : LatticeCell | ∃ a ∈ (K.indices : Set ι),
      x ∈ (tile a).cells} = (K.unionTile.cells : Set LatticeCell) := by
    ext x
    exact (K.exact_union x).symm
  have insideConnected : FourNeighborConnected (K.unionTile.cells : Set LatticeCell) := by
    rw [← insideUnion]
    exact P3350T1GraphCellUnionConnected G.adjacent G.adjacent_irreflexive
      tile (K.indices : Set ι) K.nonempty
      (fun a _ => cellConnected a)
      (fun a _ b _ hab => cellDisjoint a b hab)
      (fun a _ b _ hab => hadjacency a b hab)
      K.induced_connected
  have outsideUnion : {x : LatticeCell | ∃ a ∈ (K.indices : Set ι)ᶜ,
      x ∈ (tile a).cells} = (K.unionTile.cells : Set LatticeCell)ᶜ := by
    ext x
    constructor
    · rintro ⟨a, ha, hxa⟩ hx
      obtain ⟨b, hb, hxb⟩ := (K.exact_union x).1 hx
      have hab : a = b := (hindexed x).unique hxa hxb
      exact ha (hab.symm ▸ hb)
    · intro hx
      obtain ⟨a, hxa, _⟩ := hindexed x
      refine ⟨a, ?_, hxa⟩
      intro ha
      exact hx ((K.exact_union x).2 ⟨a, ha, hxa⟩)
  have outsideConnected : FourNeighborConnected ((K.unionTile.cells : Set LatticeCell)ᶜ) := by
    let : Infinite LatticeCell := by
      apply Infinite.of_injective (fun n : Nat => (n : GaussianInt))
      intro a b h
      have hh := congrArg Zsqrtd.re h
      norm_num at hh ⊢
      omega
    have hnonempty : ((K.indices : Set ι)ᶜ).Nonempty := by
      obtain ⟨x, hx⟩ := K.unionTile.cells.exists_notMem
      obtain ⟨a, hxa, _⟩ := hindexed x
      refine ⟨a, ?_⟩
      intro ha
      exact hx ((K.exact_union x).2 ⟨a, ha, hxa⟩)
    rw [← outsideUnion]
    exact P3350T1GraphCellUnionConnected G.adjacent G.adjacent_irreflexive
      tile (K.indices : Set ι)ᶜ hnonempty
      (fun a _ => cellConnected a)
      (fun a _ b _ hab => cellDisjoint a b hab)
      (fun a _ b _ hab => hadjacency a b hab)
      K.complement_connected
  have hchecker := FiniteConnectedCellSetNoCheckerboard
    K.unionTile.cells insideConnected outsideConnected
  exact FinitePolyominoDiskCriterion K.unionTile insideConnected outsideConnected hchecker

end ApollonianSuperharmonic

end
