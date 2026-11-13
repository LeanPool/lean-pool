/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.ListEndpointFacts

public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.P5635T1EndpointDiagonalOwnership
public import LeanPool.ApollonianSuperharmonic.AffineTriangularNoFourfoldCellOwners
public import LeanPool.ApollonianSuperharmonic.BandRegularTranslatePeriodicComplex
public import LeanPool.ApollonianSuperharmonic.P4158T1AncestorCells
public import LeanPool.ApollonianSuperharmonic.TileString
public import LeanPool.ApollonianSuperharmonic.P4431T1OwnerTransitionSelector

-- [TABLET NODE: P4366T2LocalSectors]

/-!
# P4366T2LocalSectors

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LocalSectorGeometry

private theorem regular_index :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (base : ProtoTile), ∀ (P : PeriodicTileComplex ↥(TilingLattice
            Ci)), (∀ (u : ↥(TilingLattice Ci)), P.tile u = TileTranslation base (↑u :
            GaussianInt)) → (∀ (W : ProtoTile), (W ∈ RegularTileFamily base (TilingLattice Ci)) →
            (∃ a : TilingLattice Ci, P.tile a = W)) ) := by
  classical
  intro Ci base P htiles W hW
  change ∃ v ∈ TilingLattice Ci, W = TileTranslation base v at hW
  rcases hW with ⟨v, hv, hW⟩
  refine ⟨⟨v, hv⟩, ?_⟩
  calc
    P.tile ⟨v, hv⟩ = TileTranslation base v := htiles ⟨v, hv⟩
    _ = W := hW.symm

private theorem htiles_lattice :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (base : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
            (ProperBandQuadruple q) → ((BandPrototile (q 0) base) → (∀ (P : PeriodicTileComplex
            ↥(TilingLattice Ci)), (∀ (u : ↥(TilingLattice Ci)), P.tile u = TileTranslation base
            (↑u : GaussianInt)) → (∀ (a : TilingLattice Ci), LatticeTile (P.tile a)))) ) := by
  classical
  intro Ci base q hproper hbase' P htiles a
  rw [htiles]
  exact (TileDiskAreaCovariance base (a : GaussianInt)).1.mp
    (BandTileSimultaneousInduction q hproper base hbase').1

private theorem neighbor_injective :
    (by
      classical
      exact
        let neighbor (x : GaussianInt) : Fin 4 → GaussianInt :=
          ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        ∀ (x : GaussianInt),
          ∀ {j : Fin 4}, ∀ {k : Fin 4}, neighbor x j = neighbor x k → j = k
    ) := by
  classical
  intro neighbor x j k h
  fin_cases j <;> fin_cases k <;>
    simp [neighbor, Zsqrtd.ext_iff] at h ⊢ <;> omega



private theorem edge_of_sector_cell :
    (by
      classical
      exact
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        ∀ (R : ProtoTile), ∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈
            R.cells ∨
            LatticeVertexIncidentCell x (j + 1) ∈ R.cells) → (edgeAt x j ∈ FootprintEdges R) ) := by
  classical
  intro edgeAt R x j hc
  fin_cases j
  · rcases hc with h | h
    · simpa [edgeAt] using
        (show {x, x + ⟨0, 1⟩} ∈ FootprintEdges R from
          ⟨x, by simpa [LatticeVertexIncidentCell] using h,
            Or.inr (Or.inl rfl)⟩)
    · simpa [edgeAt] using
        (show {x, x + ⟨0, 1⟩} ∈ FootprintEdges R from
          ⟨x - 1, by simpa [LatticeVertexIncidentCell] using h,
            Or.inr (Or.inr (Or.inl (by simp [sub_eq_add_neg,
              add_comm, add_left_comm])))⟩)
  · rcases hc with h | h
    · simpa [edgeAt] using
        (show {x - 1, x} ∈ FootprintEdges R from
          ⟨x - 1, by simpa [LatticeVertexIncidentCell] using h,
            Or.inl (by simp [sub_eq_add_neg, add_comm,
              add_left_comm])⟩)
    · simpa [edgeAt] using
        (show {x - 1, x} ∈ FootprintEdges R from
          ⟨x - 1 - ⟨0, 1⟩, by simpa [LatticeVertexIncidentCell] using h,
            Or.inr (Or.inr (Or.inr (by simp [sub_eq_add_neg,
              add_comm, add_left_comm, add_assoc])))⟩)
  · rcases hc with h | h
    · simpa [edgeAt] using
        (show {x - ⟨0, 1⟩, x} ∈ FootprintEdges R from
          ⟨x - 1 - ⟨0, 1⟩, by
            simpa [LatticeVertexIncidentCell] using h,
            Or.inr (Or.inr (Or.inl (by simp [sub_eq_add_neg,
              add_comm, add_left_comm, add_assoc])))⟩)
    · simpa [edgeAt] using
        (show {x - ⟨0, 1⟩, x} ∈ FootprintEdges R from
          ⟨x - ⟨0, 1⟩, by
            simpa [LatticeVertexIncidentCell] using h,
            Or.inr (Or.inl (by simp []))⟩)
  · rcases hc with h | h
    · simpa [edgeAt] using
        (show {x, x + 1} ∈ FootprintEdges R from
          ⟨x - ⟨0, 1⟩, by simpa [LatticeVertexIncidentCell] using h,
            Or.inr (Or.inr (Or.inr (by simp [sub_eq_add_neg,
              add_comm, add_left_comm])))⟩)
    · simpa [edgeAt] using
        (show {x, x + 1} ∈ FootprintEdges R from
          ⟨x, by
            simpa [LatticeVertexIncidentCell] using h,
            Or.inl rfl⟩)



private theorem forward_index :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (base : ProtoTile), ∀ (tiles : List ProtoTile), ∀ (hs : List
            PartialOdometer), (∀ T ∈ tiles, T ∈ RegularTileFamily base (TilingLattice Ci)) → (∀
            (P : PeriodicTileComplex ↥(TilingLattice Ci)), (∀ (W : ProtoTile), (W ∈
            RegularTileFamily base (TilingLattice Ci)) → (∃ a : TilingLattice Ci, P.tile a = W))
            → (∀ (U : ProtoTile), ∀ (g : PartialOdometer), ((U, g) ∈ tiles.zip hs) → (∃ a :
            TilingLattice Ci, P.tile a = U))) ) := by
  classical
  intro Ci base tiles hs hfamily P regular_index U g hzip
  apply regular_index
  exact hfamily U (List.of_mem_zip hzip).1

private theorem reverse_index :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (base : ProtoTile), ∀ (reverseTiles : List ProtoTile), ∀
            (reverseHs : List PartialOdometer), ∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)),
            (∀ (W : ProtoTile), (W ∈ RegularTileFamily base (TilingLattice Ci)) → (∃ a :
            TilingLattice Ci, P.tile a = W)) → ((∀ T ∈ reverseTiles, T ∈ RegularTileFamily base
            (TilingLattice Ci)) → (∀ (V : ProtoTile), ∀ (k : PartialOdometer), ((V, k) ∈
            reverseTiles.zip reverseHs) → (∃ a : TilingLattice Ci, P.tile a = V))) ) := by
  classical
  intro Ci base reverseTiles reverseHs P regular_index hfamilyR V k hzip
  apply regular_index
  exact hfamilyR V (List.of_mem_zip hzip).1

private theorem index_eq_of_tile_eq :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)), (∀ (a :
            TilingLattice Ci), LatticeTile (P.tile a)) → (∀ (a : TilingLattice Ci), ∀ (b :
            TilingLattice Ci), (P.tile a = P.tile b) → (a = b)) ) := by
  classical
  intro Ci P htiles_lattice a b h
  obtain ⟨c, hc⟩ := (LatticeTileGridStructure (P.tile a)
    (htiles_lattice a)).1.1
  exact (PeriodicTileIndexedMultiplicityOne P c).unique hc (by simpa [h] using hc)

private theorem owner_mem_iff :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)),
        let owner : GaussianInt → TilingLattice Ci := fun c =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P c)
        (∀ (c : GaussianInt), c ∈ (P.tile (owner c)).cells) → ((∀ (c : GaussianInt), ∀ (a :
            TilingLattice Ci), (c ∈ (P.tile a).cells) → (owner c = a)) → (∀ (c : GaussianInt), ∀
            (a : TilingLattice Ci), c ∈ (P.tile a).cells ↔ owner c = a)) ) := by
  classical
  intro Ci P owner owner_cell owner_unique c a
  constructor
  · exact owner_unique c a
  · intro h
    simpa [h] using owner_cell c

private theorem owner_eq_tile :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)),
        let owner : GaussianInt → TilingLattice Ci := fun c =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P c)
        (∀ (c : GaussianInt), ∀ (a : TilingLattice Ci), (c ∈ (P.tile a).cells) → (owner c = a)) →
            (∀ (c : GaussianInt), ∀ (a : TilingLattice Ci), ∀ (T : ProtoTile), (P.tile a = T) →
            ((c ∈ T.cells) → (owner c = a))) ) := by
  classical
  intro Ci P owner owner_unique c a T hPT hc
  apply owner_unique
  simpa [hPT] using hc

private theorem no_fourfold :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (base : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (P
            : PeriodicTileComplex ↥(TilingLattice Ci)), ∀ [ Nonempty
            (AffineTriangularComplexChart P fun (mn : ℤ × ℤ) => TileTranslation base ((↑mn.1 :
            GaussianInt) * BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) + (↑mn.2 :
            GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))))],
        ∀ (x : GaussianInt), ∀ (a0 : TilingLattice Ci), ∀ (a1 : TilingLattice Ci), ∀ (a2 :
            TilingLattice Ci), ∀ (a3 : TilingLattice Ci), (x ∈ (P.tile a0).cells) → ((x - 1 ∈
            (P.tile a1).cells) → ((x - 1 - ⟨0, 1⟩ ∈ (P.tile a2).cells) → ((x - ⟨0, 1⟩ ∈ (P.tile
            a3).cells) → (a0 = a1 ∨ a0 = a2 ∨ a0 = a3 ∨ a1 = a2 ∨ a1 = a3 ∨ a2 = a3)))) ) := by
  classical
  intro Ci base q P hchart x a0 a1 a2 a3 h0 h1 h2 h3
  let tileAt : Int × Int → ProtoTile := fun mn => TileTranslation base
    ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
      (mn.2 : GaussianInt) * BandVectors.1 (q 2) (q 0))
  let chart : AffineTriangularComplexChart P tileAt := Classical.choice hchart
  exact AffineTriangularNoFourfoldCellOwners P tileAt chart x a0 a1 a2 a3
    h0 h1 h2 h3

private theorem owner_no_fourfold :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)),
        let owner : GaussianInt → TilingLattice Ci := fun c =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P c)
        (∀ (c : GaussianInt), c ∈ (P.tile (owner c)).cells) → ((∀ (x : GaussianInt), ∀ (a0 :
            TilingLattice Ci), ∀ (a1 : TilingLattice Ci), ∀ (a2 : TilingLattice Ci), ∀ (a3 :
            TilingLattice Ci), (x ∈ (P.tile a0).cells) → ((x - 1 ∈ (P.tile a1).cells) → ((x - 1 -
            ⟨0, 1⟩ ∈ (P.tile a2).cells) → ((x - ⟨0, 1⟩ ∈ (P.tile a3).cells) → (a0 = a1 ∨ a0 = a2
            ∨ a0 = a3 ∨ a1 = a2 ∨ a1 = a3 ∨ a2 = a3))))) → (∀ (x : GaussianInt), owner
            (LatticeVertexIncidentCell x 0) = owner (LatticeVertexIncidentCell x 1) ∨ owner
            (LatticeVertexIncidentCell x 0) = owner (LatticeVertexIncidentCell x 2) ∨ owner
            (LatticeVertexIncidentCell x 0) = owner (LatticeVertexIncidentCell x 3) ∨ owner
            (LatticeVertexIncidentCell x 1) = owner (LatticeVertexIncidentCell x 2) ∨ owner
            (LatticeVertexIncidentCell x 1) = owner (LatticeVertexIncidentCell x 3) ∨ owner
            (LatticeVertexIncidentCell x 2) = owner (LatticeVertexIncidentCell x 3))) ) := by
  classical
  intro Ci P owner owner_cell no_fourfold x
  have h := no_fourfold x (owner (LatticeVertexIncidentCell x 0))
    (owner (LatticeVertexIncidentCell x 1))
    (owner (LatticeVertexIncidentCell x 2))
    (owner (LatticeVertexIncidentCell x 3))
    (owner_cell _) (by simpa [LatticeVertexIncidentCell] using owner_cell (x - 1))
    (by simpa [LatticeVertexIncidentCell] using
      owner_cell (x - 1 - ⟨0, 1⟩))
    (by simpa [LatticeVertexIncidentCell] using owner_cell (x - ⟨0, 1⟩))
  simpa [LatticeVertexIncidentCell] using h

private theorem owner_no_checkerboard :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)), (∀ (a :
            TilingLattice Ci), LatticeTile (P.tile a)) → (
        let owner : GaussianInt → TilingLattice Ci := fun c =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P c)
        (∀ (c : GaussianInt), ∀ (a : TilingLattice Ci), c ∈ (P.tile a).cells ↔ owner c = a) → (∀
            (x : GaussianInt), ∀ (a : TilingLattice Ci), ¬ ((owner (LatticeVertexIncidentCell x
            0) = a ∧ owner (LatticeVertexIncidentCell x 2) = a ∧ owner (LatticeVertexIncidentCell
            x 1) ≠ a ∧ owner (LatticeVertexIncidentCell x 3) ≠ a) ∨ (owner
            (LatticeVertexIncidentCell x 1) = a ∧ owner (LatticeVertexIncidentCell x 3) = a ∧
            owner (LatticeVertexIncidentCell x 0) ≠ a ∧ owner (LatticeVertexIncidentCell x 2) ≠
            a)))) ) := by
  classical
  intro Ci P htiles_lattice owner owner_mem_iff x a
  have hcheck := (LatticeTileGridStructure (P.tile a) (htiles_lattice a)).2.1 x
  simpa [LatticeVertexIncidentCell, owner_mem_iff] using hcheck

private theorem cross_ne :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), (Disjoint T0.cells
            T0'.cells) → (∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)), (∀ (a : TilingLattice
            Ci), LatticeTile (P.tile a)) → (∀ (a : TilingLattice Ci), ∀ (b : TilingLattice Ci),
            ((P.tile a).cells ⊆ T0.cells) → (((P.tile b).cells ⊆ T0'.cells) → (a ≠ b)))) ) := by
  classical
  intro Ci T0 T0' hdis P htiles_lattice a b ha hb hab
  subst b
  obtain ⟨c, hc⟩ := (LatticeTileGridStructure (P.tile a)
    (htiles_lattice a)).1.1
  exact (Finset.disjoint_left.mp hdis) (ha hc) (hb hc)

private theorem indexed_edge_witnesses :
    (by
      classical
      exact
        ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (h0
            : PartialOdometer), ∀ (h0' : PartialOdometer), ∀ (tiles : List ProtoTile), ∀
            (reverseTiles : List ProtoTile), ∀ (hs : List PartialOdometer), ∀ (reverseHs : List
            PartialOdometer), (Disjoint T0.cells T0'.cells) → (∀ (path : List GaussianInt), (∀ (a
            : GaussianInt), ∀ (b : GaussianInt), ∀ (l : List GaussianInt), ∀ (r : List
            GaussianInt), path = l ++ a :: b :: r → (∃ (U : ProtoTile) (g : PartialOdometer), U ∈
            (List.drop (1 : ℕ) tiles).dropLast ∧ (U, g) ∈ tiles.zip hs ∧ {a, b} ∈ FootprintEdges
            U ∧ AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0) ∧ ∃ (V : ProtoTile) (k :
            PartialOdometer), V ∈ (List.drop (1 : ℕ) reverseTiles).dropLast ∧ (V, k) ∈
            reverseTiles.zip reverseHs ∧ {a, b} ∈ FootprintEdges V ∧ AncestorOdometer Ci.1.1
            C0.1.1 V T0' k h0') → (∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)), (∀ (a :
            TilingLattice Ci), LatticeTile (P.tile a)) → ((∀ (U : ProtoTile), ∀ (g :
            PartialOdometer), ((U, g) ∈ tiles.zip hs) → (∃ a : TilingLattice Ci, P.tile a = U)) →
            ((∀ (V : ProtoTile), ∀ (k : PartialOdometer), ((V, k) ∈ reverseTiles.zip reverseHs) →
            (∃ a : TilingLattice Ci, P.tile a = V)) → ((∀ (U : ProtoTile), ∀ (T : ProtoTile), ∀
            (g : PartialOdometer), ∀ (h : PartialOdometer), (AncestorOdometer Ci.1.1 C0.1.1 U T g
            h) → (U.cells ⊆ T.cells)) → (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l : List
            GaussianInt), ∀ (r : List GaussianInt), (path = l ++ a :: b :: r) → (∃ U V :
            ProtoTile, ∃ g k : PartialOdometer, ∃ ia ib : TilingLattice Ci, U ∈ (tiles.drop
            1).dropLast ∧ (U, g) ∈ tiles.zip hs ∧ {a, b} ∈ FootprintEdges U ∧ AncestorOdometer
            Ci.1.1 C0.1.1 U T0 g h0 ∧ V ∈ (reverseTiles.drop 1).dropLast ∧ (V, k) ∈
            reverseTiles.zip reverseHs ∧ {a, b} ∈ FootprintEdges V ∧ AncestorOdometer Ci.1.1
            C0.1.1 V T0' k h0' ∧ P.tile ia = U ∧ P.tile ib = V ∧ ia ≠ ib))))))) ) := by
  classical
  intro C0 Ci T0 T0' h0 h0' tiles reverseTiles hs reverseHs hdis path hedges P htiles_lattice
      forward_index reverse_index ancestor_cells a b l r hpathEdge
  rcases hedges a b l r hpathEdge with ⟨hfwd, hrev⟩
  rcases hfwd with ⟨U, g, hUint, hzip, hedgeU, hancU⟩
  rcases hrev with ⟨V, k, hVint, hzip', hedgeV, hancV⟩
  obtain ⟨ia, hia⟩ := forward_index U g hzip
  obtain ⟨ib, hib⟩ := reverse_index V k hzip'
  have hsubU : (P.tile ia).cells ⊆ T0.cells := by
    rw [hia]
    exact ancestor_cells U T0 g h0 hancU
  have hsubV : (P.tile ib).cells ⊆ T0'.cells := by
    rw [hib]
    exact ancestor_cells V T0' k h0' hancV
  have hne : ia ≠ ib := by
    intro heq
    subst ib
    obtain ⟨c, hc⟩ := (LatticeTileGridStructure (P.tile ia)
      (htiles_lattice ia)).1.1
    exact (Finset.disjoint_left.mp hdis) (hsubU hc) (hsubV hc)
  exact ⟨U, V, g, k, ia, ib, hUint, hzip, hedgeU, hancU,
    hVint, hzip', hedgeV, hancV, hia, hib, hne⟩

private theorem indexed_transition :
    (by
      classical
      exact
        ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (h0
            : PartialOdometer), ∀ (h0' : PartialOdometer), ∀ (tiles : List ProtoTile), ∀
            (reverseTiles : List ProtoTile), ∀ (hs : List PartialOdometer), ∀ (reverseHs : List
            PartialOdometer), (Disjoint T0.cells T0'.cells) → (∀ (path : List GaussianInt), ∀ (P
            : PeriodicTileComplex ↥(TilingLattice Ci)), (∀ (U : ProtoTile), ∀ (T : ProtoTile), ∀
            (g : PartialOdometer), ∀ (h : PartialOdometer), (AncestorOdometer Ci.1.1 C0.1.1 U T g
            h) → (U.cells ⊆ T.cells)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l : List
            GaussianInt), ∀ (r : List GaussianInt), (path = l ++ a :: b :: r) → (∃ U V :
            ProtoTile, ∃ g k : PartialOdometer, ∃ ia ib : TilingLattice Ci, U ∈ (tiles.drop
            1).dropLast ∧ (U, g) ∈ tiles.zip hs ∧ {a, b} ∈ FootprintEdges U ∧ AncestorOdometer
            Ci.1.1 C0.1.1 U T0 g h0 ∧ V ∈ (reverseTiles.drop 1).dropLast ∧ (V, k) ∈
            reverseTiles.zip reverseHs ∧ {a, b} ∈ FootprintEdges V ∧ AncestorOdometer Ci.1.1
            C0.1.1 V T0' k h0' ∧ P.tile ia = U ∧ P.tile ib = V ∧ ia ≠ ib)) → (∀ (a :
            GaussianInt), ∀ (b : GaussianInt), ∀ (x : GaussianInt), ∀ (l : List GaussianInt), ∀
            (r : List GaussianInt), (path = l ++ a :: b :: r) → ((x = a ∨ x = b) → (∃ U V :
            ProtoTile, ∃ g k : PartialOdometer, ∃ ia ib : TilingLattice Ci, ∃ j : Fin 4, ({a, b}
            : Finset GaussianInt) = ![{x, x + ⟨0, 1⟩}, {x - 1, x}, {x - ⟨0, 1⟩, x}, {x, x + 1}] j
            ∧ U ∈ (tiles.drop 1).dropLast ∧ (U, g) ∈ tiles.zip hs ∧ {a, b} ∈ FootprintEdges U ∧
            AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0 ∧ V ∈ (reverseTiles.drop 1).dropLast ∧ (V,
            k) ∈ reverseTiles.zip reverseHs ∧ {a, b} ∈ FootprintEdges V ∧ AncestorOdometer Ci.1.1
            C0.1.1 V T0' k h0' ∧ P.tile ia = U ∧ P.tile ib = V ∧ ia ≠ ib ∧
            (LatticeVertexIncidentCell x j ∈ (P.tile ia).cells ∧ LatticeVertexIncidentCell x (j +
            1) ∈ (P.tile ib).cells ∨ LatticeVertexIncidentCell x j ∈ (P.tile ib).cells ∧
            LatticeVertexIncidentCell x (j + 1) ∈ (P.tile ia).cells)))))) ) := by
  classical
  intro C0 Ci T0 T0' h0 h0' tiles reverseTiles hs reverseHs hdis path P ancestor_cells
      indexed_edge_witnesses a b x l r hpathEdge hxedge
  obtain ⟨U, V, g, k, ia, ib, hUint, hzip, hedgeU, hancU,
    hVint, hzip', hedgeV, hancV, hia, hib, hne⟩ :=
    indexed_edge_witnesses a b l r hpathEdge
  have hsubU : U.cells ⊆ T0.cells := ancestor_cells U T0 g h0 hancU
  have hsubV : V.cells ⊆ T0'.cells := ancestor_cells V T0' k h0' hancV
  have hdisUV : Disjoint U.cells V.cells := by
    apply Finset.disjoint_left.mpr
    intro c hcU hcV
    exact (Finset.disjoint_left.mp hdis) (hsubU hcU) (hsubV hcV)
  have hxe : x ∈ ({a, b} : Finset GaussianInt) := by
    rcases hxedge with rfl | rfl <;> simp
  obtain ⟨j, hje, htransition⟩ := P3102T2CommonEdgeSectorTransition
    U V x {a, b} hdisUV hxe ⟨hedgeU, hedgeV⟩
  rcases htransition with htransition | htransition
  · exact ⟨U, V, g, k, ia, ib, j, hje, hUint, hzip, hedgeU, hancU,
      hVint, hzip', hedgeV, hancV, hia, hib, hne,
      Or.inl ⟨by simpa [hia] using htransition.1,
        by simpa [hib] using htransition.2⟩⟩
  · exact ⟨U, V, g, k, ia, ib, j, hje, hUint, hzip, hedgeU, hancU,
      hVint, hzip', hedgeV, hancV, hia, hib, hne,
      Or.inr ⟨by simpa [hib] using htransition.1,
        by simpa [hia] using htransition.2⟩⟩

private theorem first_edge_unique :
    (by
      classical
      exact
        ∀ (p : List GaussianInt), (p.Nodup) → (∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (rest
            : List GaussianInt), (p = x :: y :: rest) → (∀ (e : Finset GaussianInt), (∃ a b :
            GaussianInt, ∃ l r : List GaussianInt,
          p = l ++ a :: b :: r ∧ e = {a, b}) → ((x ∈ e) → (e = {x, y})))) ) := by
  classical
  intro p hpNodup x y rest hpath e he hxe
  rcases he with ⟨a, b, l, r, hdecomp, heq⟩
  have hmem : x ∈ ({a, b} : Finset GaussianInt) := by simpa [heq] using hxe
  have hcases : x = a ∨ x = b := by simpa using hmem
  have hsub : [a, b] <:+: p := by
    refine ⟨l, r, ?_⟩
    simpa [List.cons_append] using hdecomp.symm
  have hne : p ≠ [] := by rw [hpath]; simp
  have hhead? : p.head? = some x := by rw [hpath]; simp
  have hhead : p.head hne = x := by
    simpa [List.head?_eq_some_head hne] using hhead?
  have hheadmem : p.head hne ∈ [a, b] := by
    rcases hcases with hxa | hxb
    · simp [hhead, hxa]
    · simp [hhead, hxb]
  have hprefix : [a, b] <+: p :=
    hpNodup.prefix_of_head_mem_of_infix hsub hheadmem
  rcases hprefix with ⟨tail, htail⟩
  have hab : p = [a, b] ++ tail := htail.symm
  have hform : x :: y :: rest = a :: b :: tail := by
    calc
      x :: y :: rest = p := hpath.symm
      _ = [a, b] ++ tail := hab
      _ = a :: b :: tail := rfl
  have hxa : x = a := by injection hform
  have hyb : y = b := by
    have htailEq : y :: rest = b :: tail := by injection hform
    injection htailEq
  simp [heq, hxa, hyb]

private theorem reverse_edge_decomp :
    (by
      classical
      exact
        ∀ (p : List GaussianInt), ∀ (e : Finset GaussianInt), (∃ a b : GaussianInt, ∃ l r : List
            GaussianInt,
            p = l ++ a :: b :: r ∧ e = {a, b}) → (∃ a b : GaussianInt, ∃ l r : List GaussianInt,
                p.reverse = l ++ a :: b :: r ∧ e = {a, b}) ) := by
  classical
  intro p e he
  rcases he with ⟨a, b, l, r, hdecomp, heq⟩
  refine ⟨b, a, r.reverse, l.reverse, ?_, ?_⟩
  · rw [hdecomp]
    simp [List.reverse_append, List.append_assoc]
  · simpa [Finset.pair_comm] using heq

private theorem last_edge_unique :
    (by
      classical
      exact
        (∀ (p : List GaussianInt), (p.Nodup) → (∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (rest
            : List GaussianInt), (p = x :: y :: rest) → (∀ (e : Finset GaussianInt), (∃ a b :
            GaussianInt, ∃ l r : List GaussianInt, p = l ++ a :: b :: r ∧ e = {a, b}) → ((x ∈ e)
            → (e = {x, y}))))) → ((∀ (p : List GaussianInt), ∀ (e : Finset GaussianInt), (∃ a b :
            GaussianInt, ∃ l r : List GaussianInt, p = l ++ a :: b :: r ∧ e = {a, b}) → (∃ a b :
            GaussianInt, ∃ l r : List GaussianInt, p.reverse = l ++ a :: b :: r ∧ e = {a, b})) →
            (∀ (p : List GaussianInt), (p.Nodup) → (∀ (x : GaussianInt), ∀ (z : GaussianInt), ∀
            (rest : List GaussianInt), (p = rest ++ z :: x :: []) → (∀ (e : Finset GaussianInt),
            (∃ a b : GaussianInt, ∃ l r : List GaussianInt,
            p = l ++ a :: b :: r ∧ e = {a, b}) → ((x ∈ e) → (e = {z, x})))))) ) := by
  classical
  intro first_edge_unique reverse_edge_decomp p hpNodup x z rest hpath e he hxe
  have hrevNodup : p.reverse.Nodup := List.nodup_reverse.mpr hpNodup
  have hrevPath : p.reverse = x :: z :: rest.reverse := by
    rw [hpath]
    simp [List.reverse_append]
  have hrevDecomp := reverse_edge_decomp p e he
  have hresult := first_edge_unique p.reverse hrevNodup x z rest.reverse
    hrevPath e hrevDecomp hxe
  simpa [Finset.pair_comm] using hresult

private abbrev split_mem :=
  @ListEndpointFacts.splitMembership GaussianInt

private theorem hsuf :
    (by
      classical
      exact
        ∀ (path : List GaussianInt), ∀ (x : GaussianInt), ((2 : ℕ) ≤ path.length) → (∀ (suf :
            List GaussianInt), (path = [] ++ x :: suf) → (suf ≠ [])) ) := by
  classical
  intro path x hlength suf hsplit hnil
  subst suf
  rw [hsplit] at hlength
  simp at hlength

private theorem hUVAt563 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)), (∀ (a :
            TilingLattice Ci), ∀ (b : TilingLattice Ci), (P.tile a = P.tile b) → (a = b)) → (∀ (U
            : ProtoTile), ∀ (V : ProtoTile), ∀ (ia : ↥(TilingLattice Ci)), ∀ (ib :
            ↥(TilingLattice Ci)), (P.tile ia = U) → ((P.tile ib = V) → ((ia ≠ ib) → (U ≠ V)))) )
            := by
  classical
  intro Ci P index_eq_of_tile_eq U V ia ib hUidx hVidx hidxne hEq
  exact hidxne (index_eq_of_tile_eq ia ib
    (hUidx.trans (hEq.trans hVidx.symm)))

private theorem hpathLast :
    (by
      classical
      exact
        ∀ (path : List GaussianInt), ∀ (x : GaussianInt), ∀ (pre : List GaussianInt), (path = pre
            ++ [x]) → (∀ (hpre' : pre ≠ []),
        let z := pre.getLast hpre'
        let pre' := pre.dropLast
        (pre' ++ [z] = pre) → (path = pre' ++ z :: x :: [])) ) := by
  classical
  intro path x pre hsplit hpre' z pre' hpreEq
  calc
    path = pre ++ x :: [] := hsplit
    _ = pre' ++ z :: x :: [] := by rw [← hpreEq]; simp [List.append_assoc]

private theorem hleft :
    (by
      classical
      exact
        ∀ (path : List GaussianInt), ∀ (x : GaussianInt), ∀ (pre : List GaussianInt), ∀ (y :
            GaussianInt), ∀ (rest : List GaussianInt), (path = pre ++ x :: y :: rest) → (∀ (hpre'
            : pre ≠ []),
        let z := pre.getLast hpre'
        let pre' := pre.dropLast
        (pre' ++ [z] = pre) → (path = pre' ++ z :: x :: y :: rest)) ) := by
  classical
  intro path x pre y rest hsplit hpre' z pre' hpreEq
  calc
    path = pre ++ x :: y :: rest := hsplit
    _ = pre' ++ z :: x :: y :: rest := by rw [← hpreEq]; simp [List.append_assoc]

private theorem hEdgeNe :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (pre : List GaussianInt), ∀ (y : GaussianInt), ∀ (hpre' : pre ≠ []),
        let z := pre.getLast hpre'
        (z ≠ x) → ((z ≠ y) → (({z, x} : Finset GaussianInt) ≠ {x, y})) ) := by
  classical
  intro x pre y hpre' z hzx hzy heq
  have hzmem : z = x ∨ z = y := by
    have : z ∈ ({x, y} : Finset GaussianInt) := by
      rw [← heq]
      exact Finset.mem_insert.mpr (Or.inl rfl)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  rcases hzmem with hz | hz
  · exact hzx hz
  · exact hzy hz

private theorem hjne :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (pre : List GaussianInt), ∀ (y : GaussianInt), ∀ (hpre' : pre ≠ []),
        let z := pre.getLast hpre'
        ∀ (jL : Fin (4 : ℕ)), (({z, x} : Finset GaussianInt) = ![{x, x + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt)},
            {x - (1 : GaussianInt), x}, {x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), x}, {x,
            x + (1 : GaussianInt)}] jL) → (∀ (jR : Fin (4 : ℕ)), (({x, y} : Finset GaussianInt) =
                ![{x, x + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt)}, {x - (1 : GaussianInt), x}, {x - (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt), x}, {x, x + (1 : GaussianInt)}] jR) → ((z ≠ x) → ((z ≠ y) →
            (jL ≠ jR)))) ) := by
  classical
  intro x pre y hpre' z jL eL jR eR hzx hzy heq
  have hedgeEq : ({z, x} : Finset GaussianInt) = {x, y} := by
    calc
      _ = ![{x, x + ⟨0, 1⟩}, {x - 1, x},
          {x - ⟨0, 1⟩, x}, {x, x + 1}] jL := eL
      _ = ![{x, x + ⟨0, 1⟩}, {x - 1, x},
          {x - ⟨0, 1⟩, x}, {x, x + 1}] jR := by rw [heq]
      _ = {x, y} := eR.symm
  have hzm : z = x ∨ z = y := by
    have : z ∈ ({x, y} : Finset GaussianInt) := by
      rw [← hedgeEq]
      exact Finset.mem_insert.mpr (Or.inl rfl)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  rcases hzm with h | h
  · exact (hzx h).elim
  · exact hzy h

private theorem hidxX :
    (by
      classical
      exact
        ∀ (path : List GaussianInt), ∀ (x : GaussianInt), ∀ (pre : List GaussianInt), ∀ (y :
            GaussianInt), ∀ (rest : List GaussianInt), ∀ (hpre' : pre ≠ []),
        let z := pre.getLast hpre'
        let pre' := pre.dropLast
        (path = pre' ++ z :: x :: y :: rest) → (((pre' ++ z :: x :: y :: rest).Nodup) →
            (path.idxOf x = pre'.length + 1)) ) := by
  classical
  intro path x pre y rest hpre' z pre' hleft hnodupPath
  have hndSplit :
      ((pre' ++ [z]) ++ (x :: y :: rest)).Nodup := by
    simpa [List.append_assoc] using hnodupPath
  have hdisSplit := (List.nodup_append.mp hndSplit).2.2
  have hxnot : x ∉ pre' ++ [z] := by
    intro hxmem
    exact hdisSplit x hxmem x (List.mem_cons_self ..) rfl
  calc
    path.idxOf x =
        ((pre' ++ [z]) ++ (x :: y :: rest)).idxOf x := by
      rw [hleft]
      simp [List.append_assoc]
    _ = (pre' ++ [z]).length + (x :: y :: rest).idxOf x :=
      List.idxOf_append_of_notMem hxnot
    _ = pre'.length + 1 := by simp

private theorem hidxY :
    (by
      classical
      exact
        ∀ (path : List GaussianInt), ∀ (x : GaussianInt), ∀ (pre : List GaussianInt), ∀ (y :
            GaussianInt), ∀ (rest : List GaussianInt), ∀ (hpre' : pre ≠ []),
        let z := pre.getLast hpre'
        let pre' := pre.dropLast
        (path = pre' ++ z :: x :: y :: rest) → (((pre' ++ z :: x :: y :: rest).Nodup) →
            (path.idxOf y = pre'.length + 2)) ) := by
  classical
  intro path x pre y rest hpre' z pre' hleft hnodupPath
  have hndSplit :
      ((pre' ++ [z, x]) ++ (y :: rest)).Nodup := by
    simpa [List.append_assoc] using hnodupPath
  have hdisSplit := (List.nodup_append.mp hndSplit).2.2
  have hynot : y ∉ pre' ++ [z, x] := by
    intro hymem
    exact hdisSplit y hymem y (List.mem_cons_self ..) rfl
  calc
    path.idxOf y =
        ((pre' ++ [z, x]) ++ (y :: rest)).idxOf y := by
      rw [hleft]
      simp [List.append_assoc]
    _ = (pre' ++ [z, x]).length + (y :: rest).idxOf y :=
      List.idxOf_append_of_notMem hynot
    _ = pre'.length + 2 := by simp

private theorem hidxZ :
    (by
      classical
      exact
        ∀ (path : List GaussianInt), ∀ (x : GaussianInt), ∀ (pre : List GaussianInt), ∀ (y :
            GaussianInt), ∀ (rest : List GaussianInt), ∀ (hpre' : pre ≠ []),
        let z := pre.getLast hpre'
        let pre' := pre.dropLast
        (path = pre' ++ z :: x :: y :: rest) → (((pre' ++ z :: x :: y :: rest).Nodup) →
            (path.idxOf z = pre'.length)) ) := by
  classical
  intro path x pre y rest hpre' z pre' hleft hnodupPath
  have hznot : z ∉ pre' := by
    have hndSplit : (pre' ++ z :: x :: y :: rest).Nodup := by
      simpa [List.append_assoc] using hnodupPath
    have hdisSplit := (List.nodup_append.mp
      (by simpa [List.cons_append, List.append_assoc] using hndSplit)).2.2
    intro hzmem
    exact hdisSplit z hzmem z (List.mem_cons_self ..) rfl
  calc
    path.idxOf z = (pre' ++ z :: x :: y :: rest).idxOf z := by
      rw [hleft]
    _ = pre'.length + (z :: x :: y :: rest).idxOf z :=
      List.idxOf_append_of_notMem hznot
    _ = pre'.length := by simp

private theorem internal_edge_unique :
    (by
      classical
      exact
        ∀ (path : List GaussianInt),
          ∀ (x : GaussianInt),
            path.Nodup →
              ∀ (pre : List GaussianInt),
                ∀ (y : GaussianInt),
                  ∀ (hpre' : pre ≠ []),
                    let z := pre.getLast hpre'
                    let pre' := pre.dropLast
                    path.idxOf x = pre'.length + 1 →
                      path.idxOf y = pre'.length + 2 →
                        path.idxOf z = pre'.length →
                          ∀ (e : Finset GaussianInt),
                            (∃ a b l r, path = l ++ a :: b :: r ∧ e = { a, b }) →
                              x ∈ e → e = { z, x } ∨ e = { x, y }
    ) := by
  classical
  intro path x hnodup pre y hpre' z pre' hidxX hidxY hidxZ e he hxe
  rcases he with ⟨a, b, l, r, hdecomp, heq⟩
  have hcases : x = a ∨ x = b := by
    have : x ∈ ({a, b} : Finset GaussianInt) := by
      simpa [heq] using hxe
    simpa using this
  have hndAB : (l ++ a :: b :: r).Nodup := by
    rw [← hdecomp]
    exact hnodup
  have hndA : (l ++ (a :: b :: r)).Nodup := by
    simpa [List.append_assoc] using hndAB
  have haNot : a ∉ l := by
    have hdis := (List.nodup_append.mp hndA).2.2
    intro hamem
    exact hdis a hamem a (List.mem_cons_self ..) rfl
  have hndB : ((l ++ [a]) ++ (b :: r)).Nodup := by
    simpa [List.append_assoc] using hndAB
  have hbNot : b ∉ l ++ [a] := by
    have hdis := (List.nodup_append.mp hndB).2.2
    intro hbmem
    exact hdis b hbmem b (List.mem_cons_self ..) rfl
  have hidxA : path.idxOf a = l.length := by
    calc
      path.idxOf a = (l ++ a :: b :: r).idxOf a := by rw [hdecomp]
      _ = l.length + (a :: b :: r).idxOf a :=
        List.idxOf_append_of_notMem haNot
      _ = l.length := by simp
  have hidxB : path.idxOf b = l.length + 1 := by
    calc
      path.idxOf b = ((l ++ [a]) ++ b :: r).idxOf b := by
        rw [hdecomp]
        simp [List.append_assoc]
      _ = (l ++ [a]).length + (b :: r).idxOf b :=
        List.idxOf_append_of_notMem hbNot
      _ = l.length + 1 := by simp
  rcases hcases with hxa | hxb
  · subst a
    have hlen : l.length = pre'.length + 1 := by
      rw [← hidxA, hidxX]
    have hby : path.idxOf b = path.idxOf y := by
      rw [hidxB, hlen, hidxY]
    have hbPath : b ∈ path := by rw [hdecomp]; simp
    have hby' : b = y := (List.idxOf_inj (l := path)
      (hx := hbPath)).1 hby
    simp [heq, hby']
  · subst b
    have hlen : l.length + 1 = pre'.length + 1 := by
      rw [← hidxB, hidxX]
    have hlen' : l.length = pre'.length := by omega
    have hza : path.idxOf a = path.idxOf z := by
      rw [hidxA, hlen', hidxZ]
    have hza' : a = z := (List.idxOf_inj (l := path)
      (hx := by rw [hdecomp]; simp)).1 hza
    simp [heq, hza']

private theorem outer_side_class :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0.cells) →
            (outerLabel x j = 0)) → ((∀ (x : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell x j ∈ T0'.cells) → (outerLabel x j = 1)) → (∀ (x :
            GaussianInt), (∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈ T0.cells ∨
            LatticeVertexIncidentCell x j ∈ T0'.cells) → (∀ (j : Fin 4), (outerLabel x j = 0 ∧
            LatticeVertexIncidentCell x j ∈ T0.cells) ∨ (outerLabel x j = 1 ∧
            LatticeVertexIncidentCell x j ∈ T0'.cells)))) ) := by
  classical
  intro T0 T0' outerLabel label_T0 label_T0' x hsectorOuter j
  rcases hsectorOuter j with h0 | h1
  · exact Or.inl ⟨label_T0 x j h0, h0⟩
  · exact Or.inr ⟨label_T0' x j h1, h1⟩

private theorem hLaligned :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (P : PeriodicTileComplex
            ↥(TilingLattice Ci)),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0.cells) →
            (outerLabel x j = 0)) → ((∀ (x : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell x j ∈ T0'.cells) → (outerLabel x j = 1)) → (
        let owner : GaussianInt → TilingLattice Ci := fun c =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P c)
        (∀ (c : GaussianInt), ∀ (a : TilingLattice Ci), (c ∈ (P.tile a).cells) → (owner c = a)) →
            (∀ (x : GaussianInt), ∀ (UL : ProtoTile), ∀ (VL : ProtoTile), ∀ (iaL :
            ↥(TilingLattice Ci)), ∀ (ibL : ↥(TilingLattice Ci)), ∀ (jL : Fin (4 : ℕ)), (P.tile
            iaL = UL) → ((P.tile ibL = VL) → ((LatticeVertexIncidentCell x jL ∈ (P.tile
            iaL).cells ∧ LatticeVertexIncidentCell x (jL + (1 : Fin (4 : ℕ))) ∈ (P.tile
            ibL).cells ∨ LatticeVertexIncidentCell x jL ∈ (P.tile ibL).cells ∧
            LatticeVertexIncidentCell x (jL + (1 : Fin (4 : ℕ))) ∈ (P.tile iaL).cells) →
            ((UL.cells ⊆ T0.cells) → ((VL.cells ⊆ T0'.cells) → (((outerLabel x jL = 0 ∧ owner
            (LatticeVertexIncidentCell x jL) = iaL) ∧ (outerLabel x (jL + 1) = 1 ∧ owner
            (LatticeVertexIncidentCell x (jL + 1)) = ibL)) ∨ ((outerLabel x jL = 1 ∧ owner
            (LatticeVertexIncidentCell x jL) = ibL) ∧ (outerLabel x (jL + 1) = 0 ∧ owner
            (LatticeVertexIncidentCell x (jL + 1)) = iaL)))))))))) ) := by
  classical
  intro Ci T0 T0' P outerLabel label_T0 label_T0' owner owner_unique x UL VL iaL ibL jL hULidx
      hVLidx hsectorL hULsub hVLsub
  rcases hsectorL with h | h
  · left
    constructor
    · exact ⟨label_T0 x jL (hULsub (by simpa [hULidx] using h.1)),
        owner_unique _ iaL (by simpa [hULidx] using h.1)⟩
    · exact ⟨label_T0' x (jL + 1) (hVLsub (by simpa [hVLidx] using h.2)),
        owner_unique _ ibL (by simpa [hVLidx] using h.2)⟩
  · right
    constructor
    · exact ⟨label_T0' x jL (hVLsub (by simpa [hVLidx] using h.1)),
        owner_unique _ ibL (by simpa [hVLidx] using h.1)⟩
    · exact ⟨label_T0 x (jL + 1) (hULsub (by simpa [hULidx] using h.2)),
        owner_unique _ iaL (by simpa [hULidx] using h.2)⟩

private abbrev hRaligned :=
  ApollonianSuperharmonic.LocalSectorGeometry.hLaligned

private theorem transition_is_path_edge :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (path : List GaussianInt),
        let neighbor (x : GaussianInt) : Fin 4 → GaussianInt :=
          ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (x : GaussianInt), ∀ (j : Fin 4), x ∈ edgeAt x j ∧ neighbor x j ∈ edgeAt x j) → ((∀ (x
            : GaussianInt), ∀ {j : Fin 4}, ∀ {k : Fin 4}, (edgeAt x j = edgeAt x k) → (j = k)) →
            ((∀ (R : ProtoTile), ∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x
            j ∈ R.cells ∨ LatticeVertexIncidentCell x (j + 1) ∈ R.cells) → (edgeAt x j ∈
            FootprintEdges R)) → (
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        ∀ (x : GaussianInt), (∀ (e : Finset GaussianInt), e ∈ FootprintEdges T0 ∩ FootprintEdges
            T0' ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l : List GaussianInt) (r : List
            GaussianInt), path = l ++ a :: b :: r ∧ e = {a, b}) → (∀ (pre : List GaussianInt), ∀
            (y : GaussianInt), ∀ (hpre' : pre ≠ []),
        let z := pre.getLast hpre'
        ∀ (jL : Fin (4 : ℕ)), (({z, x} : Finset GaussianInt) = ![{x, x + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt)},
            {x - (1 : GaussianInt), x}, {x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt), x}, {x,
            x + (1 : GaussianInt)}] jL) → (∀ (jR : Fin (4 : ℕ)), (({x, y} : Finset GaussianInt) =
                ![{x, x + (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt)}, {x - (1 : GaussianInt), x}, {x - (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt), x}, {x, x + (1 : GaussianInt)}] jR) → ((∀ (e : Finset
            GaussianInt), (∃ a b l r, path = l ++ a :: b :: r ∧ e = {a, b}) → ((x ∈ e) → (e = {z,
            x} ∨ e = {x, y}))) → ((∀ (j : Fin 4), (outerLabel x j = 0 ∧ LatticeVertexIncidentCell
            x j ∈ T0.cells) ∨ (outerLabel x j = 1 ∧ LatticeVertexIncidentCell x j ∈ T0'.cells)) →
            (∀ (j : Fin 4), (outerLabel x j ≠ outerLabel x (j + 1)) → (j = jL ∨ j = jR))))))))) )
            := by
  classical
  intro T0 T0' path neighbor edgeAt edgeAt_mem edgeAt_injective edge_of_sector_cell outerLabel x
      hedgesPath pre y hpre' z jL eL jR eR internal_edge_unique outer_side_class j hchange
  rcases outer_side_class j with h0 | h1 <;>
    rcases outer_side_class (j + 1) with h0' | h1'
  · exact False.elim (hchange (h0.1.trans h0'.1.symm))
  · have he0 : edgeAt x j ∈ FootprintEdges T0 :=
      edge_of_sector_cell T0 x j (Or.inl h0.2)
    have he1 : edgeAt x j ∈ FootprintEdges T0' :=
      edge_of_sector_cell T0' x j (Or.inr h1'.2)
    have hpathEdge := (hedgesPath (edgeAt x j)).mp ⟨he0, he1⟩
    rcases internal_edge_unique (edgeAt x j) hpathEdge
        (edgeAt_mem x j).1 with hleft | hright
    · left
      apply edgeAt_injective x
      calc
        edgeAt x j = {z, x} := hleft
        _ = edgeAt x jL := eL
    · right
      apply edgeAt_injective x
      calc
        edgeAt x j = {x, y} := hright
        _ = edgeAt x jR := eR
  · have he0 : edgeAt x j ∈ FootprintEdges T0' :=
      edge_of_sector_cell T0' x j (Or.inl h1.2)
    have he1 : edgeAt x j ∈ FootprintEdges T0 :=
      edge_of_sector_cell T0 x j (Or.inr h0'.2)
    have hpathEdge := (hedgesPath (edgeAt x j)).mp ⟨he1, he0⟩
    rcases internal_edge_unique (edgeAt x j) hpathEdge
        (edgeAt_mem x j).1 with hleft | hright
    · left
      apply edgeAt_injective x
      calc
        edgeAt x j = {z, x} := hleft
        _ = edgeAt x jL := eL
    · right
      apply edgeAt_injective x
      calc
        edgeAt x j = {x, y} := hright
        _ = edgeAt x jR := eR
  · exact False.elim (hchange (h1.1.trans h1'.1.symm))

private theorem side_mem_zero :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0.cells) →
            (outerLabel x j = 0)) → (∀ (x : GaussianInt),
        let sectorSide : Fin 4 → Bool := fun j => decide (outerLabel x j = 1)
        ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0.cells) → (sectorSide j = false)) ) := by
  classical
  intro T0 T0' outerLabel label_T0 x sectorSide j hc
  simp [sectorSide, label_T0 x j hc]

private theorem side_mem_one :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0'.cells) →
            (outerLabel x j = 1)) → (∀ (x : GaussianInt),
        let sectorSide : Fin 4 → Bool := fun j => decide (outerLabel x j = 1)
        ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0'.cells) → (sectorSide j = true)) ) := by
  classical
  intro T0 T0' outerLabel label_T0' x sectorSide j hc
  simp [sectorSide, label_T0' x j hc]

private theorem sector_in_tile :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)),
        let owner : GaussianInt → TilingLattice Ci := fun c =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P c)
        (∀ (c : GaussianInt), ∀ (a : TilingLattice Ci), c ∈ (P.tile a).cells ↔ owner c = a) → (∀
            (x : GaussianInt),
        let sectorOwner : Fin 4 → TilingLattice Ci := fun j =>
          owner (LatticeVertexIncidentCell x j)
        ∀ (j : Fin 4), ∀ (a : TilingLattice Ci), (sectorOwner j = a) → (LatticeVertexIncidentCell
            x j ∈ (P.tile a).cells)) ) := by
  classical
  intro Ci P owner owner_mem_iff x sectorOwner j a howner
  exact (owner_mem_iff (LatticeVertexIncidentCell x j) a).2 howner

private theorem side_same_T0 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (P : PeriodicTileComplex
            ↥(TilingLattice Ci)),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        let owner : GaussianInt → TilingLattice Ci := fun c =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P c)
        ∀ (x : GaussianInt),
        let sectorOwner : Fin 4 → TilingLattice Ci := fun j =>
          owner (LatticeVertexIncidentCell x j)
        let sectorSide : Fin 4 → Bool := fun j => decide (outerLabel x j = 1)
        (∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0.cells) → (sectorSide j = false)) →
            ((∀ (j : Fin 4), ∀ (a : TilingLattice Ci), (sectorOwner j = a) →
            (LatticeVertexIncidentCell x j ∈ (P.tile a).cells)) → (∀ (i : Fin 4), ∀ (j : Fin 4),
            ∀ (a : TilingLattice Ci), ((P.tile a).cells ⊆ T0.cells) → ((sectorOwner i = a) →
            ((sectorOwner j = a) → (sectorSide i = sectorSide j))))) ) := by
  classical
  intro Ci T0 T0' P outerLabel owner x sectorOwner sectorSide side_mem_zero sector_in_tile i j a
      hsub hi hj
  rw [side_mem_zero i (hsub (sector_in_tile i a hi)),
    side_mem_zero j (hsub (sector_in_tile j a hj))]

private theorem side_same_T0' :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (P : PeriodicTileComplex
            ↥(TilingLattice Ci)),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        let owner : GaussianInt → TilingLattice Ci := fun c =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P c)
        ∀ (x : GaussianInt),
        let sectorOwner : Fin 4 → TilingLattice Ci := fun j =>
          owner (LatticeVertexIncidentCell x j)
        let sectorSide : Fin 4 → Bool := fun j => decide (outerLabel x j = 1)
        (∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0'.cells) → (sectorSide j = true)) →
            ((∀ (j : Fin 4), ∀ (a : TilingLattice Ci), (sectorOwner j = a) →
            (LatticeVertexIncidentCell x j ∈ (P.tile a).cells)) → (∀ (i : Fin 4), ∀ (j : Fin 4),
            ∀ (a : TilingLattice Ci), ((P.tile a).cells ⊆ T0'.cells) → ((sectorOwner i = a) →
            ((sectorOwner j = a) → (sectorSide i = sectorSide j))))) ) := by
  classical
  intro Ci T0 T0' P outerLabel owner x sectorOwner sectorSide side_mem_one sector_in_tile i j a
      hsub hi hj
  rw [side_mem_one i (hsub (sector_in_tile i a hi)),
    side_mem_one j (hsub (sector_in_tile j a hj))]

private theorem side_consistent_left :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (P : PeriodicTileComplex
            ↥(TilingLattice Ci)),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        let owner : GaussianInt → TilingLattice Ci := fun c =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P c)
        ∀ (x : GaussianInt), ∀ (UL : ProtoTile), ∀ (VL : ProtoTile), ∀ (iaL : ↥(TilingLattice
            Ci)), ∀ (ibL : ↥(TilingLattice Ci)), ∀ (jL : Fin (4 : ℕ)), (P.tile iaL = UL) →
            ((P.tile ibL = VL) → (∀ (UR : ProtoTile), ∀ (VR : ProtoTile), ∀ (iaR :
            ↥(TilingLattice Ci)), ∀ (ibR : ↥(TilingLattice Ci)), ∀ (jR : Fin (4 : ℕ)), (P.tile
            iaR = UR) → ((P.tile ibR = VR) → ((UL.cells ⊆ T0.cells) → ((VL.cells ⊆ T0'.cells) →
            ((UR.cells ⊆ T0.cells) → ((VR.cells ⊆ T0'.cells) → ((((outerLabel x jL = 0 ∧ owner
            (LatticeVertexIncidentCell x jL) = iaL) ∧ (outerLabel x (jL + 1) = 1 ∧ owner
            (LatticeVertexIncidentCell x (jL + 1)) = ibL)) ∨ ((outerLabel x jL = 1 ∧ owner
            (LatticeVertexIncidentCell x jL) = ibL) ∧ (outerLabel x (jL + 1) = 0 ∧ owner
            (LatticeVertexIncidentCell x (jL + 1)) = iaL))) → ((((outerLabel x jR = 0 ∧ owner
            (LatticeVertexIncidentCell x jR) = iaR) ∧ (outerLabel x (jR + 1) = 1 ∧ owner
            (LatticeVertexIncidentCell x (jR + 1)) = ibR)) ∨ ((outerLabel x jR = 1 ∧ owner
            (LatticeVertexIncidentCell x jR) = ibR) ∧ (outerLabel x (jR + 1) = 0 ∧ owner
            (LatticeVertexIncidentCell x (jR + 1)) = iaR))) → ((∀ (j : Fin 4), (outerLabel x j ≠
            outerLabel x (j + 1)) → (j = jL ∨ j = jR)) → (
        let sectorOwner : Fin 4 → TilingLattice Ci := fun j =>
          owner (LatticeVertexIncidentCell x j)
        let sectorSide : Fin 4 → Bool := fun j => decide (outerLabel x j = 1)
        (∀ (i : Fin 4), ∀ (j : Fin 4), ∀ (a : TilingLattice Ci), ((P.tile a).cells ⊆ T0.cells) →
            ((sectorOwner i = a) → ((sectorOwner j = a) → (sectorSide i = sectorSide j)))) → ((∀
            (i : Fin 4), ∀ (j : Fin 4), ∀ (a : TilingLattice Ci), ((P.tile a).cells ⊆ T0'.cells)
            → ((sectorOwner i = a) → ((sectorOwner j = a) → (sectorSide i = sectorSide j)))) → (∀
            i, ∀ k, sectorSide i ≠ sectorSide (i + 1) → sectorOwner k = sectorOwner i →
            sectorSide k = sectorSide i))))))))))))) ) := by
  classical
  intro Ci T0 T0' P outerLabel owner x UL VL iaL ibL jL hULidx hVLidx UR VR iaR ibR jR hURidx
      hVRidx hULsub hVLsub hURsub hVRsub hLaligned hRaligned transition_is_path_edge sectorOwner
      sectorSide side_same_T0 side_same_T0' i k hchange hsame
  have hchange' : outerLabel x i ≠ outerLabel x (i + 1) := by
    intro heq
    exact hchange (by simp only [sectorSide, heq])
  rcases transition_is_path_edge i hchange' with hi | hi <;> subst i
  · rcases hLaligned with h | h
    · exact (side_same_T0 jL k iaL
        (by simpa only [hULidx] using hULsub) h.1.2
        (hsame.trans h.1.2)).symm
    · exact (side_same_T0' jL k ibL
        (by simpa only [hVLidx] using hVLsub) h.1.2
        (hsame.trans h.1.2)).symm
  · rcases hRaligned with h | h
    · exact (side_same_T0 jR k iaR
        (by simpa only [hURidx] using hURsub) h.1.2
        (hsame.trans h.1.2)).symm
    · exact (side_same_T0' jR k ibR
        (by simpa only [hVRidx] using hVRsub) h.1.2
        (hsame.trans h.1.2)).symm

private theorem side_consistent_right :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (P : PeriodicTileComplex
            ↥(TilingLattice Ci)),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        let owner : GaussianInt → TilingLattice Ci := fun c =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P c)
        ∀ (x : GaussianInt), ∀ (UL : ProtoTile), ∀ (VL : ProtoTile), ∀ (iaL : ↥(TilingLattice
            Ci)), ∀ (ibL : ↥(TilingLattice Ci)), ∀ (jL : Fin (4 : ℕ)), (P.tile iaL = UL) →
            ((P.tile ibL = VL) → (∀ (UR : ProtoTile), ∀ (VR : ProtoTile), ∀ (iaR :
            ↥(TilingLattice Ci)), ∀ (ibR : ↥(TilingLattice Ci)), ∀ (jR : Fin (4 : ℕ)), (P.tile
            iaR = UR) → ((P.tile ibR = VR) → ((UL.cells ⊆ T0.cells) → ((VL.cells ⊆ T0'.cells) →
            ((UR.cells ⊆ T0.cells) → ((VR.cells ⊆ T0'.cells) → ((((outerLabel x jL = 0 ∧ owner
            (LatticeVertexIncidentCell x jL) = iaL) ∧ (outerLabel x (jL + 1) = 1 ∧ owner
            (LatticeVertexIncidentCell x (jL + 1)) = ibL)) ∨ ((outerLabel x jL = 1 ∧ owner
            (LatticeVertexIncidentCell x jL) = ibL) ∧ (outerLabel x (jL + 1) = 0 ∧ owner
            (LatticeVertexIncidentCell x (jL + 1)) = iaL))) → ((((outerLabel x jR = 0 ∧ owner
            (LatticeVertexIncidentCell x jR) = iaR) ∧ (outerLabel x (jR + 1) = 1 ∧ owner
            (LatticeVertexIncidentCell x (jR + 1)) = ibR)) ∨ ((outerLabel x jR = 1 ∧ owner
            (LatticeVertexIncidentCell x jR) = ibR) ∧ (outerLabel x (jR + 1) = 0 ∧ owner
            (LatticeVertexIncidentCell x (jR + 1)) = iaR))) → ((∀ (j : Fin 4), (outerLabel x j ≠
            outerLabel x (j + 1)) → (j = jL ∨ j = jR)) → (
        let sectorOwner : Fin 4 → TilingLattice Ci := fun j =>
          owner (LatticeVertexIncidentCell x j)
        let sectorSide : Fin 4 → Bool := fun j => decide (outerLabel x j = 1)
        (∀ (i : Fin 4), ∀ (j : Fin 4), ∀ (a : TilingLattice Ci), ((P.tile a).cells ⊆ T0.cells) →
            ((sectorOwner i = a) → ((sectorOwner j = a) → (sectorSide i = sectorSide j)))) → ((∀
            (i : Fin 4), ∀ (j : Fin 4), ∀ (a : TilingLattice Ci), ((P.tile a).cells ⊆ T0'.cells)
            → ((sectorOwner i = a) → ((sectorOwner j = a) → (sectorSide i = sectorSide j)))) → (∀
            i, ∀ k, sectorSide i ≠ sectorSide (i + 1) → sectorOwner k = sectorOwner (i + 1) →
            sectorSide k = sectorSide (i + 1)))))))))))))) ) := by
  classical
  intro Ci T0 T0' P outerLabel owner x UL VL iaL ibL jL hULidx hVLidx UR VR iaR ibR jR hURidx
      hVRidx hULsub hVLsub hURsub hVRsub hLaligned hRaligned transition_is_path_edge sectorOwner
      sectorSide side_same_T0 side_same_T0' i k hchange hsame
  have hchange' : outerLabel x i ≠ outerLabel x (i + 1) := by
    intro heq
    exact hchange (by simp only [sectorSide, heq])
  rcases transition_is_path_edge i hchange' with hi | hi <;> subst i
  · rcases hLaligned with h | h
    · exact (side_same_T0' (jL + 1) k ibL
        (by simpa only [hVLidx] using hVLsub) h.2.2
        (hsame.trans h.2.2)).symm
    · exact (side_same_T0 (jL + 1) k iaL
        (by simpa only [hULidx] using hULsub) h.2.2
        (hsame.trans h.2.2)).symm
  · rcases hRaligned with h | h
    · exact (side_same_T0' (jR + 1) k ibR
        (by simpa only [hVRidx] using hVRsub) h.2.2
        (hsame.trans h.2.2)).symm
    · exact (side_same_T0 (jR + 1) k iaR
        (by simpa only [hURidx] using hURsub) h.2.2
        (hsame.trans h.2.2)).symm

private theorem hownerOpp :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        ∀ (x : GaussianInt), (∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈ T0.cells ∧
            LatticeVertexIncidentCell x (j + (2 : Fin (4 : ℕ))) ∈ T0'.cells) → (
        let sectorSide : Fin 4 → Bool := fun j => decide (outerLabel x j = 1)
        (∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0.cells) → (sectorSide j = false)) →
            ((∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0'.cells) → (sectorSide j = true))
            → (sectorSide 0 ≠ sectorSide 2 ∨ sectorSide 1 ≠ sectorSide 3))) ) := by
  classical
  intro T0 T0' outerLabel x hsectorOpp sectorSide side_mem_zero side_mem_one
  rcases hsectorOpp with ⟨j, h0, h1⟩
  have hs0 := side_mem_zero j h0
  have hs1 := side_mem_one (j + 2) h1
  fin_cases j
  · exact Or.inl (fun heq => Bool.false_ne_true
      (hs0.symm.trans (heq.trans hs1)))
  · exact Or.inr (fun heq => Bool.false_ne_true
      (hs0.symm.trans (heq.trans hs1)))
  · exact Or.inl (fun heq => Bool.false_ne_true
      (hs0.symm.trans (heq.symm.trans hs1)))
  · exact Or.inr (fun heq => Bool.false_ne_true
      (hs0.symm.trans (heq.symm.trans hs1)))

private theorem diagonal_cells :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)),
        let owner : GaussianInt → TilingLattice Ci := fun c =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P c)
        ∀ (x : GaussianInt),
        let sectorOwner : Fin 4 → TilingLattice Ci := fun j =>
          owner (LatticeVertexIncidentCell x j)
        (∀ (j : Fin 4), ∀ (a : TilingLattice Ci), (sectorOwner j = a) →
            (LatticeVertexIncidentCell x j ∈ (P.tile a).cells)) → (∀ (j : Fin 4), ∀ (U :
            ProtoTile), ∀ (V : ProtoTile), ∀ (a : TilingLattice Ci), ∀ (b : TilingLattice Ci),
            (P.tile a = U) → ((P.tile b = V) → (((sectorOwner j = a ∧ sectorOwner (j + 1) = b) ∨
            (sectorOwner j = b ∧ sectorOwner (j + 1) = a)) → ((sectorOwner j = sectorOwner (j + 3) ∨
            sectorOwner (j + 1) = sectorOwner (j + 2)) → ((x ∈ U.cells ∧ x - 1 - ⟨0, 1⟩ ∈
                V.cells) ∨ (x ∈ V.cells ∧ x - 1 - ⟨0, 1⟩ ∈ U.cells) ∨ (x - 1 ∈ U.cells ∧ x - ⟨0,
                1⟩ ∈ V.cells) ∨ (x - 1 ∈ V.cells ∧ x - ⟨0, 1⟩ ∈ U.cells)))))) ) := by
  classical
  intro Ci P owner x sectorOwner sector_in_tile j U V a b hUa hVb haligned hselect
  have hd : ∃ t : Fin 4,
      (sectorOwner t = a ∧ sectorOwner (t + 2) = b) ∨
      (sectorOwner t = b ∧ sectorOwner (t + 2) = a) := by
    rcases hselect with hsame | hsame
    · refine ⟨j + 1, ?_⟩
      rcases haligned with h | h
      · right
        exact ⟨h.2, by simpa only [add_assoc] using hsame.symm.trans h.1⟩
      · left
        exact ⟨h.2, by simpa only [add_assoc] using hsame.symm.trans h.1⟩
    · refine ⟨j, ?_⟩
      rcases haligned with h | h
      · exact Or.inl ⟨h.1, hsame.symm.trans h.2⟩
      · exact Or.inr ⟨h.1, hsame.symm.trans h.2⟩
  obtain ⟨t, ht⟩ := hd
  have hc :
      (LatticeVertexIncidentCell x t ∈ U.cells ∧
        LatticeVertexIncidentCell x (t + 2) ∈ V.cells) ∨
      (LatticeVertexIncidentCell x t ∈ V.cells ∧
        LatticeVertexIncidentCell x (t + 2) ∈ U.cells) := by
    rcases ht with ht | ht
    · exact Or.inl ⟨by simpa only [hUa] using sector_in_tile t a ht.1,
        by simpa only [hVb] using sector_in_tile (t + 2) b ht.2⟩
    · exact Or.inr ⟨by simpa only [hVb] using sector_in_tile t b ht.1,
        by simpa only [hUa] using sector_in_tile (t + 2) a ht.2⟩
  rcases hc with hc | hc
  · fin_cases t
    · exact Or.inl (by simpa [LatticeVertexIncidentCell] using hc)
    · exact Or.inr (Or.inr (Or.inl
        (by simpa [LatticeVertexIncidentCell] using hc)))
    · exact Or.inr (Or.inl
        (by simpa [LatticeVertexIncidentCell] using ⟨hc.2, hc.1⟩))
    · exact Or.inr (Or.inr (Or.inr
        (by simpa [LatticeVertexIncidentCell] using ⟨hc.2, hc.1⟩)))
  · fin_cases t
    · exact Or.inr (Or.inl (by simpa [LatticeVertexIncidentCell] using hc))
    · exact Or.inr (Or.inr (Or.inr
        (by simpa [LatticeVertexIncidentCell] using hc)))
    · exact Or.inl
        (by simpa [LatticeVertexIncidentCell] using ⟨hc.2, hc.1⟩)
    · exact Or.inr (Or.inr (Or.inl
        (by simpa [LatticeVertexIncidentCell] using ⟨hc.2, hc.1⟩)))

private theorem hchange'At1020 :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        ∀ (x : GaussianInt),
        let sectorSide : Fin 4 → Bool := fun j => decide (outerLabel x j = 1)
        ∀ (i : Fin (4 : ℕ)), (sectorSide i ≠ sectorSide (i + (1 : Fin (4 : ℕ)))) → (outerLabel x
            i ≠ outerLabel x (i + 1)) ) := by
  classical
  intro T0 T0' outerLabel x sectorSide i hchange heq
  exact hchange (by simp only [sectorSide, heq])

private theorem hUVAt1027 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)), (∀ (a :
            TilingLattice Ci), ∀ (b : TilingLattice Ci), (P.tile a = P.tile b) → (a = b)) → (∀
            (UL : ProtoTile), ∀ (VL : ProtoTile), ∀ (iaL : ↥(TilingLattice Ci)), ∀ (ibL :
            ↥(TilingLattice Ci)), (P.tile iaL = UL) → ((P.tile ibL = VL) → ((iaL ≠ ibL) → (UL ≠
            VL)))) ) := by
  classical
  intro Ci P index_eq_of_tile_eq UL VL iaL ibL hULidx hVLidx hidxLne heq
  exact hidxLne (index_eq_of_tile_eq iaL ibL
    (hULidx.trans (heq.trans hVLidx.symm)))

private theorem hUVAt1038 :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)), (∀ (a :
            TilingLattice Ci), ∀ (b : TilingLattice Ci), (P.tile a = P.tile b) → (a = b)) → (∀
            (UR : ProtoTile), ∀ (VR : ProtoTile), ∀ (iaR : ↥(TilingLattice Ci)), ∀ (ibR :
            ↥(TilingLattice Ci)), (P.tile iaR = UR) → ((P.tile ibR = VR) → ((iaR ≠ ibR) → (UR ≠
            VR)))) ) := by
  classical
  intro Ci P index_eq_of_tile_eq UR VR iaR ibR hURidx hVRidx hidxRne heq
  exact hidxRne (index_eq_of_tile_eq iaR ibR
    (hURidx.trans (heq.trans hVRidx.symm)))

end LocalSectorGeometry

namespace LocalSectorConclusions

private theorem initialSector :
    (by
      classical
      exact
        ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (h0
            : PartialOdometer), ∀ (h0' : PartialOdometer), ∀ (Rminus : ProtoTile), ∀ (tiles :
            List ProtoTile), ∀ (reverseTiles : List ProtoTile), ∀ (hs : List PartialOdometer), ∀
            (reverseHs : List PartialOdometer), ∀ (EM : ExactTileInterfaceTriple T0 T0' Rminus),
            (LatticeTile T0) → ((LatticeTile T0') → ((LatticeTile Rminus) → ((Disjoint T0.cells
            T0'.cells) → ((Disjoint T0.cells Rminus.cells) → ((Disjoint T0'.cells Rminus.cells) →
            ((∀ x ∈ FootprintVertices T0, ∀ y ∈ FootprintVertices T0, FourNeighborAdjacent x y →
            {x, y} ∈ FootprintEdges T0) → ((∀ x ∈ FootprintVertices T0', ∀ y ∈ FootprintVertices
            T0', FourNeighborAdjacent x y → {x, y} ∈ FootprintEdges T0') → (∀ (path : List
            GaussianInt), (path.head? = some EM.point) → (∀ (P : PeriodicTileComplex
            ↥(TilingLattice Ci)), ∀ (minusIndex : ↥(TilingLattice Ci)), (P.tile minusIndex =
            Rminus) → ((∀ (U : ProtoTile), ∀ (T : ProtoTile), ∀ (g : PartialOdometer), ∀ (h :
            PartialOdometer), (AncestorOdometer Ci.1.1 C0.1.1 U T g h) → (U.cells ⊆ T.cells)) → (
        let owner : GaussianInt → TilingLattice Ci := fun c =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P c)
        (∀ (a : TilingLattice Ci), ∀ (b : TilingLattice Ci), (P.tile a = P.tile b) → (a = b)) →
            ((∀ (c : GaussianInt), ∀ (a : TilingLattice Ci), c ∈ (P.tile a).cells ↔ owner c = a)
            → ((∀ (x : GaussianInt), owner (LatticeVertexIncidentCell x 0) = owner
            (LatticeVertexIncidentCell x 1) ∨ owner (LatticeVertexIncidentCell x 0) = owner
            (LatticeVertexIncidentCell x 2) ∨ owner (LatticeVertexIncidentCell x 0) = owner
            (LatticeVertexIncidentCell x 3) ∨ owner (LatticeVertexIncidentCell x 1) = owner
            (LatticeVertexIncidentCell x 2) ∨ owner (LatticeVertexIncidentCell x 1) = owner
            (LatticeVertexIncidentCell x 3) ∨ owner (LatticeVertexIncidentCell x 2) = owner
            (LatticeVertexIncidentCell x 3)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (x :
            GaussianInt), ∀ (l : List GaussianInt), ∀ (r : List GaussianInt), (path = l ++ a :: b
            :: r) → ((x = a ∨ x = b) → (∃ U V : ProtoTile, ∃ g k : PartialOdometer, ∃ ia ib :
            TilingLattice Ci, ∃ j : Fin 4, ({a, b} : Finset GaussianInt) = ![{x, x + ⟨0, 1⟩},
            {x - 1, x}, {x - ⟨0, 1⟩, x}, {x, x + 1}] j ∧ U ∈ (tiles.drop 1).dropLast ∧ (U, g) ∈
            tiles.zip hs ∧ {a, b} ∈ FootprintEdges U ∧ AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0 ∧
            V ∈ (reverseTiles.drop 1).dropLast ∧ (V, k) ∈ reverseTiles.zip reverseHs ∧ {a, b} ∈
            FootprintEdges V ∧ AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0' ∧ P.tile ia = U ∧
            P.tile ib = V ∧ ia ≠ ib ∧ (LatticeVertexIncidentCell x j ∈ (P.tile ia).cells ∧
            LatticeVertexIncidentCell x (j + 1) ∈ (P.tile ib).cells ∨ LatticeVertexIncidentCell x
            j ∈ (P.tile ib).cells ∧ LatticeVertexIncidentCell x (j + 1) ∈ (P.tile ia).cells)))) →
            (∀ (x : GaussianInt), (∀ (y : GaussianInt), y = x ∨ y = x + (1 : GaussianInt) ∨ y = x
            - (1 : GaussianInt) ∨ y = x + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y = x - (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt) → y ∈ FootprintVertices T0 ∨ y ∈ FootprintVertices T0') →
            ((path.Nodup) → (((2 : ℕ) ≤ path.length) → ((∀ (e : Finset GaussianInt), e ∈
            FootprintEdges T0 ∩ FootprintEdges T0' ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l :
            List GaussianInt) (r : List GaussianInt), path = l ++ a :: b :: r ∧ e = {a, b}) → ((∀
            (p : List GaussianInt), (p.Nodup) → (∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀
            (rest : List GaussianInt), (p = x :: y :: rest) → (∀ (e : Finset GaussianInt), (∃ a b
            : GaussianInt, ∃ l r : List GaussianInt, p = l ++ a :: b :: r ∧ e = {a, b}) → ((x ∈
            e) → (e = {x, y}))))) → (∀ (pre : List GaussianInt), ∀ (suf : List GaussianInt),
            (path = pre ++ x :: suf) → ((pre = []) → (∃ y : GaussianInt, ∃ U V : ProtoTile, ∃ g k
            : PartialOdometer, ((∃ l r : List GaussianInt, path = l ++ x :: y :: r) ∨ (∃ l r :
            List GaussianInt, path = l ++ y :: x :: r)) ∧ U ≠ V ∧ {x, y} ∈ FootprintEdges U ∩
            FootprintEdges V ∧ U ∈ (tiles.drop 1).dropLast ∧ (U, g) ∈ tiles.zip hs ∧
            AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0 ∧ V ∈ (reverseTiles.drop 1).dropLast ∧ (V,
            k) ∈ reverseTiles.zip reverseHs ∧ AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0' ∧ ((x ∈
            U.cells ∧ x - 1 - ⟨0, 1⟩ ∈ V.cells) ∨ (x ∈ V.cells ∧ x - 1 - ⟨0, 1⟩ ∈ U.cells) ∨ (x -
            1 ∈ U.cells ∧ x - ⟨0, 1⟩ ∈ V.cells) ∨ (x - 1 ∈ V.cells ∧ x - ⟨0, 1⟩ ∈
            U.cells)))))))))))))))))))))))) ) := by
  classical
  intro C0 Ci T0 T0' h0 h0' Rminus tiles reverseTiles hs reverseHs EM hT hT' hRm hdis hTm hT'm
      hreg hreg' path hhead P minusIndex hminusIndex ancestor_cells owner index_eq_of_tile_eq
      owner_mem_iff owner_no_fourfold indexed_transition x hstar hnodup hlength hedgesPath
      first_edge_unique pre suf hsplit hpre
  subst pre
  have hsuf := LocalSectorGeometry.hsuf path x hlength suf hsplit
  obtain ⟨y, rest, rfl⟩ := List.exists_cons_of_ne_nil hsuf
  have hpathEdge : path = [] ++ x :: y :: rest := by simpa using hsplit
  have hstart : x = EM.point := by
    simpa [hpathEdge] using hhead
  rcases indexed_transition x y x [] rest hpathEdge (Or.inl rfl) with
    ⟨U, V, g, k, ia, ib, jEdge, hedgeAt, hUint, hzip, hedgeU,
      hancU, hVint, hzip', hedgeV, hancV, hUidx, hVidx, hidxne,
      hsectorEdge⟩
  have hfinalCells := P5635T1EndpointDiagonalOwnership P owner owner_mem_iff
    owner_no_fourfold T0 T0' Rminus U V EM hT hT' hRm hdis hTm hT'm
    hreg hreg' minusIndex ia ib hminusIndex hUidx hVidx hidxne
    (ancestor_cells U T0 g h0 hancU) (ancestor_cells V T0' k h0' hancV)
    x y hstart hstar ⟨hedgeU, hedgeV⟩ (by
      intro e hxe he
      exact first_edge_unique path hnodup x y rest hpathEdge e
        ((hedgesPath e).mp he) hxe)
  have hUV : U ≠ V := LocalSectorGeometry.hUVAt563 Ci P index_eq_of_tile_eq U V ia ib hUidx
      hVidx hidxne
  exact ⟨y, U, V, g, k, Or.inl ⟨[], rest, hpathEdge⟩,
    hUV, ⟨hedgeU, hedgeV⟩, hUint, hzip, hancU,
    hVint, hzip', hancV, hfinalCells⟩

private theorem terminalSector :
    (by
      classical
      exact
        ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (h0
            : PartialOdometer), ∀ (h0' : PartialOdometer), ∀ (Rplus : ProtoTile), ∀ (tiles : List
            ProtoTile), ∀ (reverseTiles : List ProtoTile), ∀ (hs : List PartialOdometer), ∀
            (reverseHs : List PartialOdometer), ∀ (EP : ExactTileInterfaceTriple T0 T0' Rplus),
            (LatticeTile T0) → ((LatticeTile T0') → ((LatticeTile Rplus) → ((Disjoint T0.cells
            T0'.cells) → ((Disjoint T0.cells Rplus.cells) → ((Disjoint T0'.cells Rplus.cells) →
            ((∀ x ∈ FootprintVertices T0, ∀ y ∈ FootprintVertices T0, FourNeighborAdjacent x y →
            {x, y} ∈ FootprintEdges T0) → ((∀ x ∈ FootprintVertices T0', ∀ y ∈ FootprintVertices
            T0', FourNeighborAdjacent x y → {x, y} ∈ FootprintEdges T0') → (∀ (path : List
            GaussianInt), (path.getLast? = some EP.point) → (∀ (P : PeriodicTileComplex
            ↥(TilingLattice Ci)), ∀ (plusIndex : ↥(TilingLattice Ci)), (P.tile plusIndex = Rplus)
            → ((∀ (U : ProtoTile), ∀ (T : ProtoTile), ∀ (g : PartialOdometer), ∀ (h :
            PartialOdometer), (AncestorOdometer Ci.1.1 C0.1.1 U T g h) → (U.cells ⊆ T.cells)) → (
        let owner : GaussianInt → TilingLattice Ci := fun c =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P c)
        (∀ (a : TilingLattice Ci), ∀ (b : TilingLattice Ci), (P.tile a = P.tile b) → (a = b)) →
            ((∀ (c : GaussianInt), ∀ (a : TilingLattice Ci), c ∈ (P.tile a).cells ↔ owner c = a)
            → ((∀ (x : GaussianInt), owner (LatticeVertexIncidentCell x 0) = owner
            (LatticeVertexIncidentCell x 1) ∨ owner (LatticeVertexIncidentCell x 0) = owner
            (LatticeVertexIncidentCell x 2) ∨ owner (LatticeVertexIncidentCell x 0) = owner
            (LatticeVertexIncidentCell x 3) ∨ owner (LatticeVertexIncidentCell x 1) = owner
            (LatticeVertexIncidentCell x 2) ∨ owner (LatticeVertexIncidentCell x 1) = owner
            (LatticeVertexIncidentCell x 3) ∨ owner (LatticeVertexIncidentCell x 2) = owner
            (LatticeVertexIncidentCell x 3)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (x :
            GaussianInt), ∀ (l : List GaussianInt), ∀ (r : List GaussianInt), (path = l ++ a :: b
            :: r) → ((x = a ∨ x = b) → (∃ U V : ProtoTile, ∃ g k : PartialOdometer, ∃ ia ib :
            TilingLattice Ci, ∃ j : Fin 4, ({a, b} : Finset GaussianInt) = ![{x, x + ⟨0, 1⟩},
            {x - 1, x}, {x - ⟨0, 1⟩, x}, {x, x + 1}] j ∧ U ∈ (tiles.drop 1).dropLast ∧ (U, g) ∈
            tiles.zip hs ∧ {a, b} ∈ FootprintEdges U ∧ AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0 ∧
            V ∈ (reverseTiles.drop 1).dropLast ∧ (V, k) ∈ reverseTiles.zip reverseHs ∧ {a, b} ∈
            FootprintEdges V ∧ AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0' ∧ P.tile ia = U ∧
            P.tile ib = V ∧ ia ≠ ib ∧ (LatticeVertexIncidentCell x j ∈ (P.tile ia).cells ∧
            LatticeVertexIncidentCell x (j + 1) ∈ (P.tile ib).cells ∨ LatticeVertexIncidentCell x
            j ∈ (P.tile ib).cells ∧ LatticeVertexIncidentCell x (j + 1) ∈ (P.tile ia).cells)))) →
            (∀ (x : GaussianInt), (∀ (y : GaussianInt), y = x ∨ y = x + (1 : GaussianInt) ∨ y = x
            - (1 : GaussianInt) ∨ y = x + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y = x - (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt) → y ∈ FootprintVertices T0 ∨ y ∈ FootprintVertices T0') →
            ((path.Nodup) → ((∀ (e : Finset GaussianInt), e ∈ FootprintEdges T0 ∩ FootprintEdges
            T0' ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l : List GaussianInt) (r : List
            GaussianInt), path = l ++ a :: b :: r ∧ e = {a, b}) → ((∀ (p : List GaussianInt),
            (p.Nodup) → (∀ (x : GaussianInt), ∀ (z : GaussianInt), ∀ (rest : List GaussianInt),
            (p = rest ++ z :: x :: []) → (∀ (e : Finset GaussianInt), (∃ a b : GaussianInt, ∃ l r
            : List GaussianInt, p = l ++ a :: b :: r ∧ e = {a, b}) → ((x ∈ e) → (e = {z, x})))))
            → (∀ (pre : List GaussianInt), (¬pre = []) → ((path = pre ++ [x]) → (∃ y :
            GaussianInt, ∃ U V : ProtoTile, ∃ g k : PartialOdometer, ((∃ l r : List GaussianInt,
            path = l ++ x :: y :: r) ∨ (∃ l r : List GaussianInt, path = l ++ y :: x :: r)) ∧ U ≠
            V ∧ {x, y} ∈ FootprintEdges U ∩ FootprintEdges V ∧ U ∈ (tiles.drop 1).dropLast ∧ (U,
            g) ∈ tiles.zip hs ∧ AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0 ∧ V ∈ (reverseTiles.drop
            1).dropLast ∧ (V, k) ∈ reverseTiles.zip reverseHs ∧ AncestorOdometer Ci.1.1 C0.1.1 V
            T0' k h0' ∧ ((x ∈ U.cells ∧ x - 1 - ⟨0, 1⟩ ∈ V.cells) ∨ (x ∈ V.cells ∧ x - 1 - ⟨0, 1⟩
            ∈ U.cells) ∨ (x - 1 ∈ U.cells ∧ x - ⟨0, 1⟩ ∈ V.cells) ∨ (x - 1 ∈ V.cells ∧ x - ⟨0, 1⟩
            ∈ U.cells))))))))))))))))))))))) ) := by
  classical
  intro C0 Ci T0 T0' h0 h0' Rplus tiles reverseTiles hs reverseHs EP hT hT' hRp hdis hTp hT'p
      hreg hreg' path hlast P plusIndex hplusIndex ancestor_cells owner index_eq_of_tile_eq
      owner_mem_iff owner_no_fourfold indexed_transition x hstar hnodup hedgesPath
      last_edge_unique pre hpre hsplit
  have hpre' : pre ≠ [] := hpre
  let z := pre.getLast hpre'
  let pre' := pre.dropLast
  have hpreEq : pre' ++ [z] = pre := List.dropLast_append_getLast hpre'
  have hpathLast : path = pre' ++ z :: x :: [] := LocalSectorGeometry.hpathLast path x pre
      hsplit hpre' hpreEq
  have hend : x = EP.point := by
    simpa [hsplit] using hlast
  rcases indexed_transition z x x pre' [] hpathLast (Or.inr rfl) with
    ⟨U, V, g, k, ia, ib, jEdge, hedgeAt, hUint, hzip, hedgeU,
      hancU, hVint, hzip', hedgeV, hancV, hUidx, hVidx, hidxne,
      hsectorEdge⟩
  have hfinalCells := P5635T1EndpointDiagonalOwnership P owner owner_mem_iff
    owner_no_fourfold T0 T0' Rplus U V EP hT hT' hRp hdis hTp hT'p
    hreg hreg' plusIndex ia ib hplusIndex hUidx hVidx hidxne
    (ancestor_cells U T0 g h0 hancU) (ancestor_cells V T0' k h0' hancV)
    x z hend hstar
    ⟨by simpa [Finset.pair_comm] using hedgeU,
      by simpa [Finset.pair_comm] using hedgeV⟩ (by
        intro e hxe he
        simpa [Finset.pair_comm] using
          last_edge_unique path hnodup x z pre' hpathLast e
            ((hedgesPath e).mp he) hxe)
  have hUV : U ≠ V := LocalSectorGeometry.hUVAt563 Ci P index_eq_of_tile_eq U V ia ib hUidx
      hVidx hidxne
  exact ⟨z, U, V, g, k, Or.inr ⟨pre', [], hpathLast⟩,
    hUV, ⟨by simpa [Finset.pair_comm] using hedgeU,
      by simpa [Finset.pair_comm] using hedgeV⟩, hUint, hzip, hancU,
    hVint, hzip', hancV, hfinalCells⟩

private theorem interiorSector :
    (by
      classical
      exact
        ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (h0
            : PartialOdometer), ∀ (h0' : PartialOdometer), ∀ (tiles : List ProtoTile), ∀
            (reverseTiles : List ProtoTile), ∀ (hs : List PartialOdometer), ∀ (reverseHs : List
            PartialOdometer), (LatticeTile T0) → ((LatticeTile T0') → ((Disjoint T0.cells
            T0'.cells) → (∀ (path : List GaussianInt), ∀ (P : PeriodicTileComplex ↥(TilingLattice
            Ci)),
        let neighbor (x : GaussianInt) : Fin 4 → GaussianInt :=
          ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (x : GaussianInt), ∀ (j : Fin 4), x ∈ edgeAt x j ∧ neighbor x j ∈ edgeAt x j) → ((∀ (x
            : GaussianInt), ∀ {j : Fin 4}, ∀ {k : Fin 4}, (edgeAt x j = edgeAt x k) → (j = k)) →
            ((∀ (R : ProtoTile), ∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x
            j ∈ R.cells ∨ LatticeVertexIncidentCell x (j + 1) ∈ R.cells) → (edgeAt x j ∈
            FootprintEdges R)) → (
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0.cells) →
            (outerLabel x j = 0)) → ((∀ (x : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell x j ∈ T0'.cells) → (outerLabel x j = 1)) → ((∀ (U :
            ProtoTile), ∀ (T : ProtoTile), ∀ (g : PartialOdometer), ∀ (h : PartialOdometer),
            (AncestorOdometer Ci.1.1 C0.1.1 U T g h) → (U.cells ⊆ T.cells)) → (
        let owner : GaussianInt → TilingLattice Ci := fun c =>
          Classical.choose (PeriodicTileIndexedMultiplicityOne P c)
        (∀ (c : GaussianInt), ∀ (a : TilingLattice Ci), (c ∈ (P.tile a).cells) → (owner c = a)) →
            ((∀ (a : TilingLattice Ci), ∀ (b : TilingLattice Ci), (P.tile a = P.tile b) → (a =
            b)) → ((∀ (c : GaussianInt), ∀ (a : TilingLattice Ci), c ∈ (P.tile a).cells ↔ owner c
            = a) → ((∀ (x : GaussianInt), owner (LatticeVertexIncidentCell x 0) = owner
            (LatticeVertexIncidentCell x 1) ∨ owner (LatticeVertexIncidentCell x 0) = owner
            (LatticeVertexIncidentCell x 2) ∨ owner (LatticeVertexIncidentCell x 0) = owner
            (LatticeVertexIncidentCell x 3) ∨ owner (LatticeVertexIncidentCell x 1) = owner
            (LatticeVertexIncidentCell x 2) ∨ owner (LatticeVertexIncidentCell x 1) = owner
            (LatticeVertexIncidentCell x 3) ∨ owner (LatticeVertexIncidentCell x 2) = owner
            (LatticeVertexIncidentCell x 3)) → ((∀ (x : GaussianInt), ∀ (a : TilingLattice Ci), ¬
            ((owner (LatticeVertexIncidentCell x 0) = a ∧ owner (LatticeVertexIncidentCell x 2) =
            a ∧ owner (LatticeVertexIncidentCell x 1) ≠ a ∧ owner (LatticeVertexIncidentCell x 3)
            ≠ a) ∨ (owner (LatticeVertexIncidentCell x 1) = a ∧ owner (LatticeVertexIncidentCell
            x 3) = a ∧ owner (LatticeVertexIncidentCell x 0) ≠ a ∧ owner
            (LatticeVertexIncidentCell x 2) ≠ a))) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt),
            ∀ (x : GaussianInt), ∀ (l : List GaussianInt), ∀ (r : List GaussianInt), (path = l ++
            a :: b :: r) → ((x = a ∨ x = b) → (∃ U V : ProtoTile, ∃ g k : PartialOdometer, ∃ ia
            ib : TilingLattice Ci, ∃ j : Fin 4, ({a, b} : Finset GaussianInt) = ![{x, x + ⟨0,
            1⟩}, {x - 1, x}, {x - ⟨0, 1⟩, x}, {x, x + 1}] j ∧ U ∈ (tiles.drop 1).dropLast ∧ (U,
            g) ∈ tiles.zip hs ∧ {a, b} ∈ FootprintEdges U ∧ AncestorOdometer Ci.1.1 C0.1.1 U T0 g
            h0 ∧ V ∈ (reverseTiles.drop 1).dropLast ∧ (V, k) ∈ reverseTiles.zip reverseHs ∧ {a,
            b} ∈ FootprintEdges V ∧ AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0' ∧ P.tile ia = U ∧
            P.tile ib = V ∧ ia ≠ ib ∧ (LatticeVertexIncidentCell x j ∈ (P.tile ia).cells ∧
            LatticeVertexIncidentCell x (j + 1) ∈ (P.tile ib).cells ∨ LatticeVertexIncidentCell x
            j ∈ (P.tile ib).cells ∧ LatticeVertexIncidentCell x (j + 1) ∈ (P.tile ia).cells)))) →
            (∀ (x : GaussianInt), (x ∈ path) → ((∀ (y : GaussianInt), y = x ∨ y = x + (1 :
            GaussianInt) ∨ y = x - (1 : GaussianInt) ∨ y = x + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)
            ∨ y = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) → y ∈ FootprintVertices T0 ∨ y ∈
            FootprintVertices T0') → ((path.Nodup) → ((∀ (e : Finset GaussianInt), e ∈
            FootprintEdges T0 ∩ FootprintEdges T0' ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l :
            List GaussianInt) (r : List GaussianInt), path = l ++ a :: b :: r ∧ e = {a, b}) → (∀
            (pre : List GaussianInt), (¬pre = []) → (∀ (y : GaussianInt), ∀ (rest : List
            GaussianInt), (path = pre ++ x :: y :: rest) → (∃ y : GaussianInt, ∃ U V : ProtoTile,
            ∃ g k : PartialOdometer, ((∃ l r : List GaussianInt, path = l ++ x :: y :: r) ∨ (∃ l
            r : List GaussianInt, path = l ++ y :: x :: r)) ∧ U ≠ V ∧ {x, y} ∈ FootprintEdges U ∩
            FootprintEdges V ∧ U ∈ (tiles.drop 1).dropLast ∧ (U, g) ∈ tiles.zip hs ∧
            AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0 ∧ V ∈ (reverseTiles.drop 1).dropLast ∧ (V,
            k) ∈ reverseTiles.zip reverseHs ∧ AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0' ∧ ((x ∈
            U.cells ∧ x - 1 - ⟨0, 1⟩ ∈ V.cells) ∨ (x ∈ V.cells ∧ x - 1 - ⟨0, 1⟩ ∈ U.cells) ∨ (x -
            1 ∈ U.cells ∧ x - ⟨0, 1⟩ ∈ V.cells) ∨ (x - 1 ∈ V.cells ∧ x - ⟨0, 1⟩ ∈
            U.cells))))))))))))))))))))))) ) := by
  classical
  intro C0 Ci T0 T0' h0 h0' tiles reverseTiles hs reverseHs hT hT' hdis path P neighbor edgeAt
      edgeAt_mem edgeAt_injective edge_of_sector_cell outerLabel label_T0 label_T0'
      ancestor_cells owner owner_unique index_eq_of_tile_eq owner_mem_iff owner_no_fourfold
      owner_no_checkerboard indexed_transition x hx hstar hnodup hedgesPath pre hpre y rest hsplit
  have hpre' : pre ≠ [] := hpre
  let z := pre.getLast hpre'
  let pre' := pre.dropLast
  have hpreEq : pre' ++ [z] = pre := List.dropLast_append_getLast hpre'
  have hleft : path = pre' ++ z :: x :: y :: rest := LocalSectorGeometry.hleft path x pre y
      rest hsplit hpre' hpreEq
  have hright : path = pre ++ x :: y :: rest := hsplit
  have hleftWitness := indexed_transition z x x pre' (y :: rest)
    hleft (Or.inr rfl)
  have hrightWitness := indexed_transition x y x pre rest hright (Or.inl rfl)
  rcases hleftWitness with ⟨UL, VL, gL, kL, iaL, ibL, jL, eL,
    hULint, hULzip, hedgeUL, hancUL, hVLint, hVLzip, hedgeVL,
    hancVL, hULidx, hVLidx, hidxLne, hsectorL⟩
  rcases hrightWitness with ⟨UR, VR, gR, kR, iaR, ibR, jR, eR,
    hURint, hURzip, hedgeUR, hancUR, hVRint, hVRzip, hedgeVR,
    hancVR, hURidx, hVRidx, hidxRne, hsectorR⟩
  have hnodupPath : (pre' ++ z :: x :: y :: rest).Nodup := by
    simpa [hleft] using hnodup
  have htailNodup : (z :: x :: y :: rest).Nodup :=
    (List.nodup_append.mp hnodupPath).2.1
  have hznot : z ∉ x :: y :: rest := (List.nodup_cons.mp htailNodup).1
  have hzx : z ≠ x := by
    intro heq
    subst x
    exact hznot (List.mem_cons_self ..)
  have hzy : z ≠ y := by
    intro heq
    subst y
    exact hznot (List.mem_cons_of_mem x (List.mem_cons_self ..))
  have hEdgeNe : ({z, x} : Finset GaussianInt) ≠ {x, y} := LocalSectorGeometry.hEdgeNe x
      pre y hpre' hzx hzy
  have hjne := LocalSectorGeometry.hjne x pre y hpre' jL eL jR eR hzx hzy
  have hedgeL : {z, x} ∈ FootprintEdges T0 ∩ FootprintEdges T0' :=
    (hedgesPath {z, x}).mpr ⟨z, x, pre', y :: rest, hleft, rfl⟩
  have hedgeR : {x, y} ∈ FootprintEdges T0 ∩ FootprintEdges T0' :=
    (hedgesPath {x, y}).mpr ⟨x, y, pre, rest, hright, rfl⟩
  obtain ⟨hsectorOuter, hsectorOpp⟩ := (LocalLatticeInterfaceSectors.2
    T0 T0' x hT hT' hdis
    ⟨{z, x}, {x, y}, hEdgeNe, by simp, by simp, hedgeL, hedgeR⟩)
  have hULsub : UL.cells ⊆ T0.cells :=
    ancestor_cells UL T0 gL h0 hancUL
  have hVLsub : VL.cells ⊆ T0'.cells :=
    ancestor_cells VL T0' kL h0' hancVL
  have hURsub : UR.cells ⊆ T0.cells :=
    ancestor_cells UR T0 gR h0 hancUR
  have hVRsub : VR.cells ⊆ T0'.cells :=
    ancestor_cells VR T0' kR h0' hancVR
  have hLaligned := LocalSectorGeometry.hLaligned Ci T0 T0' P label_T0 label_T0'
      owner_unique x UL VL iaL ibL jL hULidx hVLidx hsectorL hULsub hVLsub
  have hRaligned := LocalSectorGeometry.hRaligned Ci T0 T0' P label_T0 label_T0'
      owner_unique x UR VR iaR ibR jR hURidx hVRidx hsectorR hURsub hVRsub
  have transition_is_path_edge := LocalSectorGeometry.transition_is_path_edge T0 T0' path
      edgeAt_mem edgeAt_injective edge_of_sector_cell x hedgesPath pre y hpre' jL eL jR eR
      (LocalSectorGeometry.internal_edge_unique path x hnodup pre y hpre'
      (LocalSectorGeometry.hidxX path x pre y rest hpre' hleft hnodupPath)
      (LocalSectorGeometry.hidxY path x pre y rest hpre' hleft hnodupPath)
      (LocalSectorGeometry.hidxZ path x pre y rest hpre' hleft hnodupPath))
      (LocalSectorGeometry.outer_side_class T0 T0' label_T0 label_T0' x hsectorOuter)
  let sectorOwner : Fin 4 → TilingLattice Ci := fun j =>
    owner (LatticeVertexIncidentCell x j)
  let sectorSide : Fin 4 → Bool := fun j => decide (outerLabel x j = 1)
  have side_mem_zero := LocalSectorGeometry.side_mem_zero T0 T0' label_T0 x
  have side_mem_one := LocalSectorGeometry.side_mem_one T0 T0' label_T0' x
  have sector_in_tile := LocalSectorGeometry.sector_in_tile Ci P owner_mem_iff x
  have side_same_T0 := LocalSectorGeometry.side_same_T0 Ci T0 T0' P x side_mem_zero
      sector_in_tile
  have side_same_T0' := LocalSectorGeometry.side_same_T0' Ci T0 T0' P x side_mem_one
      sector_in_tile
  have side_consistent_left := LocalSectorGeometry.side_consistent_left Ci T0 T0' P x UL VL
      iaL ibL jL hULidx hVLidx UR VR iaR ibR jR hURidx hVRidx hULsub hVLsub hURsub hVRsub
      hLaligned hRaligned transition_is_path_edge side_same_T0 side_same_T0'
  have side_consistent_right := LocalSectorGeometry.side_consistent_right Ci T0 T0' P x UL
      VL iaL ibL jL hULidx hVLidx UR VR iaR ibR jR hURidx hVRidx hULsub hVLsub hURsub
      hVRsub hLaligned hRaligned transition_is_path_edge side_same_T0 side_same_T0'
  have hownerRepeat := owner_no_fourfold x
  have hownerCheckA := owner_no_checkerboard x (sectorOwner 0)
  have hownerCheckB := owner_no_checkerboard x (sectorOwner 1)
  have hownerOpp := LocalSectorGeometry.hownerOpp T0 T0' x hsectorOpp side_mem_zero
      side_mem_one
  obtain ⟨i, hchange, hselected⟩ := P4431T1OwnerTransitionSelector
    sectorOwner sectorSide side_consistent_left side_consistent_right
    hownerRepeat (by
      intro hcheck
      rcases hcheck with h | h
      · exact hownerCheckA (Or.inl ⟨rfl, h.1.symm, h.2.1, h.2.2⟩)
      · exact hownerCheckB (Or.inr ⟨rfl, h.1.symm, h.2.1, h.2.2⟩))
    hownerOpp
  have diagonal_cells := LocalSectorGeometry.diagonal_cells Ci P x sector_in_tile
  have hchange' := LocalSectorGeometry.hchange'At1020 T0 T0' x i hchange
  rcases transition_is_path_edge i hchange' with hi | hi <;> subst i
  · have hd := diagonal_cells jL UL VL iaL ibL hULidx hVLidx
      (hLaligned.imp (fun h => ⟨h.1.2, h.2.2⟩) (fun h => ⟨h.1.2, h.2.2⟩))
      hselected
    have hUV : UL ≠ VL := LocalSectorGeometry.hUVAt1027 Ci P index_eq_of_tile_eq UL VL iaL
        ibL hULidx hVLidx hidxLne
    exact ⟨z, UL, VL, gL, kL, Or.inr ⟨pre', y :: rest, hleft⟩,
      hUV, ⟨by simpa only [Finset.pair_comm] using hedgeUL,
        by simpa only [Finset.pair_comm] using hedgeVL⟩,
      hULint, hULzip, hancUL, hVLint, hVLzip, hancVL, hd⟩
  · have hd := diagonal_cells jR UR VR iaR ibR hURidx hVRidx
      (hRaligned.imp (fun h => ⟨h.1.2, h.2.2⟩) (fun h => ⟨h.1.2, h.2.2⟩))
      hselected
    have hUV : UR ≠ VR := LocalSectorGeometry.hUVAt1038 Ci P index_eq_of_tile_eq UR VR iaR
        ibR hURidx hVRidx hidxRne
    exact ⟨y, UR, VR, gR, kR, Or.inl ⟨pre, rest, hright⟩,
      hUV, ⟨hedgeUR, hedgeVR⟩,
      hURint, hURzip, hancUR, hVRint, hVRzip, hancVR, hd⟩

end LocalSectorConclusions

theorem P4366T2LocalSectors
    (C0 Ci : BandCircle) (hlarge : 1 < Ci.1.1.1)
    (T0 T0' : ProtoTile) (h0 h0' : PartialOdometer)
    (orientation : Bool) (base Rminus Rplus : ProtoTile)
    (tiles reverseTiles : List ProtoTile) (hs reverseHs : List PartialOdometer)
    (hf : TileString Ci orientation base Rminus Rplus tiles)
    (hr : TileString Ci orientation base Rplus Rminus reverseTiles)
    (EM : ExactTileInterfaceTriple T0 T0' Rminus)
    (EP : ExactTileInterfaceTriple T0 T0' Rplus)
    (hT : LatticeTile T0) (hT' : LatticeTile T0')
    (hRm : LatticeTile Rminus) (hRp : LatticeTile Rplus)
    (hdis : Disjoint T0.cells T0'.cells)
    (hTm : Disjoint T0.cells Rminus.cells)
    (hT'm : Disjoint T0'.cells Rminus.cells)
    (hTp : Disjoint T0.cells Rplus.cells)
    (hT'p : Disjoint T0'.cells Rplus.cells)
    (hreg : ∀ x, x ∈ FootprintVertices T0 → ∀ y, y ∈ FootprintVertices T0 →
      FourNeighborAdjacent x y → {x, y} ∈ FootprintEdges T0)
    (hreg' : ∀ x, x ∈ FootprintVertices T0' → ∀ y, y ∈ FootprintVertices T0' →
      FourNeighborAdjacent x y → {x, y} ∈ FootprintEdges T0')
    (path : List GaussianInt)
    (hp : path.Nodup ∧ 2 ≤ path.length ∧
      path.head? = some EM.point ∧ path.getLast? = some EP.point ∧
      FootprintVertices T0 ∩ FootprintVertices T0' = (path.toFinset : Set GaussianInt) ∧
      (∀ a b : GaussianInt, ∀ l r : List GaussianInt,
        path = l ++ a :: b :: r → FourNeighborAdjacent a b) ∧
      ∀ e, e ∈ FootprintEdges T0 ∩ FootprintEdges T0' ↔
        ∃ a b : GaussianInt, ∃ l r : List GaussianInt,
          path = l ++ a :: b :: r ∧ e = {a, b})
    (hedges : ∀ a b : GaussianInt, ∀ l r : List GaussianInt,
      path = l ++ a :: b :: r →
      (∃ U g, U ∈ (tiles.drop 1).dropLast ∧ (U, g) ∈ tiles.zip hs ∧
        {a, b} ∈ FootprintEdges U ∧
        AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0) ∧
      (∃ V k, V ∈ (reverseTiles.drop 1).dropLast ∧
        (V, k) ∈ reverseTiles.zip reverseHs ∧ {a, b} ∈ FootprintEdges V ∧
        AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0')) :
    ∀ x, x ∈ path →
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices T0 ∨ y ∈ FootprintVertices T0') →
      ∃ y : GaussianInt, ∃ U V : ProtoTile, ∃ g k : PartialOdometer,
        ((∃ l r : List GaussianInt, path = l ++ x :: y :: r) ∨
          (∃ l r : List GaussianInt, path = l ++ y :: x :: r)) ∧
        U ≠ V ∧ {x, y} ∈ FootprintEdges U ∩ FootprintEdges V ∧
        U ∈ (tiles.drop 1).dropLast ∧ (U, g) ∈ tiles.zip hs ∧
        AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0 ∧
        V ∈ (reverseTiles.drop 1).dropLast ∧
        (V, k) ∈ reverseTiles.zip reverseHs ∧
        AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0' ∧
        ((x ∈ U.cells ∧ x - 1 - ⟨0, 1⟩ ∈ V.cells) ∨
          (x ∈ V.cells ∧ x - 1 - ⟨0, 1⟩ ∈ U.cells) ∨
          (x - 1 ∈ U.cells ∧ x - ⟨0, 1⟩ ∈ V.cells) ∨
          (x - 1 ∈ V.cells ∧ x - ⟨0, 1⟩ ∈ U.cells)) := by
-- BODY
  classical
  rcases hf with ⟨hbase, hhead, hlast, hpair, hfamily, hchain, hheight⟩
  have hgene := BandGenealogy Ci
  rcases hgene with hunit | ⟨q, hsemi, hq0, hbelow, hcanonical⟩
  · simp [hunit] at hlarge
  · have hbelow' : ∀ j : Fin 3, (q j.succ).1 < (q 0).1 := by
      simpa [hq0] using hbelow
    have hproper : ProperBandQuadruple q := ⟨hsemi, hbelow'⟩
    have hbase' : BandPrototile (q 0) base := by simpa [hq0] using hbase
    obtain ⟨P, hPlattice, htiles, hadjacent, hposition, hvertices, hedgesP,
      hfaces, hchart⟩ := BandRegularTranslatePeriodicComplex Ci q hproper hq0
        base hbase'
    let tileAt : Int × Int → ProtoTile := fun mn => TileTranslation base
      ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
        (mn.2 : GaussianInt) * BandVectors.1 (q 2) (q 0))
    let chart : AffineTriangularComplexChart P tileAt := Classical.choice hchart
    have regular_index := LocalSectorGeometry.regular_index Ci base P htiles
    have htiles_lattice := LocalSectorGeometry.htiles_lattice Ci base q hproper hbase' P htiles
    let neighbor (x : GaussianInt) : Fin 4 → GaussianInt :=
      ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
    let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
      ![{x, x + ⟨0, 1⟩}, {x - 1, x},
        {x - ⟨0, 1⟩, x}, {x, x + 1}]
    have edgeAt_mem := LatticeVertexSectorFacts.edgeMembership
    have edgeAt_eq_pair := LatticeVertexSectorFacts.edgePair
    have edgeAt_injective (x : GaussianInt) {j k : Fin 4}
        (h : edgeAt x j = edgeAt x k) := LatticeVertexSectorFacts.edgeInjective
            (LatticeVertexSectorFacts.neighborDistinct) (LocalSectorGeometry.neighbor_injective)
                edgeAt_mem x (j := j) (k := k) h
    have edge_of_sector_cell := LocalSectorGeometry.edge_of_sector_cell
    let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
      if LatticeVertexIncidentCell x j ∈ T0.cells then 0
      else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
    have label_T0 := LatticeVertexSectorFacts.firstTileLabel T0 T0'
    have label_T0' := LatticeVertexSectorFacts.secondTileLabel T0 T0' hdis
    rcases hr with ⟨hbaseR, hheadR, hlastR, hpairR, hfamilyR, hchainR, hheightR⟩
    have forward_index := LocalSectorGeometry.forward_index Ci base tiles hs hfamily P regular_index
    have reverse_index := LocalSectorGeometry.reverse_index Ci base reverseTiles reverseHs P
        regular_index hfamilyR
    obtain ⟨minusIndex, hminusIndex⟩ := regular_index Rminus
      (hfamily Rminus (List.mem_of_head? hhead))
    obtain ⟨plusIndex, hplusIndex⟩ := regular_index Rplus
      (hfamily Rplus (List.mem_of_getLast? hlast))
    have ancestor_cells (U T : ProtoTile) (g h : PartialOdometer)
        (hanc : AncestorOdometer Ci.1.1 C0.1.1 U T g h) :
        U.cells ⊆ T.cells :=
      P4158T1AncestorCells Ci.1.1 C0.1.1 U T hanc.2.1
    let owner : GaussianInt → TilingLattice Ci := fun c =>
      Classical.choose (PeriodicTileIndexedMultiplicityOne P c)
    have owner_cell (c : GaussianInt) : c ∈ (P.tile (owner c)).cells :=
      (Classical.choose_spec (PeriodicTileIndexedMultiplicityOne P c)).1
    have owner_unique (c : GaussianInt) (a : TilingLattice Ci)
        (hc : c ∈ (P.tile a).cells) : owner c = a :=
      (PeriodicTileIndexedMultiplicityOne P c).unique (owner_cell c) hc
    have index_eq_of_tile_eq := LocalSectorGeometry.index_eq_of_tile_eq Ci P htiles_lattice
    have owner_mem_iff := LocalSectorGeometry.owner_mem_iff Ci P owner_cell owner_unique
    have owner_eq_tile := LocalSectorGeometry.owner_eq_tile Ci P owner_unique
    have owner_no_fourfold := LocalSectorGeometry.owner_no_fourfold Ci P owner_cell
        (@LocalSectorGeometry.no_fourfold Ci base q P hchart)
    have owner_no_checkerboard := LocalSectorGeometry.owner_no_checkerboard Ci P htiles_lattice
        owner_mem_iff
    have cross_ne := LocalSectorGeometry.cross_ne Ci T0 T0' hdis P htiles_lattice
    have indexed_transition := LocalSectorGeometry.indexed_transition C0 Ci T0 T0' h0 h0' tiles
        reverseTiles hs reverseHs hdis path P ancestor_cells
        (LocalSectorGeometry.indexed_edge_witnesses C0 Ci T0 T0' h0 h0' tiles reverseTiles hs
        reverseHs hdis path hedges P htiles_lattice forward_index reverse_index ancestor_cells)
    intro x hx hstar
    rcases hp with ⟨hnodup, hlength, hhead, hlast, hvertices, hstep, hedgesPath⟩
    have first_edge_unique := LocalSectorGeometry.first_edge_unique
    have last_edge_unique (p : List GaussianInt) (hpNodup : p.Nodup)
        (x z : GaussianInt) (rest : List GaussianInt)
        (hpath : p = rest ++ z :: x :: []) (e : Finset GaussianInt)
        (he : ∃ a b : GaussianInt, ∃ l r : List GaussianInt,
          p = l ++ a :: b :: r ∧ e = {a, b})
        (hxe : x ∈ e) := LocalSectorGeometry.last_edge_unique first_edge_unique
            (LocalSectorGeometry.reverse_edge_decomp) p hpNodup x z rest hpath e he hxe
    have split_mem := LocalSectorGeometry.split_mem
    obtain ⟨pre, suf, hsplit⟩ := split_mem path x hx
    by_cases hpre : pre = []
    · have initialSector := LocalSectorConclusions.initialSector C0 Ci T0 T0' h0 h0' Rminus tiles
        reverseTiles hs reverseHs EM hT hT' hRm hdis hTm hT'm hreg hreg' path hhead P minusIndex
        hminusIndex ancestor_cells index_eq_of_tile_eq owner_mem_iff owner_no_fourfold
        indexed_transition x hstar hnodup hlength hedgesPath first_edge_unique pre suf hsplit hpre
      exact initialSector
    · cases suf
      · have terminalSector := LocalSectorConclusions.terminalSector C0 Ci T0 T0' h0 h0' Rplus
          tiles reverseTiles hs reverseHs EP hT hT' hRp hdis hTp hT'p hreg hreg' path hlast P
          plusIndex hplusIndex ancestor_cells index_eq_of_tile_eq owner_mem_iff owner_no_fourfold
          indexed_transition x hstar hnodup hedgesPath last_edge_unique pre hpre hsplit
        exact terminalSector
      · rename_i y rest
        exact (LocalSectorConclusions.interiorSector C0 Ci T0 T0' h0 h0' tiles reverseTiles hs
            reverseHs hT hT' hdis path P edgeAt_mem edgeAt_injective edge_of_sector_cell label_T0
            label_T0' ancestor_cells owner_unique index_eq_of_tile_eq owner_mem_iff
            owner_no_fourfold owner_no_checkerboard indexed_transition x hx hstar hnodup
            hedgesPath pre hpre y rest hsplit)

end ApollonianSuperharmonic

end
