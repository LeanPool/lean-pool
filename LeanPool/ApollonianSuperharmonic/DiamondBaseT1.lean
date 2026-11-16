/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence
public import LeanPool.ApollonianSuperharmonic.DiamondRecursiveQuadruple
public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.DiamondTileGeometry
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.TileCellComplement
public import LeanPool.ApollonianSuperharmonic.TileArea
public import LeanPool.ApollonianSuperharmonic.TileTouching
public import LeanPool.ApollonianSuperharmonic.DiamondTileRecursiveIdentification
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.P5116T1UnitDeletionDisk
public import LeanPool.ApollonianSuperharmonic.P5116T1PredecessorDeletionDisk
public import LeanPool.ApollonianSuperharmonic.LatticeTileDiskUnionInterface
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance

-- [TABLET NODE: DiamondBaseT1]

/-!
# DiamondBaseT1

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem DiamondBaseT1 (K : DiamondParameter)
    (S : Fin 3 → Bool → ProtoTile)
    (hS : ∀ i s, BandSubtileOccurrence (DiamondRecursiveQuadruple K)
      (DiamondTile K.1) i s (S i s))
    (hunion : ∀ x, x ∈ (DiamondTile K.1).cells ↔
      ∃ i s, x ∈ (S i s).cells) :
    LatticeTile (DiamondTile K.1) ∧
      TileArea (DiamondTile K.1) =
        Int.toNat ((DiamondRecursiveQuadruple K) 0).1 ∧
      ∀ i s, LatticeTile (TileCellComplement (DiamondTile K.1) (S i s)) ∧
        TileTouching (TileCellComplement (DiamondTile K.1) (S i s))
          (S i s) := by
-- BODY
  classical
  have hk := K.2
  have hgeometry := DiamondTileGeometry K.1 hk
  have harea : TileArea (DiamondTile K.1) =
      Int.toNat ((DiamondRecursiveQuadruple K) 0).1 := by
    rw [hgeometry.2]
    change 2 * K.1 * (K.1 + 1) = (2 * (K.1 : Int) * ((K.1 : Int) + 1)).toNat
    have he : ((2 * K.1 * (K.1 + 1) : Nat) : Int) =
        2 * (K.1 : Int) * ((K.1 : Int) + 1) := by push_cast; rfl
    rw [← he, Int.toNat_natCast]
  obtain ⟨_, R, hR, _, h00, h01, h10, h11, h20, h21⟩ :=
    DiamondTileRecursiveIdentification K
  have identify (i : Fin 3) (s : Bool) :
      (S i s).cells = (R i s).cells ∧
      ((S i s).cells = ∅ → (S i s).anchor = (R i s).anchor) := by
    apply BandPrototileCentroidUnique _ _ _ (hS i s).1 (hR i s).1
    exact sub_left_inj.mp ((hS i s).2.2.trans (hR i s).2.2.symm)
  have cell_mem (k : Nat) (z : GaussianInt) :
      z ∈ (DiamondTile k).cells ↔
        0 ≤ z.im ∧ z.im < 2 * (k : Int) ∧
        -(z.im + 1) ≤ z.re ∧ z.re < z.im + 1 ∧
        -(2 * (k : Int) - z.im) ≤ z.re ∧ z.re < 2 * (k : Int) - z.im :=
    (P4194T1DiamondCellRows k z).1
  have translated_mem (k : Nat) (z : GaussianInt) :
      z ∈ (TileTranslation (DiamondTile k) ⟨0, 2⟩).cells ↔
        z - ⟨0, 2⟩ ∈ (DiamondTile k).cells := by
    change z ∈ (DiamondTile k).cells.image (GaussianTranslation ⟨0, 2⟩) ↔ _
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      simpa [GaussianTranslation] using hy
    · intro hz
      exact Finset.mem_image.mpr ⟨z - ⟨0, 2⟩, hz, by simp [GaussianTranslation]⟩
  have root_ne : (DiamondTile K.1).cells.Nonempty := by
    refine ⟨0, (cell_mem _ _).mpr ?_⟩
    norm_num
    omega
  have subset (i : Fin 3) (s : Bool) : (S i s).cells ⊆ (DiamondTile K.1).cells := by
    intro z hz
    exact (hunion z).mpr ⟨i, s, hz⟩
  have positive (i : Fin 3) (s : Bool)
      (hU : LatticeTile (S i s))
      (hC : LatticeTile (TileCellComplement (DiamondTile K.1) (S i s)))
      (hcommon : (FootprintEdges (TileCellComplement (DiamondTile K.1) (S i s)) ∩
        FootprintEdges (S i s)).Nonempty) :
      LatticeTile (TileCellComplement (DiamondTile K.1) (S i s)) ∧
        TileTouching (TileCellComplement (DiamondTile K.1) (S i s)) (S i s) := by
    let C := TileCellComplement (DiamondTile K.1) (S i s)
    have hdisjoint : Disjoint C.cells (S i s).cells := by
      apply Finset.disjoint_left.mpr
      intro z hz hzS
      exact (Finset.mem_sdiff.mp hz).2 hzS
    have hwhole (z : LatticeCell) : z ∈ (DiamondTile K.1).cells ↔
        z ∈ C.cells ∨ z ∈ (S i s).cells := by
      change z ∈ (DiamondTile K.1).cells ↔
        z ∈ (DiamondTile K.1).cells \ (S i s).cells ∨ z ∈ (S i s).cells
      rw [Finset.mem_sdiff]
      constructor
      · tauto
      · rintro (⟨hz, _⟩ | hz)
        · exact hz
        · exact subset i s hz
    obtain ⟨_, ⟨x, y, p, hp, hp2, _, _, hv, hadj, he⟩, heq, hveq⟩ :=
      LatticeTileDiskUnionInterface C (S i s) (DiamondTile K.1)
        hC hU hgeometry.1 hdisjoint hwhole hcommon
    refine ⟨hC, Or.inl ⟨(LatticeTileFourNeighborConnected C hC).1,
      (LatticeTileFourNeighborConnected (S i s) hU).1, hdisjoint, ?_⟩⟩
    rw [hveq, ← heq]
    exact ⟨p, hp, hp2, hv, hadj, he⟩
  have unit_case (i : Fin 3) (s : Bool) (x : GaussianInt)
      (hshape : (S i s).cells = {x})
      (hx : (x.re = -(K.1 : Int) ∨ x.re = (K.1 : Int) - 1) ∧
        (x.im = (K.1 : Int) - 1 ∨ x.im = (K.1 : Int))) :
      LatticeTile (TileCellComplement (DiamondTile K.1) (S i s)) ∧
        TileTouching (TileCellComplement (DiamondTile K.1) (S i s)) (S i s) := by
    have hU : LatticeTile (S i s) := by
      have hd := P3092T1CenteredRectangleDisk {0} (by simp)
        ((x.re : Real) + 1 / 2, (x.im : Real) + 1 / 2)
        (fun _ => (1 / 2 : Real)) (fun _ => (1 / 2 : Real))
        (by intro j hj; norm_num) (by intro j hj; norm_num)
      norm_num [LatticeTile, TileRealization, hshape, ClosedSquareRealization,
        add_assoc] at hd ⊢
      exact hd
    have hC := P5116T1UnitDeletionDisk K.1 hk x hx
      (TileCellComplement (DiamondTile K.1) (S i s)) (by
        change (DiamondTile K.1).cells \ (S i s).cells = _
        rw [hshape])
    apply positive i s hU hC
    rcases hx.1 with hleft | hright
    · have hn : x + 1 ∈ (TileCellComplement (DiamondTile K.1) (S i s)).cells := by
        change x + 1 ∈ (DiamondTile K.1).cells \ (S i s).cells
        rw [Finset.mem_sdiff, hshape, Finset.mem_singleton, cell_mem]
        simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one,
          Zsqrtd.ext_iff] at *
        rcases hx.2 with h | h <;> omega
      refine ⟨{x + 1, x + 1 + ⟨0, 1⟩}, ?_, ?_⟩
      · exact ⟨x + 1, hn, Or.inr (Or.inl rfl)⟩
      · exact ⟨x, by simp [hshape], Or.inr (Or.inr (Or.inl rfl))⟩
    · have hn : x - 1 ∈ (TileCellComplement (DiamondTile K.1) (S i s)).cells := by
        change x - 1 ∈ (DiamondTile K.1).cells \ (S i s).cells
        rw [Finset.mem_sdiff, hshape, Finset.mem_singleton, cell_mem]
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one,
          Zsqrtd.ext_iff] at *
        rcases hx.2 with h | h <;> omega
      refine ⟨{x, x + ⟨0, 1⟩}, ?_, ?_⟩
      · refine ⟨x - 1, hn, Or.inr (Or.inr (Or.inl ?_))⟩
        simp
      · exact ⟨x, by simp [hshape], Or.inr (Or.inl rfl)⟩
  refine ⟨hgeometry.1, harea, ?_⟩
  intro i s
  fin_cases i
  · cases s
    · apply unit_case 0 false ⟨(K.1 : Int) - 1, (K.1 : Int)⟩
        ((identify 0 false).1.trans (congrArg ProtoTile.cells h01))
      exact ⟨Or.inr rfl, Or.inr rfl⟩
    · apply unit_case 0 true ⟨-(K.1 : Int), (K.1 : Int) - 1⟩
        ((identify 0 true).1.trans (congrArg ProtoTile.cells h00))
      exact ⟨Or.inl rfl, Or.inl rfl⟩
  · cases s
    · apply unit_case 1 false ⟨-(K.1 : Int), (K.1 : Int)⟩
        ((identify 1 false).1.trans (congrArg ProtoTile.cells h11))
      exact ⟨Or.inl rfl, Or.inr rfl⟩
    · apply unit_case 1 true ⟨(K.1 : Int) - 1, (K.1 : Int) - 1⟩
        ((identify 1 true).1.trans (congrArg ProtoTile.cells h10))
      exact ⟨Or.inr rfl, Or.inl rfl⟩
  · change LatticeTile (TileCellComplement (DiamondTile K.1) (S 2 s)) ∧
      TileTouching (TileCellComplement (DiamondTile K.1) (S 2 s)) (S 2 s)
    have hshape : (S 2 s).cells =
        (if s then TileTranslation (DiamondTile (K.1 - 1)) ⟨0, 2⟩
          else DiamondTile (K.1 - 1)).cells := by
      rw [(identify 2 s).1]
      cases s
      · exact congrArg ProtoTile.cells h20
      · exact congrArg ProtoTile.cells h21
    by_cases hp : 1 < K.1
    · have hU : LatticeTile (S 2 s) := by
        unfold LatticeTile TileRealization
        rw [hshape]
        have hprev := (DiamondTileGeometry (K.1 - 1) (by omega)).1
        cases s
        · exact hprev
        · exact (TileDiskAreaCovariance (DiamondTile (K.1 - 1)) ⟨0, 2⟩).1.mp hprev
      have hC := P5116T1PredecessorDeletionDisk K.1 hp s
        (TileCellComplement (DiamondTile K.1) (S 2 s)) (by
          change (DiamondTile K.1).cells \ (S 2 s).cells = _
          rw [hshape])
      apply positive 2 s hU hC
      let z : GaussianInt := ⟨0, if s then 2 else 2 * (K.1 : Int) - 2⟩
      have hzout : (if s then z - ⟨0, 1⟩ else z) ∈
          (TileCellComplement (DiamondTile K.1) (S 2 s)).cells := by
        change (if s then z - ⟨0, 1⟩ else z) ∈
          (DiamondTile K.1).cells \ (S 2 s).cells
        rw [Finset.mem_sdiff, hshape]
        cases s <;> simp only [Bool.false_eq_true, ↓reduceIte,
          cell_mem, translated_mem, Zsqrtd.re_sub, Zsqrtd.im_sub] <;>
          norm_num [z] <;> omega
      have hzin : (if s then z else z - ⟨0, 1⟩) ∈ (S 2 s).cells := by
        rw [hshape]
        cases s <;> simp only [Bool.false_eq_true, ↓reduceIte,
          cell_mem, translated_mem, Zsqrtd.re_sub, Zsqrtd.im_sub] <;>
          norm_num [z] <;> omega
      refine ⟨{z, z + 1}, ?_, ?_⟩
      · cases s
        · exact ⟨z, hzout, Or.inl rfl⟩
        · refine ⟨z - ⟨0, 1⟩, hzout, Or.inr (Or.inr (Or.inr ?_))⟩
          congr 1
      · cases s
        · refine ⟨z - ⟨0, 1⟩, hzin, Or.inr (Or.inr (Or.inr ?_))⟩
          congr 1 <;> abel
        · exact ⟨z, hzin, Or.inl rfl⟩
    · have hk1 : K.1 = 1 := by omega
      have hempty : (S 2 s).cells = ∅ := by
        rw [hshape, hk1]
        cases s <;> simp [DiamondTile, DiamondCellDomain, TileTranslation]
      have hcomp : TileCellComplement (DiamondTile K.1) (S 2 s) = DiamondTile K.1 := by
        cases ht : DiamondTile K.1
        simp [TileCellComplement, hempty]
      have hanchor : (S 2 s).anchor = (⟨0, if s then 2 else 0⟩ : GaussianInt) := by
        rw [(identify 2 s).2 hempty]
        cases s
        · rw [h20, hk1]
          rfl
        · rw [h21, hk1]
          rfl
      have hb : (S 2 s).anchor ∈ BoundaryFootprintVertices (DiamondTile K.1) := by
        rw [hanchor, BoundaryFootprintVertices, ite_eq_left root_ne]
        let z : GaussianInt := ⟨0, if s then 2 else 0⟩
        refine ⟨{z, z + 1}, ⟨z, Or.inl ⟨rfl, ?_⟩⟩, by simp [z]⟩
        cases s
        · apply Or.inl
          constructor <;> rw [cell_mem] <;> norm_num [z, hk1]
        · apply Or.inr
          constructor <;> rw [cell_mem] <;> norm_num [z, hk1]
      rw [hcomp]
      exact ⟨hgeometry.1, Or.inr (Or.inr ⟨hempty, hb⟩)⟩

end ApollonianSuperharmonic

end
