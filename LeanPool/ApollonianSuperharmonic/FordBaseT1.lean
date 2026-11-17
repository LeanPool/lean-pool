/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence
public import LeanPool.ApollonianSuperharmonic.FordRecursiveQuadruple
public import LeanPool.ApollonianSuperharmonic.FordTileGeometry
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.TileCellComplement
public import LeanPool.ApollonianSuperharmonic.TileTouching
public import LeanPool.ApollonianSuperharmonic.FordTileRecursiveIdentification
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.P5104T1CornerDeletionDisk
public import LeanPool.ApollonianSuperharmonic.LatticeTileDiskUnionInterface
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance

-- [TABLET NODE: FordBaseT1]

/-!
# FordBaseT1

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FordBaseT1 (P : FordFareyParameter) (hq : 1 < P.q)
    (S : Fin 3 → Bool → ProtoTile)
    (hS : ∀ i s, BandSubtileOccurrence (FordRecursiveQuadruple P)
      (FordTile P.q) i s (S i s))
    (hunion : ∀ x, x ∈ (FordTile P.q).cells ↔
      ∃ i s, x ∈ (S i s).cells) :
    LatticeTile (FordTile P.q) ∧
      TileArea (FordTile P.q) = Int.toNat ((FordRecursiveQuadruple P) 0).1 ∧
      ∀ i s, LatticeTile (TileCellComplement (FordTile P.q) (S i s)) ∧
        TileTouching (TileCellComplement (FordTile P.q) (S i s)) (S i s) := by
-- BODY
  classical
  have hr : 0 < P.q₁ := by
    by_contra hz
    have hz' : P.q₁ = 0 := by omega
    have hd := P.det₁
    simp [hz'] at hd
    have hdv : (P.q : Int) ∣ 1 := ⟨P.p₁, by simpa [mul_comm] using hd.symm⟩
    have hqone := Int.eq_one_of_dvd_one (by omega : 0 ≤ (P.q : Int)) hdv
    omega
  have hs := P.q₂_pos
  have hsum : (P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int) := by
    exact_mod_cast P.sum_q
  have hrq : (P.q₁ : Int) < (P.q : Int) := by omega
  have hsq : (P.q₂ : Int) < (P.q : Int) := by omega
  have hgeometry := FordTileGeometry P.q P.q_pos
  have harea : TileArea (FordTile P.q) =
      Int.toNat ((FordRecursiveQuadruple P) 0).1 := by
    change TileArea (FordTile P.q) = Int.toNat ((P.q * P.q : Nat) : Int)
    rw [Int.toNat_natCast]
    exact hgeometry.2
  obtain ⟨_, _, hrecursive⟩ := FordTileRecursiveIdentification P
  obtain ⟨_, R, hR, _, h00, h01, h10, h11, h20, ha20, h21, ha21⟩ := hrecursive hq
  have identify (i : Fin 3) (s : Bool) :
      (S i s).cells = (R i s).cells ∧
      ((S i s).cells = ∅ → (S i s).anchor = (R i s).anchor) := by
    apply BandPrototileCentroidUnique _ _ _ (hS i s).1 (hR i s).1
    have he := (hS i s).2.2.trans (hR i s).2.2.symm
    exact sub_left_inj.mp he
  have square_mem (r : Nat) (z : GaussianInt) := (P4210T1FordCellRectangles r z).1
  have translated_mem (r : Nat) (u z : GaussianInt) :
      z ∈ (TileTranslation (FordTile r) u).cells ↔
        0 ≤ z.re - u.re ∧ z.re - u.re < (r : Int) ∧
        0 ≤ z.im - u.im ∧ z.im - u.im < (r : Int) := by
    have hm : z ∈ (TileTranslation (FordTile r) u).cells ↔
        z - u ∈ (FordTile r).cells := by
      change z ∈ (FordTile r).cells.image (GaussianTranslation u) ↔ _
      constructor
      · rintro hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
        simpa [GaussianTranslation] using hy
      · intro hz
        exact Finset.mem_image.mpr ⟨z - u, hz, by simp [GaussianTranslation]⟩
    simpa only [Zsqrtd.re_sub, Zsqrtd.im_sub] using hm.trans (square_mem r (z - u))
  have root_ne : (FordTile P.q).cells.Nonempty := by
    refine ⟨0, (square_mem _ _).mpr ?_⟩
    simp only [Zsqrtd.re_zero, Zsqrtd.im_zero]
    omega
  have subset (i : Fin 3) (s : Bool) : (S i s).cells ⊆ (FordTile P.q).cells := by
    intro z hz
    exact (hunion z).mpr ⟨i, s, hz⟩
  have positive (i : Fin 3) (s : Bool) (r : Nat) (u : GaussianInt)
      (hr : 0 < r) (hshape : (S i s).cells = (TileTranslation (FordTile r) u).cells)
      (a b : Int) (ha : 0 < a) (haq : a < (P.q : Int))
      (hb : 0 < b) (hbq : b < (P.q : Int)) (left bottom : Bool)
      (hcut : ∀ z : GaussianInt, z ∈ (S i s).cells ↔
        (0 ≤ z.re ∧ z.re < (P.q : Int) ∧ 0 ≤ z.im ∧ z.im < (P.q : Int)) ∧
          ((if left then z.re < a else a ≤ z.re) ∧
            (if bottom then z.im < b else b ≤ z.im))) :
      LatticeTile (TileCellComplement (FordTile P.q) (S i s)) ∧
        TileTouching (TileCellComplement (FordTile P.q) (S i s)) (S i s) := by
    let C := TileCellComplement (FordTile P.q) (S i s)
    have hCmem (z : GaussianInt) : z ∈ C.cells ↔
        (0 ≤ z.re ∧ z.re < (P.q : Int) ∧ 0 ≤ z.im ∧ z.im < (P.q : Int)) ∧
          ¬ ((if left then z.re < a else a ≤ z.re) ∧
            (if bottom then z.im < b else b ≤ z.im)) := by
      change z ∈ (FordTile P.q).cells \ (S i s).cells ↔ _
      rw [Finset.mem_sdiff, square_mem, hcut]
      tauto
    have hC : LatticeTile C :=
      P5104T1CornerDeletionDisk C P.q a b ha haq hb hbq left bottom hCmem
    have hU : LatticeTile (S i s) := by
      unfold LatticeTile TileRealization
      rw [hshape]
      exact (TileDiskAreaCovariance (FordTile r) u).1.mp (FordTileGeometry r hr).1
    have hdisjoint : Disjoint C.cells (S i s).cells := by
      apply Finset.disjoint_left.mpr
      intro z hz hzS
      exact (Finset.mem_sdiff.mp hz).2 hzS
    have hwhole (z : LatticeCell) : z ∈ (FordTile P.q).cells ↔
        z ∈ C.cells ∨ z ∈ (S i s).cells := by
      change z ∈ (FordTile P.q).cells ↔
        z ∈ (FordTile P.q).cells \ (S i s).cells ∨ z ∈ (S i s).cells
      rw [Finset.mem_sdiff]
      have := subset i s
      constructor
      · tauto
      · rintro (⟨hz, _⟩ | hz)
        · exact hz
        · exact this hz
    let m : GaussianInt := ⟨a, if bottom then 0 else (P.q : Int) - 1⟩
    have hedge_left (V : ProtoTile) (hv : m - 1 ∈ V.cells) :
        ({m, m + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges V := by
      refine ⟨m - 1, hv, Or.inr (Or.inr (Or.inl ?_))⟩
      simp
    have hedge_right (V : ProtoTile) (hv : m ∈ V.cells) :
        ({m, m + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges V :=
      ⟨m, hv, Or.inr (Or.inl rfl)⟩
    have hcommon : (FootprintEdges C ∩ FootprintEdges (S i s)).Nonempty := by
      refine ⟨{m, m + ⟨0, 1⟩}, ?_⟩
      cases left
      · have hcm : m - 1 ∈ C.cells := by
          rw [hCmem]
          cases bottom <;> simp [m] <;> omega
        have hum : m ∈ (S i s).cells := by
          rw [hcut]
          cases bottom <;> simp [m] <;> omega
        exact ⟨hedge_left C hcm, hedge_right (S i s) hum⟩
      · have hcm : m ∈ C.cells := by
          rw [hCmem]
          cases bottom <;> simp [m] <;> omega
        have hum : m - 1 ∈ (S i s).cells := by
          rw [hcut]
          cases bottom <;> simp [m] <;> omega
        exact ⟨hedge_right C hcm, hedge_left (S i s) hum⟩
    obtain ⟨_, ⟨x, y, p, hp, hp2, _, _, hv, hadj, he⟩, heq, hveq⟩ :=
      LatticeTileDiskUnionInterface C (S i s) (FordTile P.q)
        hC hU hgeometry.1 hdisjoint hwhole hcommon
    refine ⟨hC, Or.inl ⟨(LatticeTileFourNeighborConnected C hC).1,
      (LatticeTileFourNeighborConnected (S i s) hU).1, hdisjoint, ?_⟩⟩
    rw [hveq, ← heq]
    exact ⟨p, hp, hp2, hv, hadj, he⟩
  have empty_case (s : Bool) (hempty : (S 2 s).cells = ∅)
      (hanchor : (S 2 s).anchor ∈ BoundaryFootprintVertices (FordTile P.q)) :
      LatticeTile (TileCellComplement (FordTile P.q) (S 2 s)) ∧
        TileTouching (TileCellComplement (FordTile P.q) (S 2 s)) (S 2 s) := by
    have hcomp : TileCellComplement (FordTile P.q) (S 2 s) = FordTile P.q := by
      cases htile : FordTile P.q
      simp [TileCellComplement, hempty]
    rw [hcomp]
    exact ⟨hgeometry.1, Or.inr (Or.inr ⟨hempty, hanchor⟩)⟩
  refine ⟨hgeometry.1, harea, ?_⟩
  intro i s
  fin_cases i
  · cases s
    · apply positive 0 false P.q₁ ⟨(P.q₂ : Int), (P.q₂ : Int)⟩ hr
        ((identify 0 false).1.trans h01) P.q₂ P.q₂ (by omega) hsq (by omega) hsq
        false false
      intro z
      rw [(identify 0 false).1, h01, translated_mem]
      dsimp
      omega
    · apply positive 0 true P.q₁ 0 hr (by
        rw [(identify 0 true).1, h00]
        change (FordTile P.q₁).cells = (FordTile P.q₁).cells.image (GaussianTranslation 0)
        rw [show GaussianTranslation 0 = id by funext z; simp [GaussianTranslation]]
        simp)
        P.q₁ P.q₁ (by omega) hrq (by omega) hrq true true
      intro z
      rw [(identify 0 true).1, h00, square_mem]
      dsimp
      omega
  · cases s
    · apply positive 1 false P.q₂ ⟨0, (P.q₁ : Int)⟩ hs
        ((identify 1 false).1.trans h11) P.q₂ P.q₁ (by omega) hsq (by omega) hrq
        true false
      intro z
      rw [(identify 1 false).1, h11, translated_mem]
      dsimp
      omega
    · apply positive 1 true P.q₂ ⟨(P.q₁ : Int), 0⟩ hs
        ((identify 1 true).1.trans h10) P.q₁ P.q₂ (by omega) hrq (by omega) hsq
        false true
      intro z
      rw [(identify 1 true).1, h10, translated_mem]
      dsimp
      omega
  · have htop : (⟨(P.q₂ : Int), (P.q : Int)⟩ : GaussianInt) ∈
        BoundaryFootprintVertices (FordTile P.q) := by
      let z : GaussianInt := ⟨(P.q₂ : Int), (P.q : Int)⟩
      have hout : z ∉ (FordTile P.q).cells := by rw [square_mem]; simp [z]
      have hin : z - ⟨0, 1⟩ ∈ (FordTile P.q).cells := by
        rw [square_mem]
        simp [z]
        omega
      rw [BoundaryFootprintVertices, ite_eq_left root_ne]
      exact ⟨{z, z + 1}, ⟨z, Or.inl ⟨rfl, Or.inr ⟨hout, hin⟩⟩⟩, by simp [z]⟩
    have hbottom : (⟨(P.q₁ : Int), 0⟩ : GaussianInt) ∈
        BoundaryFootprintVertices (FordTile P.q) := by
      let z : GaussianInt := ⟨(P.q₁ : Int), 0⟩
      have hin : z ∈ (FordTile P.q).cells := by rw [square_mem]; simp [z]; omega
      have hout : z - ⟨0, 1⟩ ∉ (FordTile P.q).cells := by rw [square_mem]; simp [z]
      rw [BoundaryFootprintVertices, ite_eq_left root_ne]
      exact ⟨{z, z + 1}, ⟨z, Or.inl ⟨rfl, Or.inl ⟨hin, hout⟩⟩⟩, by simp [z]⟩
    cases s
    · have he : (S 2 false).cells = ∅ := (identify 2 false).1.trans h21
      apply empty_case false he
      rw [(identify 2 false).2 he, ha21]
      exact hbottom
    · have he : (S 2 true).cells = ∅ := (identify 2 true).1.trans h20
      apply empty_case true he
      rw [(identify 2 true).2 he, ha20]
      exact htop

end ApollonianSuperharmonic

end
