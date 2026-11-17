/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5682T1AlignedSquareRawInterfaces
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTripleLatticeTouching
public import LeanPool.ApollonianSuperharmonic.FordTileGeometry
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance

-- [TABLET NODE: P5269T1IncomingSquareJunctions]

/-!
# P5269T1IncomingSquareJunctions

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5269T1IncomingSquareJunctions (r s : Nat) (hr : 0 < r) (hs : 0 < s)
    (j : Fin 4) :
    let q := r + s
    let A := TileTranslation (FordTile q) 0
    let B := TileTranslation (FordTile q)
      (![⟨q, r⟩, ⟨-(q : Int), s⟩, ⟨-(q : Int), -(r : Int)⟩,
        ⟨q, -(s : Int)⟩] j)
    let C := TileTranslation (FordTile (![r, s, r, s] j))
      (![⟨s, q⟩, ⟨-(s : Int), 0⟩, ⟨-(r : Int), s⟩, ⟨r, -(s : Int)⟩] j)
    ∃ E : ExactTileInterfaceTriple A B C,
      E.point = (![⟨q, q⟩, ⟨0, s⟩, ⟨0, s⟩, ⟨q, 0⟩] j) ∧
        TouchingTriple A B C := by
-- BODY
  classical
  let sq := fun (n : Nat) (a : GaussianInt) => TileTranslation (FordTile n) a
  obtain ⟨vertex, contact⟩ := P5682T1AlignedSquareRawInterfaces
  change ∀ (n : Nat) (_ : 0 < n) (a z : GaussianInt),
    z ∈ FootprintVertices (sq n a) ↔
      a.re ≤ z.re ∧ z.re ≤ a.re + n ∧ a.im ≤ z.im ∧ z.im ≤ a.im + n at vertex
  have disk (n : Nat) (hn : 0 < n) (a : GaussianInt) : LatticeTile (sq n a) :=
    (TileDiskAreaCovariance (FordTile n) a).1.mp (FordTileGeometry n hn).1
  have hq : 0 < r+s := by omega
  dsimp only
  simp only [Nat.cast_add]
  fin_cases j
  · obtain ⟨hab, ab, abr⟩ := contact (r+s) (r+s) hq hq 0 ⟨r+s,r⟩ true
      (by simp) (by dsimp; omega)
    obtain ⟨hcb, cb, bc⟩ := contact r (r+s) hr hq ⟨s,r+s⟩ ⟨r+s,r⟩ true
      (by dsimp; omega) (by dsimp; omega)
    obtain ⟨hac, ac, ca⟩ := contact (r+s) r hq hr 0 ⟨s,r+s⟩ false
      (by simp) (by dsimp; omega)
    simp only [Bool.false_eq_true,ite_false,ite_true,Zsqrtd.re_zero,Zsqrtd.im_zero,
      Nat.cast_add] at ab abr cb bc ac ca
    let E : ExactTileInterfaceTriple (sq (r+s) 0) (sq (r+s) ⟨r+s,r⟩) (sq r ⟨s,r+s⟩) :=
      { point := ⟨r+s,r+s⟩
        otherAB := ⟨r+s,r⟩
        otherBC := ⟨r+s,2*r+s⟩
        otherCA := ⟨s,r+s⟩
        pathAB := by convert abr using 1 <;> congr 1; omega
        pathBC := by simpa only [Set.inter_comm] using (by
          convert cb using 1 <;> congr 1 <;> omega)
        pathCA := by simpa only [Set.inter_comm] using (by
          convert ca using 1 <;> congr 1; omega)
        unique_common := by
          intro z
          simp only [Set.mem_inter_iff, vertex _ hq, vertex _ hr, Zsqrtd.ext_iff]
          dsimp
          omega }
    exact ⟨E, rfl, ExactTileInterfaceTripleLatticeTouching _ _ _ E
      (disk _ hq _) (disk _ hq _) (disk _ hr _) hab hcb.symm hac.symm⟩
  · obtain ⟨hba, ba, ab⟩ := contact (r+s) (r+s) hq hq ⟨-(r+s:Int),s⟩ 0 true
      (by dsimp; omega) (by dsimp; omega)
    obtain ⟨hcb, cb, bc⟩ := contact s (r+s) hs hq ⟨-(s:Int),0⟩ ⟨-(r+s:Int),s⟩ false
      (by dsimp; omega) (by dsimp; omega)
    obtain ⟨hca, ca, ac⟩ := contact s (r+s) hs hq ⟨-(s:Int),0⟩ 0 true
      (by dsimp; omega) (by dsimp; omega)
    simp only [Bool.false_eq_true,ite_false,ite_true,Zsqrtd.re_zero,Zsqrtd.im_zero,
      Nat.cast_add] at ba ab cb bc ca ac
    let E : ExactTileInterfaceTriple (sq (r+s) 0) (sq (r+s) ⟨-(r+s:Int),s⟩) (sq s ⟨-(s:Int),0⟩) :=
      { point := ⟨0,s⟩
        otherAB := ⟨0,r+s⟩
        otherBC := ⟨-(s:Int),s⟩
        otherCA := ⟨0,0⟩
        pathAB := by
          convert ba using 1 <;> first | exact Set.inter_comm _ _ | (congr 1; omega)
        pathBC := by simpa only [Set.inter_comm] using (by
          convert bc using 1 <;> congr 1 <;> omega)
        pathCA := by convert ac using 1 <;> congr 1; omega
        unique_common := by
          intro z
          simp only [Set.mem_inter_iff, vertex _ hq, vertex _ hs, Zsqrtd.ext_iff]
          dsimp
          omega }
    exact ⟨E, rfl, ExactTileInterfaceTripleLatticeTouching _ _ _ E
      (disk _ hq _) (disk _ hq _) (disk _ hs _) hba.symm hcb.symm hca⟩
  · obtain ⟨hba, ba, ab⟩ := contact (r+s) (r+s) hq hq ⟨-(r+s:Int),-(r:Int)⟩ 0 true
      (by dsimp; omega) (by dsimp; omega)
    obtain ⟨hbc, bc, cb⟩ := contact (r+s) r hq hr ⟨-(r+s:Int),-(r:Int)⟩ ⟨-(r:Int),s⟩ false
      (by dsimp; omega) (by dsimp; omega)
    obtain ⟨hca, ca, ac⟩ := contact r (r+s) hr hq ⟨-(r:Int),s⟩ 0 true
      (by dsimp; omega) (by dsimp; omega)
    simp only [Bool.false_eq_true,ite_false,ite_true,Zsqrtd.re_zero,Zsqrtd.im_zero,
      Nat.cast_add] at ba ab bc cb ca ac
    let E : ExactTileInterfaceTriple (sq (r+s) 0) (sq (r+s) ⟨-(r+s:Int),-(r:Int)⟩) (sq r
        ⟨-(r:Int),s⟩) :=
      { point := ⟨0,s⟩
        otherAB := ⟨0,0⟩
        otherBC := ⟨-(r:Int),s⟩
        otherCA := ⟨0,r+s⟩
        pathAB := by
          convert ab using 1 <;> first | exact Set.inter_comm _ _ | (congr 1; omega)
        pathBC := by convert cb using 1 <;> congr 1 <;> omega
        pathCA := by convert ca using 1 <;> congr 1 <;> omega
        unique_common := by
          intro z
          simp only [Set.mem_inter_iff, vertex _ hq, vertex _ hr, Zsqrtd.ext_iff]
          dsimp
          omega }
    exact ⟨E, rfl, ExactTileInterfaceTripleLatticeTouching _ _ _ E
      (disk _ hq _) (disk _ hq _) (disk _ hr _) hba.symm hbc hca⟩
  · obtain ⟨hab, ab, ba⟩ := contact (r+s) (r+s) hq hq 0 ⟨r+s,-(s:Int)⟩ true
      (by simp) (by dsimp; omega)
    obtain ⟨hcb, cb, bc⟩ := contact s (r+s) hs hq ⟨r,-(s:Int)⟩ ⟨r+s,-(s:Int)⟩ true
      (by dsimp ) (by dsimp; omega)
    obtain ⟨hca, ca, ac⟩ := contact s (r+s) hs hq ⟨r,-(s:Int)⟩ 0 false
      (by dsimp; omega) (by dsimp; omega)
    simp only [Bool.false_eq_true,ite_false,ite_true,Zsqrtd.re_zero,Zsqrtd.im_zero,
      Nat.cast_add] at ab ba cb bc ca ac
    let E : ExactTileInterfaceTriple (sq (r+s) 0) (sq (r+s) ⟨r+s,-(s:Int)⟩) (sq s ⟨r,-(s:Int)⟩) :=
      { point := ⟨r+s,0⟩
        otherAB := ⟨r+s,r⟩
        otherBC := ⟨r+s,-(s:Int)⟩
        otherCA := ⟨r,0⟩
        pathAB := by convert ab using 1 <;> congr 1 <;> omega
        pathBC := by simpa only [Set.inter_comm] using (by
          convert bc using 1 <;> congr 1 <;> omega)
        pathCA := by convert ac using 1 <;> congr 1 <;> omega
        unique_common := by
          intro z
          simp only [Set.mem_inter_iff, vertex _ hq, vertex _ hs, Zsqrtd.ext_iff]
          dsimp
          omega }
    exact ⟨E, rfl, ExactTileInterfaceTripleLatticeTouching _ _ _ E
      (disk _ hq _) (disk _ hq _) (disk _ hs _) hab hcb.symm hca⟩

end ApollonianSuperharmonic

end
