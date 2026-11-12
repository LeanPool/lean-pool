/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5682T1AlignedSquareRawInterfaces
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple

-- [TABLET NODE: P5327T1RightSquareJunctions]

/-!
# P5327T1RightSquareJunctions

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5327T1RightSquareJunctions (r t : Nat) (hr : 0 < r) (ht : 0 < t)
    (j : Fin 4) :
    let q := r + t
    let A := TileTranslation (FordTile q) 0
    let B := TileTranslation (FordTile q)
      (![⟨-(r : Int), q⟩, ⟨-(r : Int), q⟩,
        ⟨-(t : Int), -(q : Int)⟩, ⟨-(t : Int), -(q : Int)⟩] j)
    let C := TileTranslation (FordTile (![r, r, t, t] j))
      (![⟨t, q⟩, ⟨-(r : Int), t⟩, ⟨-(t : Int), 0⟩,
        ⟨r, -(t : Int)⟩] j)
    ∃ E : ExactTileInterfaceTriple A B C,
      E.point = (![⟨t, q⟩, ⟨0, q⟩, ⟨0, 0⟩, ⟨r, 0⟩] j) ∧
      E.otherAB = (![⟨0, q⟩, ⟨t, q⟩, ⟨r, 0⟩, ⟨0, 0⟩] j) ∧
      E.otherBC = (![⟨t, q+r⟩, ⟨-(r : Int), q⟩,
        ⟨-(t : Int), 0⟩, ⟨r, -(t : Int)⟩] j) ∧
      E.otherCA = (![⟨q, q⟩, ⟨0, t⟩, ⟨0, t⟩, ⟨q, 0⟩] j) := by
-- BODY
  classical
  let sq := fun (n : Nat) (a : GaussianInt) => TileTranslation (FordTile n) a
  obtain ⟨vertex, contact⟩ := P5682T1AlignedSquareRawInterfaces
  change ∀ (n : Nat) (_ : 0 < n) (a z : GaussianInt),
    z ∈ FootprintVertices (sq n a) ↔
      a.re ≤ z.re ∧ z.re ≤ a.re + n ∧ a.im ≤ z.im ∧ z.im ≤ a.im + n at vertex
  have hq : 0 < r+t := by omega
  dsimp only
  simp only [Nat.cast_add]
  fin_cases j
  · obtain ⟨_, ab, ba⟩ := contact (r+t) (r+t) hq hq 0 ⟨-(r:Int),r+t⟩ false
      (by simp) (by dsimp; omega)
    obtain ⟨_, bc, cb⟩ := contact (r+t) r hq hr ⟨-(r:Int),r+t⟩ ⟨t,r+t⟩ true
      (by dsimp; omega) (by dsimp; omega)
    obtain ⟨_, ac, ca⟩ := contact (r+t) r hq hr 0 ⟨t,r+t⟩ false
      (by simp) (by dsimp; omega)
    simp only [Bool.false_eq_true,ite_false,ite_true,Zsqrtd.re_zero,Zsqrtd.im_zero,
      Nat.cast_add] at ab ba bc cb ac ca
    let E : ExactTileInterfaceTriple (sq (r+t) 0) (sq (r+t) ⟨-(r:Int),r+t⟩)
        (sq r ⟨t,r+t⟩) :=
      { point := ⟨t,r+t⟩
        otherAB := ⟨0,r+t⟩
        otherBC := ⟨t,2*r+t⟩
        otherCA := ⟨r+t,r+t⟩
        pathAB := by convert ba using 1 <;> congr 1 <;> omega
        pathBC := by convert bc using 1 <;> congr 1 <;> omega
        pathCA := by simpa only [Set.inter_comm] using (by
          convert ac using 1 <;> congr 1; omega)
        unique_common := by
          intro z
          simp only [Set.mem_inter_iff, vertex _ hq, vertex _ hr, Zsqrtd.ext_iff]
          dsimp
          omega }
    exact ⟨E, rfl, rfl, by dsimp [E]; ext <;> dsimp; omega, rfl⟩
  · obtain ⟨_, ab, ba⟩ := contact (r+t) (r+t) hq hq 0 ⟨-(r:Int),r+t⟩ false
      (by simp) (by dsimp; omega)
    obtain ⟨_, cb, bc⟩ := contact r (r+t) hr hq ⟨-(r:Int),t⟩ ⟨-(r:Int),r+t⟩ false
      (by dsimp; omega) (by dsimp; omega)
    obtain ⟨_, ca, ac⟩ := contact r (r+t) hr hq ⟨-(r:Int),t⟩ 0 true
      (by dsimp; omega) (by dsimp; omega)
    simp only [Bool.false_eq_true,ite_false,ite_true,Zsqrtd.re_zero,Zsqrtd.im_zero,
      Nat.cast_add] at ab ba cb bc ca ac
    let E : ExactTileInterfaceTriple (sq (r+t) 0) (sq (r+t) ⟨-(r:Int),r+t⟩)
        (sq r ⟨-(r:Int),t⟩) :=
      { point := ⟨0,r+t⟩
        otherAB := ⟨t,r+t⟩
        otherBC := ⟨-(r:Int),r+t⟩
        otherCA := ⟨0,t⟩
        pathAB := by convert ab using 1 <;> congr 1 <;> omega
        pathBC := by simpa only [Set.inter_comm] using (by
          convert bc using 1 <;> congr 1 <;> omega)
        pathCA := by convert ac using 1 <;> congr 1 <;> omega
        unique_common := by
          intro z
          simp only [Set.mem_inter_iff, vertex _ hq, vertex _ hr, Zsqrtd.ext_iff]
          dsimp
          omega }
    exact ⟨E, rfl, rfl, rfl, rfl⟩
  · obtain ⟨_, ba, ab⟩ := contact (r+t) (r+t) hq hq ⟨-(t:Int),-(r+t:Int)⟩ 0 false
      (by dsimp; omega) (by dsimp; omega)
    obtain ⟨_, bc, cb⟩ := contact (r+t) t hq ht
      ⟨-(t:Int),-(r+t:Int)⟩ ⟨-(t:Int),0⟩ false
      (by dsimp; omega) (by dsimp; omega)
    obtain ⟨_, ca, ac⟩ := contact t (r+t) ht hq ⟨-(t:Int),0⟩ 0 true
      (by dsimp; omega) (by dsimp; omega)
    simp only [Bool.false_eq_true,ite_false,ite_true,Zsqrtd.re_zero,Zsqrtd.im_zero,
      Nat.cast_add] at ba ab bc cb ca ac
    let E : ExactTileInterfaceTriple (sq (r+t) 0) (sq (r+t) ⟨-(t:Int),-(r+t:Int)⟩)
        (sq t ⟨-(t:Int),0⟩) :=
      { point := ⟨0,0⟩
        otherAB := ⟨r,0⟩
        otherBC := ⟨-(t:Int),0⟩
        otherCA := ⟨0,t⟩
        pathAB := by
          convert ba using 1 <;> first | exact Set.inter_comm _ _ | (congr 1; omega)
        pathBC := by convert cb using 1 <;> congr 1 <;> omega
        pathCA := by convert ca using 1 <;> congr 1; omega
        unique_common := by
          intro z
          simp only [Set.mem_inter_iff, vertex _ hq, vertex _ ht, Zsqrtd.ext_iff]
          dsimp
          omega }
    exact ⟨E, rfl, rfl, rfl, rfl⟩
  · obtain ⟨_, ba, ab⟩ := contact (r+t) (r+t) hq hq ⟨-(t:Int),-(r+t:Int)⟩ 0 false
      (by dsimp; omega) (by dsimp; omega)
    obtain ⟨_, bc, cb⟩ := contact (r+t) t hq ht
      ⟨-(t:Int),-(r+t:Int)⟩ ⟨r,-(t:Int)⟩ true
      (by dsimp; omega) (by dsimp; omega)
    obtain ⟨_, ca, ac⟩ := contact t (r+t) ht hq ⟨r,-(t:Int)⟩ 0 false
      (by dsimp; omega) (by dsimp; omega)
    simp only [Bool.false_eq_true,ite_false,ite_true,Zsqrtd.re_zero,Zsqrtd.im_zero,
      Nat.cast_add] at ba ab bc cb ca ac
    let E : ExactTileInterfaceTriple (sq (r+t) 0) (sq (r+t) ⟨-(t:Int),-(r+t:Int)⟩)
        (sq t ⟨r,-(t:Int)⟩) :=
      { point := ⟨r,0⟩
        otherAB := ⟨0,0⟩
        otherBC := ⟨r,-(t:Int)⟩
        otherCA := ⟨r+t,0⟩
        pathAB := by
          convert ab using 1 <;> first | exact Set.inter_comm _ _ | (congr 1; omega)
        pathBC := by convert cb using 1 <;> congr 1 <;> omega
        pathCA := by convert ca using 1 <;> congr 1 <;> omega
        unique_common := by
          intro z
          simp only [Set.mem_inter_iff, vertex _ hq, vertex _ ht, Zsqrtd.ext_iff]
          dsimp
          omega }
    exact ⟨E, rfl, rfl, rfl, rfl⟩

end ApollonianSuperharmonic

end
