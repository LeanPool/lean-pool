/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.TileArea
public import LeanPool.ApollonianSuperharmonic.P3092T1DiamondCenteredRectangles
public import LeanPool.ApollonianSuperharmonic.P3092T1CenteredRectangleDisk

-- [TABLET NODE: DiamondTileGeometry]

/-!
# DiamondTileGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem DiamondTileGeometry (k : Nat) (hk : 0 < k) :
    LatticeTile (DiamondTile k) ∧
      TileArea (DiamondTile k) = 2 * k * (k + 1) := by
-- BODY
  constructor
  · change TopologicalDisk (TileRealization (DiamondTile k))
    rw [P3092T1DiamondCenteredRectangles k hk]
    have hJ : (Finset.Icc 1 k).Nonempty :=
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hk⟩⟩
    have ha : ∀ j ∈ Finset.Icc 1 k, 0 < (j : Real) := by
      intro j hj
      exact_mod_cast (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hj).1)
    have hb : ∀ j ∈ Finset.Icc 1 k, 0 < (k : Real) - (j : Real) + 1 := by
      intro j hj
      have hjk : (j : Real) ≤ (k : Real) := by
        exact_mod_cast (Finset.mem_Icc.mp hj).2
      linarith
    have hdisk := P3092T1CenteredRectangleDisk (Finset.Icc 1 k) hJ
      (0, (k : Real)) (fun j => (j : Real))
      (fun j => (k : Real) - (j : Real) + 1) ha hb
    have hrect (j : Nat) :
        Set.Icc (0 - (j : Real), (k : Real) - ((k : Real) - (j : Real) + 1))
          (0 + (j : Real), (k : Real) + ((k : Real) - (j : Real) + 1)) =
        Set.Icc (-(j : Real), (j : Real) - 1)
          ((j : Real), 2 * (k : Real) - (j : Real) + 1) := by
      congr 1 <;> ext <;> simp <;> ring
    simpa only [hrect] using hdisk
  · change (DiamondCellDomain k).card = 2 * k * (k + 1)
    classical
    let r : Nat → Nat := fun y => min (y + 1) (2 * k - y)
    let row : Nat → Finset GaussianInt := fun y =>
      (Finset.range (2 * r y)).image fun j : Nat =>
        (⟨(j : Int) - (r y : Int), (y : Int)⟩ : GaussianInt)
    have hinj (y : Nat) : Function.Injective
        (fun j : Nat => (⟨(j : Int) - (r y : Int), (y : Int)⟩ : GaussianInt)) := by
      intro i j h
      have hre := congrArg Zsqrtd.re h
      simp only at hre
      omega
    have hcard (y : Nat) : (row y).card = 2 * r y := by
      dsimp [row]
      rw [Finset.card_image_of_injective _ (hinj y), Finset.card_range]
    have hdisj : (↑(Finset.range (2 * k)) : Set Nat).PairwiseDisjoint row := by
      intro y hy z hz hyz
      apply Finset.disjoint_left.mpr
      intro x hxy hxz
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hxy
      obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hxz
      have him := congrArg Zsqrtd.im (hix.trans hjx.symm)
      simp only at him
      exact hyz (by omega)
    have hsum : (DiamondCellDomain k).card =
        ∑ y ∈ Finset.range (2 * k), 2 * r y := by
      change ((Finset.range (2 * k)).biUnion row).card = _
      rw [Finset.card_biUnion hdisj]
      exact Finset.sum_congr rfl (fun y hy => hcard y)
    have hfirst (y : Nat) (hy : y < k) : r y = y + 1 := by
      dsimp [r]
      apply Nat.min_eq_left
      omega
    have hlast (y : Nat) (hy : y < k) : r (k + y) = k - y := by
      dsimp [r]
      rw [Nat.min_eq_right (by omega)]
      omega
    have htriangle : ∀ n : Nat,
        ∑ y ∈ Finset.range n, 2 * (y + 1) = n * (n + 1) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    rw [hsum, show 2 * k = k + k by omega, Finset.sum_range_add]
    have hs1 : (∑ y ∈ Finset.range k, 2 * r y) = k * (k + 1) := by
      rw [← htriangle k]
      apply Finset.sum_congr rfl
      intro y hy
      rw [hfirst y (Finset.mem_range.mp hy)]
    have hs2 : (∑ y ∈ Finset.range k, 2 * r (k + y)) = k * (k + 1) := by
      calc
        _ = ∑ y ∈ Finset.range k, 2 * (k - y) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hlast y (Finset.mem_range.mp hy)]
        _ = ∑ y ∈ Finset.range k, 2 * (y + 1) := by
          rw [← Finset.sum_range_reflect (fun y => 2 * (y + 1)) k]
          apply Finset.sum_congr rfl
          intro y hy
          have hyk := Finset.mem_range.mp hy
          congr 1
          omega
        _ = k * (k + 1) := htriangle k
    rw [hs1, hs2]
    ring

end ApollonianSuperharmonic

end
