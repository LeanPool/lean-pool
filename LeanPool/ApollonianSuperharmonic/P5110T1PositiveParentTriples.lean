/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5110T1ParentModel
public import LeanPool.ApollonianSuperharmonic.P5110T1SquareInterface
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: P5110T1PositiveParentTriples]

/-!
# P5110T1PositiveParentTriples

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5110T1PositiveParentTriples (r s : Nat) (hr : 0 < r) (hs : 0 < s) :
    let q := r + s
    let A := FordTile q
    TouchingTriple A (TileTranslation A ⟨(q : Int), (r : Int)⟩)
        (P5110T1ParentModel r s 0 true) ∧
    TouchingTriple A (TileTranslation A ⟨-(q : Int), (s : Int)⟩)
        (P5110T1ParentModel r s 1 true) ∧
    TouchingTriple A (P5110T1ParentModel r s 0 true)
        (P5110T1ParentModel r s 1 false) := by
-- BODY
  have qpos : 0 < r + s := by omega
  have zero_shift : TileTranslation (FordTile (r + s)) 0 = FordTile (r + s) := by
    have h : GaussianTranslation 0 = id := by funext z; simp [GaussianTranslation]
    simp [TileTranslation, h]
  have swap (A B : ProtoTile) (h : TileTouching A B) : TileTouching B A := by
    rcases h with h | h | h
    · exact Or.inl ⟨h.2.1, h.1, h.2.2.1.symm, by simpa [Set.inter_comm] using h.2.2.2⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  let q := r + s
  let A := FordTile q
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · let B := TileTranslation A ⟨(q : Int), (r : Int)⟩
    let C := TileTranslation (FordTile r) ⟨(s : Int), (q : Int)⟩
    change TouchingTriple A B C
    rcases P5110T1SquareInterface q q qpos qpos
        0 ⟨(q : Int), (r : Int)⟩ true (by simp)
        (by dsimp [q]; omega) with ⟨na, nb, dab, vab, _, _, _, _, pab⟩
    rcases P5110T1SquareInterface r q hr qpos
        ⟨(s : Int), (q : Int)⟩ ⟨(q : Int), (r : Int)⟩ true
        (by dsimp [q]; omega) (by dsimp [q]; omega)
        with ⟨nc, _, dcb, vcb, _, _, _, _, pcb⟩
    rcases P5110T1SquareInterface q r qpos hr
        0 ⟨(s : Int), (q : Int)⟩ false (by simp)
        (by dsimp [q]; omega) with ⟨_, _, dac, vac, _, _, _, _, pac⟩
    rw [zero_shift] at na dab vab pab dac vac pac
    refine ⟨Or.inl ⟨na, nb, dab, pab⟩,
      swap _ _ (Or.inl ⟨nc, nb, dcb, pcb⟩),
      swap _ _ (Or.inl ⟨na, nc, dac, pac⟩), ⟨(q : Int), (q : Int)⟩, ?_, ?_⟩
    · have hab : (⟨(q : Int), (q : Int)⟩ : GaussianInt) ∈
          BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B := by
        rw [vab]; dsimp [q]; omega
      have hcb : (⟨(q : Int), (q : Int)⟩ : GaussianInt) ∈
          BoundaryFootprintVertices C ∩ BoundaryFootprintVertices B := by
        rw [vcb]; dsimp [q]; omega
      exact ⟨hab.1, hab.2, hcb.1⟩
    · intro z hz
      have hab : z ∈ BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B :=
        ⟨hz.1, hz.2.1⟩
      have hcb : z ∈ BoundaryFootprintVertices C ∩ BoundaryFootprintVertices B :=
        ⟨hz.2.2, hz.2.1⟩
      rw [vab] at hab
      rw [vcb] at hcb
      dsimp [q] at hab hcb ⊢
      apply Zsqrtd.ext <;> dsimp <;> omega
  · let B := TileTranslation A ⟨-(q : Int), (s : Int)⟩
    let C := TileTranslation (FordTile s) ⟨-(s : Int), 0⟩
    change TouchingTriple A B C
    rcases P5110T1SquareInterface q q qpos qpos
        ⟨-(q : Int), (s : Int)⟩ 0 true (by dsimp; omega)
        (by dsimp [q]; omega) with ⟨nb, na, dba, vba, _, _, _, _, pba⟩
    rcases P5110T1SquareInterface s q hs qpos
        ⟨-(s : Int), 0⟩ ⟨-(q : Int), (s : Int)⟩ false (by simp)
        (by dsimp [q]; omega) with ⟨nc, _, dcb, vcb, _, _, _, _, pcb⟩
    rcases P5110T1SquareInterface s q hs qpos
        ⟨-(s : Int), 0⟩ 0 true (by dsimp; omega)
        (by dsimp [q]; omega) with ⟨_, _, dca, vca, _, _, _, _, pca⟩
    rw [zero_shift] at na dba vba pba dca vca pca
    refine ⟨swap _ _ (Or.inl ⟨nb, na, dba, pba⟩),
      swap _ _ (Or.inl ⟨nc, nb, dcb, pcb⟩), Or.inl ⟨nc, na, dca, pca⟩,
      ⟨0, (s : Int)⟩, ?_, ?_⟩
    · have hba : (⟨0, (s : Int)⟩ : GaussianInt) ∈
          BoundaryFootprintVertices B ∩ BoundaryFootprintVertices A := by
        rw [vba]; dsimp [q]; omega
      have hca : (⟨0, (s : Int)⟩ : GaussianInt) ∈
          BoundaryFootprintVertices C ∩ BoundaryFootprintVertices A := by
        rw [vca]; dsimp [q]; omega
      exact ⟨hba.2, hba.1, hca.1⟩
    · intro z hz
      have hba : z ∈ BoundaryFootprintVertices B ∩ BoundaryFootprintVertices A :=
        ⟨hz.2.1, hz.1⟩
      have hca : z ∈ BoundaryFootprintVertices C ∩ BoundaryFootprintVertices A :=
        ⟨hz.2.2, hz.1⟩
      rw [vba] at hba
      rw [vca] at hca
      dsimp [q] at hba hca ⊢
      apply Zsqrtd.ext <;> dsimp <;> omega
  · let B := TileTranslation (FordTile r) ⟨(s : Int), (q : Int)⟩
    let C := TileTranslation (FordTile s) ⟨0, (q : Int)⟩
    change TouchingTriple A B C
    rcases P5110T1SquareInterface q r qpos hr
        0 ⟨(s : Int), (q : Int)⟩ false (by simp)
        (by dsimp [q]; omega) with ⟨na, nb, dab, vab, _, _, _, _, pab⟩
    rcases P5110T1SquareInterface s r hs hr
        ⟨0, (q : Int)⟩ ⟨(s : Int), (q : Int)⟩ true (by simp)
        (by dsimp [q]; omega) with ⟨nc, _, dcb, vcb, _, _, _, _, pcb⟩
    rcases P5110T1SquareInterface q s qpos hs
        0 ⟨0, (q : Int)⟩ false (by simp)
        (by dsimp [q]; omega) with ⟨_, _, dac, vac, _, _, _, _, pac⟩
    rw [zero_shift] at na dab vab pab dac vac pac
    refine ⟨Or.inl ⟨na, nb, dab, pab⟩,
      swap _ _ (Or.inl ⟨nc, nb, dcb, pcb⟩),
      swap _ _ (Or.inl ⟨na, nc, dac, pac⟩), ⟨(s : Int), (q : Int)⟩, ?_, ?_⟩
    · have hab : (⟨(s : Int), (q : Int)⟩ : GaussianInt) ∈
          BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B := by
        rw [vab]; dsimp [q]; omega
      have hac : (⟨(s : Int), (q : Int)⟩ : GaussianInt) ∈
          BoundaryFootprintVertices A ∩ BoundaryFootprintVertices C := by
        rw [vac]; dsimp [q]; omega
      exact ⟨hab.1, hab.2, hac.2⟩
    · intro z hz
      have hab : z ∈ BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B :=
        ⟨hz.1, hz.2.1⟩
      have hac : z ∈ BoundaryFootprintVertices A ∩ BoundaryFootprintVertices C :=
        ⟨hz.1, hz.2.2⟩
      rw [vab] at hab
      rw [vac] at hac
      dsimp [q] at hab hac ⊢
      apply Zsqrtd.ext <;> dsimp <;> omega

end ApollonianSuperharmonic

end
