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
public import LeanPool.ApollonianSuperharmonic.TouchingTriplePermutations

-- [TABLET NODE: P5110T1AnchoredTriples]

/-!
# P5110T1AnchoredTriples

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5110T1AnchoredTriples (r s : Nat) (hr : 0 < r) (hs : 0 < s) :
    let q := r + s
    let A := FordTile q
    TouchingTriple A (TileTranslation A ⟨0, -(q : Int)⟩)
        (P5110T1ParentModel r s 2 true) ∧
    TouchingTriple A (P5110T1ParentModel r s 1 true)
        (P5110T1ParentModel r s 2 false) ∧
    TouchingTriple A (P5110T1ParentModel r s 2 true)
        (P5110T1ParentModel r s 0 false) := by
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
  have with_empty (A B : ProtoTile) (a : GaussianInt) (h : TileTouching A B)
      (ha : a ∈ BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B) :
      TouchingTriple A B ⟨∅, a⟩ := by
    refine ⟨h, Or.inr (Or.inr ⟨rfl, ha.2⟩),
      Or.inr (Or.inl ⟨rfl, ha.1⟩), a, ?_, ?_⟩
    · exact ⟨ha.1, ha.2, by simp [BoundaryFootprintVertices]⟩
    · intro y hy
      simpa [BoundaryFootprintVertices] using hy.2.2
  let q := r + s
  let A := FordTile q
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · let B := TileTranslation A ⟨0, -(q : Int)⟩
    change TouchingTriple A B ⟨∅, ⟨(q : Int), 0⟩⟩
    rcases P5110T1SquareInterface q q qpos qpos
        ⟨0, -(q : Int)⟩ 0 false (by dsimp; omega)
        (by dsimp [q]; omega) with ⟨nb, na, dba, vba, _, _, _, _, pba⟩
    rw [zero_shift] at na dba vba pba
    apply with_empty A B ⟨(q : Int), 0⟩
      (swap _ _ (Or.inl ⟨nb, na, dba, pba⟩))
    have hba : (⟨(q : Int), 0⟩ : GaussianInt) ∈
        BoundaryFootprintVertices B ∩ BoundaryFootprintVertices A := by
      rw [vba]; dsimp [q]; omega
    exact ⟨hba.2, hba.1⟩
  · let B := TileTranslation (FordTile s) ⟨-(s : Int), 0⟩
    change TouchingTriple A B ⟨∅, 0⟩
    rcases P5110T1SquareInterface s q hs qpos
        ⟨-(s : Int), 0⟩ 0 true (by dsimp; omega)
        (by dsimp [q]; omega) with ⟨nb, na, dba, vba, _, _, _, _, pba⟩
    rw [zero_shift] at na dba vba pba
    apply with_empty A B 0 (swap _ _ (Or.inl ⟨nb, na, dba, pba⟩))
    have hba : (0 : GaussianInt) ∈
        BoundaryFootprintVertices B ∩ BoundaryFootprintVertices A := by
      rw [vba]; dsimp [q]; omega
    exact ⟨hba.2, hba.1⟩
  · let B := TileTranslation (FordTile r) ⟨(q : Int), 0⟩
    change TouchingTriple A ⟨∅, ⟨(q : Int), 0⟩⟩ B
    rcases P5110T1SquareInterface q r qpos hr
        0 ⟨(q : Int), 0⟩ true (by simp)
        (by dsimp [q]; omega) with ⟨na, nb, dab, vab, _, _, _, _, pab⟩
    rw [zero_shift] at na dab vab pab
    apply (TouchingTriplePermutations A B ⟨∅, ⟨(q : Int), 0⟩⟩).mp _ |>.1
    apply with_empty A B ⟨(q : Int), 0⟩ (Or.inl ⟨na, nb, dab, pab⟩)
    rw [vab]; dsimp [q]; omega

end ApollonianSuperharmonic

end
