/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileString

/-!
# Two-tile strings

Shared construction from the upstream two-tile string proofs. A pair has no
interior tiles, so endpoint membership, distinctness and selected adjacency suffice.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TileStringPair (C : BandCircle) (orientation : Bool) (base R S : ProtoTile)
    (hbase : BandPrototile C.1.1 base)
    (hR : R ∈ RegularTileFamily base (TilingLattice C))
    (hS : S ∈ RegularTileFamily base (TilingLattice C)) (hne : R ≠ S)
    (hadjacent : if C.1.1.1 = 1 then
      ∃ v : GaussianInt, UnitTriangularStep orientation v ∧
        TileCentroid S - TileCentroid R = GaussianRealPoint v
      else TileTouching R S) :
    TileString C orientation base R S [R, S] := by
  classical
  unfold TileString
  refine ⟨hbase, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simpa using hne
  · intro T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact hR
    · exact hS
  · simpa [List.IsChain, List.isChain_pair] using hadjacent
  · intro pre T post heq hpre hpost
    have hlength := congrArg List.length heq
    simp only [List.length_cons, List.length_nil, List.length_append] at hlength
    have hpreLength : 1 ≤ pre.length := List.length_pos_iff.mpr hpre
    have hpostLength : 1 ≤ post.length := List.length_pos_iff.mpr hpost
    have hbound : 3 ≤ pre.length + (post.length + 1) :=
      Nat.add_le_add hpreLength (Nat.succ_le_succ hpostLength)
    have hfalse : ¬ (3 : ℕ) ≤ 2 := by decide
    apply False.elim
    apply hfalse
    calc
      3 ≤ pre.length + (post.length + 1) := hbound
      _ = 2 := hlength.symm

theorem TileStringPairOfNonunit (C : BandCircle) (orientation : Bool) (base R S : ProtoTile)
    (hbase : BandPrototile C.1.1 base)
    (hR : R ∈ RegularTileFamily base (TilingLattice C))
    (hS : S ∈ RegularTileFamily base (TilingLattice C)) (hne : R ≠ S)
    (hnonunit : C.1.1.1 ≠ 1) (htouching : TileTouching R S) :
    TileString C orientation base R S [R, S] := by
  apply TileStringPair C orientation base R S hbase hR hS hne
  simpa only [ite_eq_right hnonunit] using htouching

end ApollonianSuperharmonic
