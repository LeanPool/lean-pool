/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4261T2AdjacentMatrixSlope
public import LeanPool.ApollonianSuperharmonic.P4250T1DefinedHalfIntegralSlope
public import LeanPool.ApollonianSuperharmonic.OdometerStringRespect

-- [TABLET NODE: P4261T2UnitStringTelescoping]

/-!
# P4261T2UnitStringTelescoping

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4261T2UnitStringTelescoping
    (C : BandCircle) (_hunit : C.1.1.1 = 1)
    (orientation : Bool) (base R S : ProtoTile)
    (tiles reverseTiles : List ProtoTile) (hs reverseHs : List PartialOdometer)
    (hf : OdometerStringRespect C orientation base R S tiles hs)
    (hr : OdometerStringRespect C orientation base S R reverseTiles reverseHs)
    (hendpoint : PartialOdometer)
    (hh : hs.head? = some hendpoint) (hh' : reverseHs.getLast? = some hendpoint)
    (U V : ProtoTile) (g k : PartialOdometer)
    (hU : (U, g) ∈ tiles.zip hs) (hV : (V, k) ∈ reverseTiles.zip reverseHs) :
    ∃ s t : Real × Real,
      PartialOdometerSlope g = some s ∧ PartialOdometerSlope k = some t ∧
      t.1 - s.1 = CircleMatrix C 0 0 * ((TileCentroid V).1 - (TileCentroid U).1) +
        CircleMatrix C 0 1 * ((TileCentroid V).2 - (TileCentroid U).2) ∧
      t.2 - s.2 = CircleMatrix C 1 0 * ((TileCentroid V).1 - (TileCentroid U).1) +
        CircleMatrix C 1 1 * ((TileCentroid V).2 - (TileCentroid U).2) := by
-- BODY
  obtain ⟨s, _, hsg, _⟩ := P4250T1DefinedHalfIntegralSlope C.1.1 U g C.2
    (List.forall₂_zip hf.2.1 hU)
  obtain ⟨t, _, htk, _⟩ := P4250T1DefinedHalfIntegralSlope C.1.1 V k C.2
    (List.forall₂_zip hr.2.1 hV)
  let invariant := fun X : ProtoTile × PartialOdometer =>
    let p := (PartialOdometerSlope X.2).getD (0, 0)
    (p.1 - CircleMatrix C 0 0 * (TileCentroid X.1).1 -
        CircleMatrix C 0 1 * (TileCentroid X.1).2,
      p.2 - CircleMatrix C 1 0 * (TileCentroid X.1).1 -
        CircleMatrix C 1 1 * (TileCentroid X.1).2)
  let invRel := fun X Y : ProtoTile × PartialOdometer => invariant X = invariant Y
  have invStep : ∀ A B : ProtoTile × PartialOdometer,
      LeftLatticeAdjacent C A.1 B.1 A.2 B.2 → invRel A B := by
    intro A B hadj
    obtain ⟨p, r, hp, hr, h0, h1⟩ := P4261T2AdjacentMatrixSlope C _ _ _ _ hadj
    change invariant A = invariant B
    apply Prod.ext <;> simp only [invariant, hp, hr, Option.getD_some]
    · linear_combination -h0
    · linear_combination -h1
  have hfirstChain : (tiles.zip hs).IsChain invRel := hf.2.2.imp invStep
  have hsecondChain : (reverseTiles.zip reverseHs).IsChain invRel := hr.2.2.imp invStep
  let : Trans invRel invRel invRel := ⟨by
    intro a b c hab hbc
    exact hab.trans hbc⟩
  let : Std.Refl invRel := ⟨fun _ => rfl⟩
  have hfirstPairwise := List.isChain_iff_pairwise.mp hfirstChain
  have hsecondPairwise := List.isChain_iff_pairwise.mp hsecondChain
  obtain ⟨postTiles, hpostTiles⟩ := List.head?_eq_some_iff.mp hf.1.2.1
  obtain ⟨postHs, hpostHs⟩ := List.head?_eq_some_iff.mp hh
  have hzipHead : tiles.zip hs = (R, hendpoint) :: postTiles.zip postHs := by
    rw [hpostTiles, hpostHs]
    rfl
  obtain ⟨preTiles, hpreTiles⟩ := List.getLast?_eq_some_iff.mp hr.1.2.2.1
  obtain ⟨preHs, hpreHs⟩ := List.getLast?_eq_some_iff.mp hh'
  have hlenPre : preTiles.length = preHs.length := by
    have hlen := List.Forall₂.length_eq hr.2.1
    rw [hpreTiles, hpreHs, List.length_append, List.length_singleton,
      List.length_append, List.length_singleton] at hlen
    omega
  have hzipLast : reverseTiles.zip reverseHs = preTiles.zip preHs ++ [(R, hendpoint)] := by
    rw [hpreTiles, hpreHs, List.zip_append hlenPre]
    simp
  have hInvU : invariant (R, hendpoint) = invariant (U, g) := by
    rw [hzipHead] at hfirstPairwise hU
    simpa using hfirstPairwise.rel_head hU
  have hInvV : invariant (V, k) = invariant (R, hendpoint) := by
    rw [hzipLast] at hsecondPairwise hV
    simpa using hsecondPairwise.rel_getLast hV
  have hInvUV := hInvU.symm.trans hInvV.symm
  refine ⟨s, t, hsg, htk, ?_, ?_⟩
  · have heq := congrArg Prod.fst hInvUV
    simp only [invariant, hsg, htk, Option.getD_some] at heq
    linear_combination -heq
  · have heq := congrArg Prod.snd hInvUV
    simp only [invariant, hsg, htk, Option.getD_some] at heq
    linear_combination -heq

end ApollonianSuperharmonic

end
