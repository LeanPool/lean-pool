/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandRegularTileTouchingClassification
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TileString
public import LeanPool.ApollonianSuperharmonic.VectorNonvanishing
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: P4549T1NegativeIncomingSide]

/-!
# P4549T1NegativeIncomingSide

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4549T1NegativeIncomingSide
    {C : BandCircle} {orientation : Bool}
    (t : Fin 4 → CircleCoordinates) (ht : ProperBandQuadruple t)
    (htC : t 0 = C.1.1)
    (base U V : ProtoTile) (g h : PartialOdometer)
    (hbase : BandPrototile C.1.1 base)
    (hU : U ∈ RegularTileFamily base (TilingLattice C))
    (hV : V ∈ RegularTileFamily base (TilingLattice C))
    (hg : TileOdometer C.1.1 U g) (hh : TileOdometer C.1.1 V h)
    (sU sV : ℝ × ℝ)
    (hsU : PartialOdometerSlope g = some sU)
    (hsV : PartialOdometerSlope h = some sV)
    (hcent : TileCentroid V - TileCentroid U =
      GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (t 0) (t 1)))
    (hslope : sV - sU =
      GaussianRealPoint (-(⟨0, 1⟩ : GaussianInt) * BandVectors.2 (t 0) (t 1))) :
    TileString C orientation base U V [U, V] ∧ LeftLatticeAdjacent C U V g h := by
-- BODY
  let I : GaussianInt := ⟨0, 1⟩
  have flip := (VectorRecursionLaws t ht.1).2.2.2.2 ht 0
  change BandVectors.1 (t 0) (t 1) = I * BandVectors.1 (t 1) (t 0) ∧
    BandVectors.2 (t 0) (t 1) = -I * BandVectors.2 (t 1) (t 0) at flip
  have vv : I * BandVectors.1 (t 0) (t 1) = -BandVectors.1 (t 1) (t 0) := by
    rw [flip.1, ← mul_assoc, show I * I = -1 from by decide +kernel, neg_one_mul]
  have aa : -I * BandVectors.2 (t 0) (t 1) = -BandVectors.2 (t 1) (t 0) := by
    rw [flip.2, ← mul_assoc, show -I * -I = -1 from by decide +kernel, neg_one_mul]
  have hc : TileCentroid V - TileCentroid U =
      -GaussianRealPoint (BandVectors.1 (t 1) (t 0)) := by
    rw [vv] at hcent
    simpa [GaussianRealPoint] using hcent
  have ha : sV - sU = -GaussianRealPoint (BandVectors.2 (t 1) (t 0)) := by
    rw [aa] at hslope
    simpa [GaussianRealPoint] using hslope
  have curvature := ProperBandCurvatureStructure t ht
  have hlarge : 1 < (t 0).1 := by
    by_contra hn
    have hzeros : ∀ k : Fin 3, (t k.succ).1 = 0 := by
      intro k
      have hnonneg := curvature.2.1 k
      have hbelow := ht.2 k
      omega
    exact (by decide : (0 : Fin 3) ≠ 1)
      (curvature.2.2 0 1 (hzeros 0) (hzeros 1))
  have hnonunit : C.1.1.1 ≠ 1 := by rw [← htC]; omega
  have htouch : TileTouching U V := by
    apply (BandRegularTileTouchingClassification C t ht htC base
      (htC.symm ▸ hbase) U V hU hV).2
    exact ⟨0, Or.inr hc⟩
  have hvne : BandVectors.1 (t 1) (t 0) ≠ 0 :=
    VectorNonvanishing t ht.1 1 0 (by decide) (Or.inr curvature.1)
  have hne : U ≠ V := by
    intro heq
    rw [heq, sub_self] at hc
    have hz : GaussianRealPoint (BandVectors.1 (t 1) (t 0)) = 0 :=
      neg_eq_zero.mp hc.symm
    apply hvne
    apply Zsqrtd.ext
    · have h := congrArg Prod.fst hz
      dsimp [GaussianRealPoint] at h
      exact_mod_cast h
    · have h := congrArg Prod.snd hz
      dsimp [GaussianRealPoint] at h
      exact_mod_cast h
  constructor
  · unfold TileString
    refine ⟨hbase, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simpa using hne
    · intro T hT
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl
      · exact hU
      · exact hV
    · simpa [List.IsChain, List.isChain_pair, hnonunit] using htouch
    · intro pre T post heq hpre hpost
      have hlen := congrArg List.length heq
      have hp : 1 ≤ pre.length := by
        cases pre with
        | nil => simp at hpre
        | cons x xs => simp
      have hq : 1 ≤ post.length := by
        cases post with
        | nil => simp at hpost
        | cons x xs => simp
      simp at hlen
      omega
  · refine ⟨hg, hh, sU, sV, hsU, hsV, Or.inr ⟨t, 0, false, ht, htC, ?_, ?_, ?_⟩⟩
    · simpa using hc
    · have h := congrArg Prod.fst ha
      simpa [GaussianRealPoint] using h
    · have h := congrArg Prod.snd ha
      simpa [GaussianRealPoint] using h

end ApollonianSuperharmonic

end
