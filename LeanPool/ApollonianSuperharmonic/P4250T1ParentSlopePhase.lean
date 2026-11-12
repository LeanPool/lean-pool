/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4250T1SlopeOffset
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralConfiguration
public import LeanPool.ApollonianSuperharmonic.TileOdometerReindexedDecomposition
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness
public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslateFormulas
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn

-- [TABLET NODE: P4250T1ParentSlopePhase]

/-!
# P4250T1ParentSlopePhase

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4250T1ParentSlopePhase
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (U : Fin 3 → ProtoTile) (h : Fin 3 → PartialOdometer)
    (p : Fin 3 → Real × Real) (a : GaussianInt)
    (ho : ∀ i, TileOdometer (q i.succ) (U i) (h i))
    (hp : ∀ i, PartialOdometerSlope (h i) = some (p i))
    (ha : (2 : Real) • p 0 = GaussianRealPoint a) :
    ∃ (s0 : Real × Real) (b : GaussianInt) (z : Fin 3 → GaussianInt),
      (2 : Real) • s0 = GaussianRealPoint b ∧
      ∀ i, p i = s0 +
        P4250T1SlopeOffset
          (BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))) +
        GaussianRealPoint (z i) := by
-- BODY
  classical
  have positive (i : Fin 3) : 0 < (q i.succ).1 := by
    have := (ProperBandCurvatureStructure q cfg.proper).2.1 i
    have := cfg.noLine i.succ
    omega
  have compare (i : Fin 3) (V : ProtoTile) (k : PartialOdometer) (pk : Real × Real)
      (hk : TileOdometer (q i.succ) V k) (hpk : PartialOdometerSlope k = some pk) :
      ∃ z : GaussianInt, p i = pk + GaussianRealPoint z := by
    obtain ⟨u, ⟨_, _, a, b, hd, hv⟩, _⟩ :=
      TileOdometerTranslationUniqueness _ (U i) V (h i) k (positive i) (ho i) hk
    have hdeq : (h i).domain = (PartialOdometerAffineTranslate k u a b).domain := by
      ext x
      rw [(PartialOdometerAffineTranslateFormulas k u a b).2.1]
      exact hd x
    have hveq : (h i).value = (PartialOdometerAffineTranslate k u a b).value := by
      funext x
      by_cases hx : x ∈ (h i).domain
      · rw [hv x hx, (PartialOdometerAffineTranslateFormulas k u a b).2.2.1
          x (by rwa [← hdeq])]
      · rw [(h i).value_outside x hx,
          (PartialOdometerAffineTranslate k u a b).value_outside x (by rwa [← hdeq])]
    have heq : h i = PartialOdometerAffineTranslate k u a b := by
      generalize h i = H at hdeq hveq ⊢
      cases H
      simp only [PartialOdometerAffineTranslate, PartialOdometer.mk.injEq]
      exact ⟨hdeq, hveq⟩
    have hs := hp i
    rw [heq, (PartialOdometerAffineTranslateFormulas k u a b).2.2.2.2.2, hpk] at hs
    exact ⟨a, (Option.some.inj hs).symm⟩
  let r := cfg.firstPredecessor
  have hr : ProperBandQuadruple r := cfg.firstProper
  have hroot : TileOdometer (r 0) (U 0) (h 0) := by
    simpa [r, cfg.firstChild] using ho 0
  have hlarge : 1 < (r 0).1 := by
    have := cfg.secondLarge
    have := cfg.order12
    simp only [r, cfg.firstChild]
    omega
  obtain ⟨S, k, _, hsub, _, _, _, _, _, _, hslope⟩ :=
    TileOdometerReindexedDecomposition r hr (U 0) (h 0) hlarge hroot
  let w := BandVectors.2 (q 3) (q 2)
  let X := BandVectors.2 (r 1) (r 3)
  let Y := BandVectors.2 (r 2) (r 1)
  have smallSlopes (i : Fin 3) (hi : 0 < (r i.succ).1) :
      ∃ pi : Real × Real, PartialOdometerSlope (k i true) = some pi ∧
        pi = p 0 + P4250T1SlopeOffset
          (BandVectors.2 (r ((i + 2).succ)) (r ((i + 1).succ))) := by
    rcases hslope i true with hz | ⟨p0, pi, hp0, hpi, hx, hy⟩
    · omega
    have heq : p0 = p 0 := Option.some.inj (hp0.symm.trans (hp 0))
    subst p0
    refine ⟨pi, hpi, ?_⟩
    apply Prod.ext
    all_goals simp [P4250T1SlopeOffset] at hx hy ⊢; linarith
  have hpos2 : 0 < (r (1 : Fin 3).succ).1 := by
    simpa [r, cfg.firstParentTwo] using positive 1
  have hpos3 : 0 < (r (2 : Fin 3).succ).1 := by
    simpa [r, cfg.firstParentThree] using positive 2
  obtain ⟨p2, hp2, heq2⟩ := smallSlopes 1 hpos2
  obtain ⟨p3, hp3, heq3⟩ := smallSlopes 2 hpos3
  have hk2 : TileOdometer (q (1 : Fin 3).succ) (S 1 true) (k 1 true) := by
    simpa [r, cfg.firstParentTwo] using hsub 1 true
  have hk3 : TileOdometer (q (2 : Fin 3).succ) (S 2 true) (k 2 true) := by
    simpa [r, cfg.firstParentThree] using hsub 2 true
  obtain ⟨z2, hz2⟩ := compare 1 _ _ p2 hk2 hp2
  obtain ⟨z3, hz3⟩ := compare 2 _ _ p3 hk3 hp3
  change p2 = p 0 + P4250T1SlopeOffset X at heq2
  change p3 = p 0 + P4250T1SlopeOffset Y at heq3
  rw [heq2] at hz2
  rw [heq3] at hz3
  let r1 : Fin 4 → CircleCoordinates := ![r 0, r 2, r 3, r 1]
  let r2 : Fin 4 → CircleCoordinates := ![r 0, r 3, r 1, r 2]
  have hr1 : SemiProperQuadruple r1 := hr.1.rotate
  have hr2 : SemiProperQuadruple r2 := by
    simpa [r1, r2] using hr1.rotate
  have incoming2 : BandVectors.2 (r 2) (r 0) =
      Y + (⟨0, 1⟩ : GaussianInt) * w := by
    simpa [r1, Y, w, r, cfg.firstParentTwo, cfg.firstParentThree] using
      (VectorRecursionLaws r1 hr1).2.2.2.1
  have incoming3 : BandVectors.2 (r 3) (r 0) =
      w + (⟨0, 1⟩ : GaussianInt) * X := by
    simpa [r2, X, w, r, cfg.firstParentTwo, cfg.firstParentThree] using
      (VectorRecursionLaws r2 hr2).2.2.2.1
  have hX : BandVectors.2 (q 1) (q 3) =
      X - (⟨0, 1⟩ : GaussianInt) * w := by
    have flip := ((VectorRecursionLaws r hr.1).2.2.2.2 hr 2).2
    change BandVectors.2 (r 0) (r 3) =
      -(⟨0, 1⟩ : GaussianInt) * BandVectors.2 (r 3) (r 0) at flip
    rw [incoming3] at flip
    have heq : BandVectors.2 (q 1) (q 3) =
        -(⟨0, 1⟩ : GaussianInt) * (w + (⟨0, 1⟩ : GaussianInt) * X) := by
      simpa [r, cfg.firstChild, cfg.firstParentThree] using flip
    rw [heq]
    apply Zsqrtd.ext <;> simp <;> ring
  have hY : BandVectors.2 (q 2) (q 1) =
      Y + (⟨0, 1⟩ : GaussianInt) * w := by
    simpa [r, cfg.firstChild, cfg.firstParentTwo] using incoming2
  refine ⟨p 0 - P4250T1SlopeOffset w,
    a - (w + GaussianQuarterTurn w),
    ![0, z2 + GaussianQuarterTurn w, z3 + w], ?_, ?_⟩
  · have hr := congrArg Prod.fst ha
    have hi := congrArg Prod.snd ha
    apply Prod.ext
    all_goals simp [GaussianRealPoint, GaussianQuarterTurn,
      P4250T1SlopeOffset] at hr hi ⊢; linarith
  · intro i
    fin_cases i
    · simp [w, GaussianRealPoint]
    · have hr := congrArg Prod.fst hz2
      have hi := congrArg Prod.snd hz2
      apply Prod.ext
      all_goals simp [hX, GaussianRealPoint, GaussianQuarterTurn,
        P4250T1SlopeOffset] at hr hi ⊢; linarith
    · have hr := congrArg Prod.fst hz3
      have hi := congrArg Prod.snd hz3
      apply Prod.ext
      all_goals simp [hY, GaussianRealPoint, GaussianQuarterTurn,
        P4250T1SlopeOffset] at hr hi ⊢; linarith

end ApollonianSuperharmonic

end
