/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileOdometer
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslateFormulas
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.GaussianQuarterTurn

-- [TABLET NODE: P4250T1DefinedHalfIntegralSlope]

/-!
# P4250T1DefinedHalfIntegralSlope

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4250T1DefinedHalfIntegralSlope
    (C : CircleCoordinates) (T : ProtoTile) (h : PartialOdometer)
    (hC : 0 < C.1) (ho : TileOdometer C T h) :
    ∃ (p : Real × Real) (a : GaussianInt),
      PartialOdometerSlope h = some p ∧
      (2 : Real) • p = GaussianRealPoint a ∧ T.cells.Nonempty := by
-- BODY
  classical
  have unitSlope (z : GaussianInt) : PartialOdometerSlope (CurvatureOneOdometer z) =
      some (((z.im : Real) / 2), ((z.im : Real) / 2)) := by
    have hs : PartialOdometerSquares (CurvatureOneOdometer z) = {0} := by
      change PartialOdometerSquares (CurvatureOneOdometer 0) = {0}
      decide +kernel
    unfold PartialOdometerSlope
    rw [hs]
    norm_num [CurvatureOneOdometer, Zsqrtd.ext_iff]
  induction ho with
  | line w x hw h hdom => simp at hC
  | unit z x T h hT hdom htrans =>
      obtain ⟨v, a, b, hd, hv⟩ := htrans
      have hdeq : h.domain =
          (PartialOdometerAffineTranslate (CurvatureOneOdometer z) v a b).domain := by
        ext y
        rw [(PartialOdometerAffineTranslateFormulas _ v a b).2.1]
        exact hd y
      have hveq : h.value =
          (PartialOdometerAffineTranslate (CurvatureOneOdometer z) v a b).value := by
        funext y
        by_cases hy : y ∈ h.domain
        · rw [hv y hy, (PartialOdometerAffineTranslateFormulas _ v a b).2.2.1
            y (by rwa [← hdeq])]
        · rw [h.value_outside y hy,
            (PartialOdometerAffineTranslate _ v a b).value_outside y
              (by rwa [← hdeq])]
      have heq : h = PartialOdometerAffineTranslate (CurvatureOneOdometer z) v a b := by
        cases h
        simp only [PartialOdometerAffineTranslate, PartialOdometer.mk.injEq]
        exact ⟨hdeq, hveq⟩
      refine ⟨((z.im : Real) / 2 + (a.re : Real),
        (z.im : Real) / 2 + (a.im : Real)),
        ⟨z.im + 2 * a.re, z.im + 2 * a.im⟩, ?_, ?_, ?_⟩
      · rw [heq, (PartialOdometerAffineTranslateFormulas _ v a b).2.2.2.2.2,
          unitSlope]
        rfl
      · ext <;> simp [GaussianRealPoint] <;> ring
      · rw [hT]
        simp
  | @decompose q hq S T hs h hT hsub hcells hfoot hcentroid hdom hvalue
      hcompat hslope ih =>
      have facts := ProperBandCurvatureStructure q hq
      have hpositive : ∃ i : Fin 3, 0 < (q i.succ).1 := by
        by_cases h0 : 0 < (q (0 : Fin 3).succ).1
        · exact ⟨0, h0⟩
        by_cases h1 : 0 < (q (1 : Fin 3).succ).1
        · exact ⟨1, h1⟩
        have hzero0 : (q (0 : Fin 3).succ).1 = 0 := by
          have := facts.2.1 0
          omega
        have hzero1 : (q (1 : Fin 3).succ).1 = 0 := by
          have := facts.2.1 1
          omega
        exact ((by decide : (0 : Fin 3) ≠ 1) (facts.2.2 0 1 hzero0 hzero1)).elim
      obtain ⟨i, hi⟩ := hpositive
      obtain ⟨pi, ai, hpi, hai, hne⟩ := ih i true hi
      rcases hslope i true with hz | ⟨p, pi', hp, hpi', hreal, himag⟩
      · omega
      have heq : pi' = pi := Option.some.inj (hpi'.symm.trans hpi)
      subst pi'
      let a := BandVectors.2 (q ((i + 2).succ)) (q ((i + 1).succ))
      refine ⟨p, ai - (a + GaussianQuarterTurn a), hp, ?_, ?_⟩
      · have hr := congrArg Prod.fst hai
        have hi := congrArg Prod.snd hai
        apply Prod.ext
        all_goals
          simp [GaussianRealPoint, GaussianQuarterTurn, a] at hr hi ⊢
          simp at hreal himag
          linarith
      · obtain ⟨x, hx⟩ := hne
        exact ⟨x, (hcells x).2 ⟨i, true, hx⟩⟩

end ApollonianSuperharmonic

end
