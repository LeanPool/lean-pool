/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4458T1RestrictionFamily
public import LeanPool.ApollonianSuperharmonic.P4536T1EndpointAlgebra
public import LeanPool.ApollonianSuperharmonic.P4536T1HalfOffsetBridge
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: P4536T1EndpointDifferences]

/-!
# P4536T1EndpointDifferences

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4536T1EndpointDifferences
    {C : BandCircle} {orientation : Bool} {base Rminus Rplus : ProtoTile}
    {hminus hplus : PartialOdometer}
    (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus)
    (D : P4458T1RestrictionFamily F) :
    ∃ s : ℝ × ℝ,
      PartialOdometerSlope (D.functions F.slot false) = some s ∧
      TileCentroid (D.tiles F.slot false) - TileCentroid Rminus =
        GaussianRealPoint (BandVectors.1 (F.q (F.slot + 1).succ) (F.q F.slot.succ)) ∧
      TileCentroid Rplus - TileCentroid (D.tiles F.slot false) =
        GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) *
          BandVectors.1 (F.q F.slot.succ) (F.q (F.slot + 2).succ)) ∧
      s - F.minusSlope =
        GaussianRealPoint (BandVectors.2 (F.q (F.slot + 1).succ) (F.q F.slot.succ)) ∧
      F.plusSlope - s =
        GaussianRealPoint (-(⟨0, 1⟩ : GaussianInt) *
          BandVectors.2 (F.q F.slot.succ) (F.q (F.slot + 2).succ)) := by
-- BODY
  let r : Fin 4 → CircleCoordinates :=
    ![F.q 0, F.q F.slot.succ, F.q (F.slot + 1).succ, F.q (F.slot + 2).succ]
  have hr : ProperBandQuadruple r := by
    have rot : ∀ j : Fin 3, ProperBandQuadruple
        ![F.q 0, F.q j.succ, F.q (j + 1).succ, F.q (j + 2).succ] := by
      intro j
      fin_cases j
      · convert F.proper using 1; funext k; fin_cases k <;> rfl
      · refine ⟨SemiProperQuadruple.rotate F.proper.1, ?_⟩
        intro k
        fin_cases k
        · exact F.proper.2 1
        · exact F.proper.2 2
        · exact F.proper.2 0
      · refine ⟨SemiProperQuadruple.rotate (SemiProperQuadruple.rotate F.proper.1), ?_⟩
        intro k
        fin_cases k
        · exact F.proper.2 2
        · exact F.proper.2 0
        · exact F.proper.2 1
    exact rot F.slot
  let I : GaussianInt := ⟨0, 1⟩
  let w := BandVectors.1 (r 3) (r 2)
  let x := BandVectors.1 (r 1) (r 3)
  let y := BandVectors.1 (r 2) (r 1)
  let wa := BandVectors.2 (r 3) (r 2)
  let xa := BandVectors.2 (r 1) (r 3)
  let ya := BandVectors.2 (r 2) (r 1)
  have laws := VectorRecursionLaws r hr.1
  have vflip : BandVectors.1 (r 0) (r 1) = I * BandVectors.1 (r 1) (r 0) :=
    (laws.2.2.2.2 hr 0).1
  have aflip : BandVectors.2 (r 0) (r 1) = -I * BandVectors.2 (r 1) (r 0) :=
    (laws.2.2.2.2 hr 0).2
  have hv := P4536T1EndpointAlgebra I w x y (by decide +kernel) laws.1
  have ha := P4536T1EndpointAlgebra (-I) wa xa ya (by decide +kernel) laws.2.1
  have vm : TileCentroid Rminus - TileCentroid F.tile =
      (1 / 2 : ℝ) • GaussianRealPoint ((x - I * y) - I * (x - I * y)) := by
    have h := F.minus_centroid
    change TileCentroid Rminus - TileCentroid F.tile =
      (1 / 2 : ℝ) • GaussianRealPoint
        (BandVectors.1 (r 1) (r 0) - BandVectors.1 (r 0) (r 1)) at h
    rw [vflip, laws.2.2.1] at h
    exact h
  have vp : TileCentroid Rplus - TileCentroid F.tile =
      (1 / 2 : ℝ) • GaussianRealPoint ((x - I * y) + I * (x - I * y)) := by
    have h := F.plus_centroid
    change TileCentroid Rplus - TileCentroid F.tile =
      (1 / 2 : ℝ) • GaussianRealPoint
        (BandVectors.1 (r 1) (r 0) + BandVectors.1 (r 0) (r 1)) at h
    rw [vflip, laws.2.2.1] at h
    exact h
  have vn : TileCentroid (D.tiles F.slot false) - TileCentroid F.tile =
      (1 / 2 : ℝ) • GaussianRealPoint (-(w - I * w)) := by
    have h := (D.occurrences F.slot false).2.2
    change TileCentroid (D.tiles F.slot false) - TileCentroid F.tile =
      (-1 : ℝ) • ((1 / 2 : ℝ) •
        (GaussianRealPoint w - (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))) at h
    rw [h]
    ext <;> simp [GaussianRealPoint, I, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
  have pos : 0 < (F.q F.slot.succ).1 := F.parent ▸ C.2
  rcases D.slopes F.slot false with hz | ⟨root, s, hroot, hs, hre, him⟩
  · omega
  have hrootEq : root = F.outerSlope := Option.some.inj (hroot.symm.trans F.slope_outer)
  subst root
  have an : s - F.outerSlope =
      (1 / 2 : ℝ) • GaussianRealPoint (-(wa - (-I) * wa)) := by
    change s.1 - F.outerSlope.1 = -1 * (1 / 2 : ℝ) *
      ((wa.re : ℝ) - (wa.im : ℝ)) at hre
    change s.2 - F.outerSlope.2 = -1 * (1 / 2 : ℝ) *
      ((wa.im : ℝ) + (wa.re : ℝ)) at him
    apply Prod.ext
    · simp [GaussianRealPoint, I, Zsqrtd.re_mul, Zsqrtd.im_mul] at hre ⊢
      linarith [hre]
    · simp [GaussianRealPoint, I, Zsqrtd.re_mul, Zsqrtd.im_mul] at him ⊢
      linarith [him]
  have am : F.minusSlope - F.outerSlope = (1 / 2 : ℝ) •
      GaussianRealPoint ((xa - (-I) * ya) - (-I) * (xa - (-I) * ya)) := by
    have h := F.minus_difference
    change F.minusSlope - F.outerSlope = (1 / 2 : ℝ) • GaussianRealPoint
      (BandVectors.2 (r 1) (r 0) - BandVectors.2 (r 0) (r 1)) at h
    rw [aflip, laws.2.2.2.1] at h
    simpa only [sub_neg_eq_add, neg_mul] using h
  have ap : F.plusSlope - F.outerSlope = (1 / 2 : ℝ) •
      GaussianRealPoint ((xa - (-I) * ya) + (-I) * (xa - (-I) * ya)) := by
    have h := F.plus_difference
    change F.plusSlope - F.outerSlope = (1 / 2 : ℝ) • GaussianRealPoint
      (BandVectors.2 (r 1) (r 0) + BandVectors.2 (r 0) (r 1)) at h
    rw [aflip, laws.2.2.2.1] at h
    simpa only [sub_neg_eq_add, neg_mul] using h
  refine ⟨s, hs, ?_, ?_, ?_, ?_⟩
  · change TileCentroid (D.tiles F.slot false) - TileCentroid Rminus = GaussianRealPoint y
    calc
      _ = (TileCentroid (D.tiles F.slot false) - TileCentroid F.tile) -
          (TileCentroid Rminus - TileCentroid F.tile) := by abel
      _ = _ := by rw [vn, vm]; exact P4536T1HalfOffsetBridge _ _ _ hv.1
  · change TileCentroid Rplus - TileCentroid (D.tiles F.slot false) = GaussianRealPoint (I * x)
    calc
      _ = (TileCentroid Rplus - TileCentroid F.tile) -
          (TileCentroid (D.tiles F.slot false) - TileCentroid F.tile) := by abel
      _ = _ := by
        rw [vp, vn]
        apply P4536T1HalfOffsetBridge
        simpa only [sub_neg_eq_add, mul_assoc] using hv.2.1
  · change s - F.minusSlope = GaussianRealPoint ya
    calc
      _ = (s - F.outerSlope) - (F.minusSlope - F.outerSlope) := by abel
      _ = _ := by rw [an, am]; exact P4536T1HalfOffsetBridge _ _ _ ha.1
  · change F.plusSlope - s = GaussianRealPoint (-I * xa)
    calc
      _ = (F.plusSlope - F.outerSlope) - (s - F.outerSlope) := by abel
      _ = _ := by
        rw [ap, an]
        apply P4536T1HalfOffsetBridge
        simpa only [sub_neg_eq_add, mul_assoc] using ha.2.1

end ApollonianSuperharmonic

end
