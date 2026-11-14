/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4536T1EndpointDifferences
public import LeanPool.ApollonianSuperharmonic.P4536T1TangentPairMatrix
public import LeanPool.ApollonianSuperharmonic.BandOrientedBoundaryOccurrenceGenealogy
public import LeanPool.ApollonianSuperharmonic.BandVectorOrientationDichotomy
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.TileString

-- [TABLET NODE: P4536T1SmallUnitSides]

/-!
# P4536T1SmallUnitSides

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4536T1SmallUnitSides
    {C : BandCircle} {orientation : Bool} {base Rminus Rplus : ProtoTile}
    {hminus hplus : PartialOdometer}
    (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus)
    (D : P4458T1RestrictionFamily F)
    (a : Fin 3) (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
    (hstep : ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] =
      ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
        p 0, p 2, p 3])
    (small : ((p 2).1 = 0 ∨ (p 2).1 = 1) ∧
      ((p 3).1 = 0 ∨ (p 3).1 = 1))
    (J : ProtoTile) (hfamily : J ∈ RegularTileFamily base (TilingLattice C))
    (hodo : TileOdometer C.1.1 J (D.functions F.slot false))
    (hcent : TileCentroid J = TileCentroid (D.tiles F.slot false)) :
    (F.slot = a + 1 →
      TileString C orientation base Rminus J [Rminus, J] ∧
      LeftLatticeAdjacent C Rminus J hminus (D.functions F.slot false)) ∧
    (F.slot = a + 2 →
      TileString C orientation base J Rplus [J, Rplus] ∧
      LeftLatticeAdjacent C J Rplus (D.functions F.slot false) hplus) := by
-- BODY
  classical
  let q : Fin 4 → CircleCoordinates :=
    ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
        2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2), p 0, p 2, p 3]
  have hqB : F.q (a + 1).succ = p 2 := by simpa using congrFun hstep 2
  have hqD : F.q (a + 2).succ = p 3 := by simpa using congrFun hstep 3
  have eta : ![F.q 0, F.q 1, F.q 2, F.q 3] = F.q := by
    funext k
    fin_cases k <;> rfl
  have large (t : Fin 4 → CircleCoordinates) (ht : ProperBandQuadruple t) :
      1 < (t 0).1 := by
    have f := ProperBandCurvatureStructure t ht
    have n0 := f.2.1 0
    have n1 := f.2.1 1
    have l0 := ht.2 0
    have l1 := ht.2 1
    by_contra h
    have z0 : (t (0 : Fin 3).succ).1 = 0 := by omega
    have z1 : (t (1 : Fin 3).succ).1 = 0 := by omega
    exact (by decide : (0 : Fin 3) ≠ 1) (f.2.2 0 1 z0 z1)
  have steps :
      (∀ e, UnitOccurrenceOrientation q 1 e →
        UnitTriangularStep e (BandVectors.1 (p 3) (p 2))) ∧
      (∀ e, UnitOccurrenceOrientation q 2 e →
        UnitTriangularStep e ((⟨0, 1⟩ : GaussianInt) * BandVectors.1 (p 3) (p 2))) := by
    rcases (BandOrientedBoundaryOccurrenceGenealogy p hp).2.2.2.2.2 with
      ⟨_, hd⟩ | ⟨t, ht, ht0, _⟩ | ⟨t, ht, ht0, _⟩
    · rcases hd with ⟨_, hB, hD, _⟩ | ⟨_, hB, hD, _⟩ <;>
        exact ⟨fun e he => (hB e he).1, fun e he => (hD e he).1⟩
    · have hl := large t ht
      rw [ht0] at hl
      rcases small.1 with h | h <;> omega
    · have hl := large t ht
      rw [ht0] at hl
      rcases small.2 with h | h <;> omega
  obtain ⟨s, hs, cvL, cvR, caL, caR⟩ := P4536T1EndpointDifferences F D
  rw [← hcent] at cvL cvR
  have unit_side (U V : ProtoTile) (g h : PartialOdometer) (r t : ℝ × ℝ)
      (v b : GaussianInt) (hu : C.1.1.1 = 1)
      (hU : TileOdometer C.1.1 U g) (hV : TileOdometer C.1.1 V h)
      (hUf : U ∈ RegularTileFamily base (TilingLattice C))
      (hVf : V ∈ RegularTileFamily base (TilingLattice C))
      (hr : PartialOdometerSlope g = some r) (ht : PartialOdometerSlope h = some t)
      (hv : UnitTriangularStep orientation v)
      (hc : TileCentroid V - TileCentroid U = GaussianRealPoint v)
      (hb : t - r = GaussianRealPoint b)
      (hm : (b.re : ℝ) = CircleMatrix C 0 0 * v.re + CircleMatrix C 0 1 * v.im ∧
        (b.im : ℝ) = CircleMatrix C 1 0 * v.re + CircleMatrix C 1 1 * v.im) :
      TileString C orientation base U V [U, V] ∧ LeftLatticeAdjacent C U V g h := by
    have hv0 : v ≠ 0 := by
      intro hz
      rw [hz] at hv
      cases orientation <;> norm_num [UnitTriangularStep, Zsqrtd.ext_iff] at hv
    have hne : U ≠ V := by
      intro heq
      have hp : GaussianRealPoint v = 0 := by rw [← hc, heq, sub_self]
      apply hv0
      apply Zsqrtd.ext
      · have he := congrArg Prod.fst hp
        change (v.re : ℝ) = 0 at he
        exact_mod_cast he
      · have he := congrArg Prod.snd hp
        change (v.im : ℝ) = 0 at he
        exact_mod_cast he
    constructor
    · refine ⟨F.base_band, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · simpa using hne
      · intro T hT
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
        rcases hT with rfl | rfl
        · exact hUf
        · exact hVf
      · simpa [List.IsChain, List.isChain_pair, hu] using (show
          ∃ w, UnitTriangularStep orientation w ∧
            TileCentroid V - TileCentroid U = GaussianRealPoint w from ⟨v, hv, hc⟩)
      · intro pre T post heq hpre hpost
        have hlen := congrArg List.length heq
        have hp : 1 ≤ pre.length := List.length_pos_iff.mpr hpre
        have hq : 1 ≤ post.length := List.length_pos_iff.mpr hpost
        simp at hlen
        omega
    · refine ⟨hU, hV, r, t, hr, ht, Or.inl ⟨hu, orientation, v, hv, hc, ?_, ?_⟩⟩
      · exact (congrArg Prod.fst hb).trans hm.1
      · exact (congrArg Prod.snd hb).trans hm.2
  constructor
  · intro hslot
    have hc : p 2 = C.1.1 := by rw [← hqB, ← hslot]; exact F.parent
    have hu : C.1.1.1 = 1 := by
      have he := congrArg Prod.fst hc
      have hp := C.2
      rcases small.1 with h | h <;> omega
    have chart : UnitOccurrenceOrientation q 1 orientation := by
      have h := F.chart hu
      have hrot : UnitOccurrenceOrientation
          ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] 1 orientation := by
        fin_cases a
        · simpa [hslot, eta] using h
        · simpa [hslot] using UnitOccurrenceOrientation.rotate h
        · simpa [hslot] using UnitOccurrenceOrientation.rotate (UnitOccurrenceOrientation.rotate h)
      rw [hstep] at hrot
      exact hrot
    have hi : (a + 1) + 1 = a + 2 := by fin_cases a <;> decide
    rw [hslot, hi, hqD, hqB] at cvL caL
    exact unit_side Rminus J hminus _ F.minusSlope s _ _ hu F.minus_odo hodo
      F.minus_family hfamily F.slope_minus hs (steps.1 orientation chart) cvL caL
      (P4536T1TangentPairMatrix C p hp.1 3 2 (by decide) hc)
  · intro hslot
    have hc : p 3 = C.1.1 := by rw [← hqD, ← hslot]; exact F.parent
    have hu : C.1.1.1 = 1 := by
      have he := congrArg Prod.fst hc
      have hp := C.2
      rcases small.2 with h | h <;> omega
    have chart : UnitOccurrenceOrientation q 2 orientation := by
      have h := F.chart hu
      have hrot : UnitOccurrenceOrientation
          ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] 2 orientation := by
        fin_cases a
        · simpa [hslot, eta] using h
        · simpa [hslot] using UnitOccurrenceOrientation.rotate h
        · simpa [hslot] using UnitOccurrenceOrientation.rotate (UnitOccurrenceOrientation.rotate h)
      rw [hstep] at hrot
      exact hrot
    have hi : (a + 2) + 2 = a + 1 := by fin_cases a <;> decide
    rw [hslot, hi, hqD, hqB] at cvR caR
    apply unit_side J Rplus _ hplus s F.plusSlope _ _ hu hodo F.plus_odo
      hfamily F.plus_family hs F.slope_plus (steps.2 orientation chart) cvR caR
    have hm := P4536T1TangentPairMatrix C p hp.1 2 3 (by decide) hc
    rcases BandVectorOrientationDichotomy (p 3) (p 2)
        ⟨p, hp.1, 3, 2, by decide, rfl, rfl⟩ with ⟨hv, ha⟩ | ⟨hv, ha⟩
    · rw [hv, ha]
      exact hm
    · rw [hv, ha]
      constructor
      · simpa only [Zsqrtd.re_neg, Zsqrtd.im_neg, Int.cast_neg, mul_neg, ← neg_add]
          using congrArg Neg.neg hm.1
      · simpa only [Zsqrtd.re_neg, Zsqrtd.im_neg, Int.cast_neg, mul_neg, ← neg_add]
          using congrArg Neg.neg hm.2

end ApollonianSuperharmonic

end
