/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4458T1RestrictionFamily
public import LeanPool.ApollonianSuperharmonic.P4536T1EndpointAlgebra
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: P4549T1DeeperFrameB]

/-!
# P4549T1DeeperFrameB

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4549T1DeeperFrameB
    {C : BandCircle} {orientation : Bool} {base Rminus Rplus : ProtoTile}
    {hminus hplus : PartialOdometer}
    (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus)
    (D : P4458T1RestrictionFamily F)
    (a : Fin 3) (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
    (hstep : ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] =
      ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
        p 0, p 2, p 3])
    (hslot : F.slot = a + 1)
    (t : Fin 4 → CircleCoordinates) (ht : ProperBandQuadruple t)
    (ht0 : t 0 = p 3) (ht1 : t 1 = p 2)
    (hchart : C.1.1.1 = 1 → UnitOccurrenceOrientation t 0 orientation)
    (J : ProtoTile) (hfamily : J ∈ RegularTileFamily base (TilingLattice C))
    (hodo : TileOdometer C.1.1 J (D.functions F.slot false))
    (hcent : TileCentroid J = TileCentroid (D.tiles F.slot false)) :
    ∃ G : P4458T1BoundaryFrame C orientation base Rminus J
        hminus (D.functions F.slot false),
      G.q = t ∧ G.slot = 0 ∧ G.outer.1.1 = F.q (a + 2).succ ∧
      G.tile = D.tiles (a + 2) true ∧ G.odometer = D.functions (a + 2) true := by
-- BODY
  have hqA : F.q a.succ = p 0 := by simpa using congrFun hstep 1
  have hqB : F.q (a + 1).succ = p 2 := by simpa using congrFun hstep 2
  have hqE : F.q (a + 2).succ = p 3 := by simpa using congrFun hstep 3
  have hparent : t 1 = C.1.1 := by rw [ht1, ← hqB, ← hslot]; exact F.parent
  have hEpos : 0 < (p 3).1 := ht0 ▸ (ProperBandCurvatureStructure t ht).1
  have hEpos' : 0 < (F.q (a + 2).succ).1 := hqE.symm ▸ hEpos
  have hBpos : 0 < (F.q F.slot.succ).1 := F.parent ▸ C.2
  have idx1 : a + 2 + 1 = a := by fin_cases a <;> rfl
  have idx2 : a + 2 + 2 = a + 1 := by fin_cases a <;> rfl
  have idx3 : a + 1 + 1 = a + 2 := by fin_cases a <;> rfl
  have idx4 : a + 1 + 2 = a := by fin_cases a <;> rfl
  let r : Fin 4 → CircleCoordinates :=
    ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
  have hr : SemiProperQuadruple r := by
    dsimp [r]
    rw [hstep]
    exact SemiProperQuadruple.successor hp.1
  let I : GaussianInt := ⟨0, 1⟩
  let w := BandVectors.1 (p 3) (p 2)
  let x := BandVectors.1 (p 0) (p 3)
  let y := BandVectors.1 (p 2) (p 0)
  let z := BandVectors.1 (p 2) (p 3)
  let wa := BandVectors.2 (p 3) (p 2)
  let xa := BandVectors.2 (p 0) (p 3)
  let ya := BandVectors.2 (p 2) (p 0)
  let za := BandVectors.2 (p 2) (p 3)
  have laws := VectorRecursionLaws r hr
  have rotated := VectorRecursionLaws _ (SemiProperQuadruple.rotate hr)
  have vrec : BandVectors.1 (F.q F.slot.succ) (F.q 0) = y - I * w := by
    simpa [r, hslot, hqA, hqB, hqE, y, w, I] using rotated.2.2.1
  have arec : BandVectors.2 (F.q F.slot.succ) (F.q 0) = ya - (-I) * wa := by
    simpa [r, hslot, hqA, hqB, hqE, ya, wa, I, neg_mul] using rotated.2.2.2.1
  have vflip := ((VectorRecursionLaws F.q F.proper.1).2.2.2.2 F.proper F.slot).1
  have aflip := ((VectorRecursionLaws F.q F.proper.1).2.2.2.2 F.proper F.slot).2
  have vw : w = I * z := by
    simpa [w, z, ht0, ht1, I] using
      ((VectorRecursionLaws t ht.1).2.2.2.2 ht 0).1
  have aw : wa = (-I) * za := by
    simpa [wa, za, ht0, ht1, I] using
      ((VectorRecursionLaws t ht.1).2.2.2.2 ht 0).2
  have offsets (e w x y z : GaussianInt) (he : e ^ 2 = -1)
      (hs : w + x + y = 0) (hf : w = e * z) :
      ((y - e * w) - e * (y - e * w) - (y - e * y) = z - w) ∧
      (-(x - e * x) - (y - e * y) = z + w) := by
    have hz : z = -e * w := by
      rw [hf]
      linear_combination z * he
    have h := P4536T1EndpointAlgebra e w x y he hs
    constructor
    · rw [hz]; exact h.2.2.2.2.2.2.1
    · rw [hz]; exact h.2.2.2.2.2.2.2.1
  have hv := offsets I w x y z (by decide +kernel)
    (by simpa [r, hqA, hqB, hqE, w, x, y] using laws.1) vw
  have ha := offsets (-I) wa xa ya za (by decide +kernel)
    (by simpa [r, hqA, hqB, hqE, wa, xa, ya] using laws.2.1) aw
  have half_sub (A B H : GaussianInt) (h : A - B = H) :
      (1 / 2 : ℝ) • GaussianRealPoint A - (1 / 2 : ℝ) • GaussianRealPoint B =
        (1 / 2 : ℝ) • GaussianRealPoint H := by
    rw [← h]
    ext <;> simp [GaussianRealPoint] <;> ring
  have vm : TileCentroid Rminus - TileCentroid F.tile = (1 / 2 : ℝ) •
      GaussianRealPoint ((y - I * w) - I * (y - I * w)) := by
    rw [F.minus_centroid, vflip, vrec]
  have vn : TileCentroid J - TileCentroid F.tile =
      (1 / 2 : ℝ) • GaussianRealPoint (-(x - I * x)) := by
    rw [hcent]
    have h := (D.occurrences F.slot false).2.2
    rw [hslot, idx3, idx4, hqA, hqE] at h
    change TileCentroid (D.tiles F.slot false) - TileCentroid F.tile = _
    rw [hslot, h]
    ext <;> simp [GaussianRealPoint, x, I, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
  have ve : TileCentroid (D.tiles (a + 2) true) - TileCentroid F.tile =
      (1 / 2 : ℝ) • GaussianRealPoint (y - I * y) := by
    have h := (D.occurrences (a + 2) true).2.2
    rw [idx1, idx2, hqA, hqB] at h
    rw [h]
    ext <;> simp [GaussianRealPoint, y, I, Zsqrtd.re_mul, Zsqrtd.im_mul]
  rcases D.slopes F.slot false with hz | ⟨root, sJ, hroot, hsJ, hre, him⟩
  · omega
  have hrootEq : root = F.outerSlope := Option.some.inj (hroot.symm.trans F.slope_outer)
  subst root
  have an : sJ - F.outerSlope =
      (1 / 2 : ℝ) • GaussianRealPoint (-(xa - (-I) * xa)) := by
    rw [hslot, idx3, idx4, hqA, hqE] at hre him
    apply Prod.ext <;>
      simp [GaussianRealPoint, xa, I, Zsqrtd.re_mul, Zsqrtd.im_mul] at hre him ⊢ <;>
      linarith
  rcases D.slopes (a + 2) true with hz | ⟨root, sE, hroot, hsE, hre, him⟩
  · omega
  have hrootEq : root = F.outerSlope := Option.some.inj (hroot.symm.trans F.slope_outer)
  subst root
  have ae : sE - F.outerSlope =
      (1 / 2 : ℝ) • GaussianRealPoint (ya - (-I) * ya) := by
    rw [idx1, idx2, hqA, hqB] at hre him
    apply Prod.ext <;>
      simp [GaussianRealPoint, ya, I, Zsqrtd.re_mul, Zsqrtd.im_mul] at hre him ⊢ <;>
      linarith
  have am : F.minusSlope - F.outerSlope = (1 / 2 : ℝ) •
      GaussianRealPoint ((ya - (-I) * wa) - (-I) * (ya - (-I) * wa)) := by
    rw [F.minus_difference, aflip, arec]
  have vmE : TileCentroid Rminus - TileCentroid (D.tiles (a + 2) true) =
      (1 / 2 : ℝ) • GaussianRealPoint (z - w) := by
    calc
      _ = (TileCentroid Rminus - TileCentroid F.tile) -
          (TileCentroid (D.tiles (a + 2) true) - TileCentroid F.tile) := by abel
      _ = _ := by rw [vm, ve]; exact half_sub _ _ _ hv.1
  have vnE : TileCentroid J - TileCentroid (D.tiles (a + 2) true) =
      (1 / 2 : ℝ) • GaussianRealPoint (z + w) := by
    calc
      _ = (TileCentroid J - TileCentroid F.tile) -
          (TileCentroid (D.tiles (a + 2) true) - TileCentroid F.tile) := by abel
      _ = _ := by rw [vn, ve]; exact half_sub _ _ _ hv.2
  have amE : F.minusSlope - sE =
      (1 / 2 : ℝ) • GaussianRealPoint (za - wa) := by
    calc
      _ = (F.minusSlope - F.outerSlope) - (sE - F.outerSlope) := by abel
      _ = _ := by rw [am, ae]; exact half_sub _ _ _ ha.1
  have anE : sJ - sE = (1 / 2 : ℝ) • GaussianRealPoint (za + wa) := by
    calc
      _ = (sJ - F.outerSlope) - (sE - F.outerSlope) := by abel
      _ = _ := by rw [an, ae]; exact half_sub _ _ _ ha.2
  let outer : BandCircle :=
    ⟨⟨p 3, Or.inl hEpos, t, ht.1, 0, ht0⟩, hEpos⟩
  have houterOdo : TileOdometer (p 3) (D.tiles (a + 2) true)
      (D.functions (a + 2) true) := hqE ▸ D.odometers (a + 2) true
  refine ⟨{
    outer := outer
    q := t
    proper := ht
    slot := 0
    child := ht0
    parent := hparent
    tile := D.tiles (a + 2) true
    odometer := D.functions (a + 2) true
    outer_odo := houterOdo
    minus_odo := F.minus_odo
    plus_odo := hodo
    outer_band := TileOdometerBandPrototile _ _ _ houterOdo
    base_band := F.base_band
    minus_family := F.minus_family
    plus_family := hfamily
    chart := hchart
    minus_centroid := by simpa only [Fin.succ_zero_eq_one, ht0, ht1, z, w] using vmE
    plus_centroid := by simpa only [Fin.succ_zero_eq_one, ht0, ht1, z, w] using vnE
    outerSlope := sE
    minusSlope := F.minusSlope
    plusSlope := sJ
    slope_outer := hsE
    slope_minus := F.slope_minus
    slope_plus := hsJ
    minus_difference := by simpa only [Fin.succ_zero_eq_one, ht0, ht1, za, wa] using amE
    plus_difference := by simpa only [Fin.succ_zero_eq_one, ht0, ht1, za, wa] using anE
  }, rfl, rfl, hqE.symm, rfl, rfl⟩

end ApollonianSuperharmonic

end
