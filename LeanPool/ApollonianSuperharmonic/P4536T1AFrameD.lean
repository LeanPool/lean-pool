/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.GaussianRealPointProperties

public import LeanPool.ApollonianSuperharmonic.P4458T1RestrictionFamily
public import LeanPool.ApollonianSuperharmonic.P4536T1EndpointAlgebra
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: P4536T1AFrameD]

/-!
# P4536T1AFrameD

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FrameDiagonalProof

private theorem properRotation (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) (a : Fin 3) :
    let r : Fin 4 → CircleCoordinates := ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
    ProperBandQuadruple r := by
  intro r
  fin_cases a
  · have heq : r = q := by
      funext j
      fin_cases j <;> rfl
    rw [heq]
    exact hq
  · refine ⟨SemiProperQuadruple.rotate hq.1, ?_⟩
    have heq : r = ![q 0, q 2, q 3, q 1] := by
      funext k
      fin_cases k <;> rfl
    rw [heq]
    intro j
    fin_cases j
    · exact hq.2 1
    · exact hq.2 2
    · exact hq.2 0
  · refine ⟨SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1), ?_⟩
    have heq : r = ![q 0, q 3, q 1, q 2] := by
      funext k
      fin_cases k <;> rfl
    rw [heq]
    intro j
    fin_cases j
    · exact hq.2 2
    · exact hq.2 0
    · exact hq.2 1


private theorem centMinus :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3), ∀ (p
        : Fin 4 → CircleCoordinates),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (r 3 = p 3) → ((F.q (F.slot).succ = p 3) → ((F.q 0 = r 0) → (
    let I : GaussianInt := ⟨0, 1⟩
    let wv := BandVectors.1 (r 3) (r 2)
    let xv := BandVectors.1 (r 1) (r 3)
    (BandVectors.1 (r 3) (r 0) = wv - I * xv) → ((BandVectors.1 (r 0) (r 3) = I * BandVectors.1
        (r 3) (r 0)) → (TileCentroid Rminus - TileCentroid F.tile =
      (1 / 2 : ℝ) • GaussianRealPoint ((wv - I * xv) - I * (wv - I * xv))))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a p r r3 hparent hzero I wv xv win vflip'
  have h := F.minus_centroid
  have hindex : F.q F.slot.succ = r 3 := hparent.trans r3.symm
  change TileCentroid Rminus - TileCentroid F.tile =
    (1 / 2 : ℝ) • GaussianRealPoint
      (BandVectors.1 (F.q F.slot.succ) (F.q 0) - BandVectors.1 (F.q 0) (F.q F.slot.succ)) at h
  rw [hindex, hzero] at h
  rw [vflip', win] at h
  simpa using h

private theorem centJ :
    ∀ (C : BandCircle),
      ∀ (orientation : Bool),
        ∀ (base : ProtoTile),
          ∀ (Rminus : ProtoTile),
            ∀ (Rplus : ProtoTile),
              ∀ (hminus : PartialOdometer),
                ∀ (hplus : PartialOdometer),
                  ∀
                    (F :
                      P4458T1BoundaryFrame C orientation base Rminus Rplus hminus
                        hplus),
                    ∀ (D : P4458T1RestrictionFamily F),
                      ∀ (a : Fin 3),
                        ((F.slot = a + 2) →
                          (∀ (J : ProtoTile),
                            (TileCentroid J = TileCentroid (D.tiles F.slot false)) →
                              (let r : Fin 4 → CircleCoordinates :=
                                ![F.q 0, F.q a.succ, F.q (a + 1).succ,
                                  F.q (a + 2).succ];
                              (let I : GaussianInt := ⟨0, 1⟩;
                              let yv := BandVectors.1 (r 2) (r 1);
                              (TileCentroid J - TileCentroid F.tile =
                                (1 / 2 : ℝ) •
                                  GaussianRealPoint (-(yv - I * yv))))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a hslot J hcent r I yv
  have h := (D.occurrences F.slot false).2.2
  have hs2 : F.slot + 2 = a + 1 := by
    rw [hslot]
    fin_cases a <;> decide
  have hs1 : F.slot + 1 = a := by
    rw [hslot]
    fin_cases a <;> decide
  have hindices : F.q ((F.slot + 2).succ) = r 2 ∧ F.q ((F.slot + 1).succ) = r 1 := by
    rw [hs2, hs1]
    constructor <;> rfl
  change TileCentroid (D.tiles F.slot false) - TileCentroid F.tile =
    (-1 : ℝ) • ((1 / 2 : ℝ) •
      (GaussianRealPoint (BandVectors.1 (F.q ((F.slot + 2).succ)) (F.q ((F.slot + 1).succ)) ) -
        (-(GaussianRealPoint (BandVectors.1 (F.q ((F.slot + 2).succ)) (F.q ((F.slot + 1).succ)))).2,
          (GaussianRealPoint (BandVectors.1 (F.q ((F.slot + 2).succ)) (F.q ((F.slot +
              1).succ)))).1))) at h
  rw [hindices.1, hindices.2] at h
  rw [hcent]
  rw [h]
  ext <;> simp [GaussianRealPoint, I, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

private theorem centK :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (D :
        P4458T1RestrictionFamily F), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let wv := BandVectors.1 (r 3) (r 2)
    TileCentroid (D.tiles a true) - TileCentroid F.tile =
      (1 / 2 : ℝ) • GaussianRealPoint (wv - I * wv) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F D a r I wv
  have h := (D.occurrences a true).2.2
  have hindices : F.q ((a + 2).succ) = r 3 ∧ F.q ((a + 1).succ) = r 2 := by
    constructor <;> rfl
  change TileCentroid (D.tiles a true) - TileCentroid F.tile =
    (1 : ℝ) • ((1 / 2 : ℝ) •
      (GaussianRealPoint (BandVectors.1 (F.q ((a + 2).succ)) (F.q ((a + 1).succ))) -
        (-(GaussianRealPoint (BandVectors.1 (F.q ((a + 2).succ)) (F.q ((a + 1).succ)))).2,
          (GaussianRealPoint (BandVectors.1 (F.q ((a + 2).succ)) (F.q ((a + 1).succ)))).1))) at h
  rw [hindices.1, hindices.2] at h
  rw [h]
  ext <;> simp [GaussianRealPoint, I, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

private theorem slopeK :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let wa := BandVectors.2 (r 3) (r 2)
    let e : GaussianInt := -I
    (BandVectors.2 (F.q ((a + 2).succ)) (F.q ((a + 1).succ)) = wa) → (∀ (sA : ℝ × ℝ), (sA.1 -
        F.outerSlope.1 = (if true = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
        ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 : Fin (3 :
        ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q (a + (1 :
        Fin (3 : ℕ))).succ)).im : ℝ))) → ((sA.2 - F.outerSlope.2 = (if true = true then (1 : ℝ)
        else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (a + (2 : Fin (3 : ℕ))).succ) (F.q
        (a + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (F.q (a + (2 : Fin (3 :
        ℕ))).succ) (F.q (a + (1 : Fin (3 : ℕ))).succ)).re : ℝ))) → (sA - F.outerSlope =
      (1 / 2 : ℝ) • GaussianRealPoint (wa - e * wa)))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r I wa e hvecA sA hARe hAIm
  have hre := hARe
  have him := hAIm
  rw [hvecA] at hre him
  change sA.1 - F.outerSlope.1 = 1 * (1 / 2 : ℝ) *
    (((wa.re : ℤ) : ℝ) - ((wa.im : ℤ) : ℝ)) at hre
  change sA.2 - F.outerSlope.2 = 1 * (1 / 2 : ℝ) *
    (((wa.im : ℤ) : ℝ) + ((wa.re : ℤ) : ℝ)) at him
  apply Prod.ext
  · simp [GaussianRealPoint, e, I, Zsqrtd.re_mul, Zsqrtd.im_mul] at hre ⊢
    linarith
  · simp [GaussianRealPoint, e, I, Zsqrtd.re_mul, Zsqrtd.im_mul] at him ⊢
    linarith

private theorem slopeJ :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    let I : GaussianInt := ⟨0, 1⟩
    let ya := BandVectors.2 (r 2) (r 1)
    let e : GaussianInt := -I
    (BandVectors.2 (F.q ((F.slot + 2).succ)) (F.q ((F.slot + 1).succ)) = ya) → (∀ (sJ : ℝ × ℝ),
        (sJ.1 - F.outerSlope.1 = (if false = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
        ((↑(BandVectors.2 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 :
        ℕ))).succ)).re : ℝ) - (↑(BandVectors.2 (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q
        (F.slot + (1 : Fin (3 : ℕ))).succ)).im : ℝ))) → ((sJ.2 - F.outerSlope.2 = (if false =
        true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (F.q (F.slot + (2 :
        Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2
        (F.q (F.slot + (2 : Fin (3 : ℕ))).succ) (F.q (F.slot + (1 : Fin (3 : ℕ))).succ)).re :
        ℝ))) → (sJ - F.outerSlope =
      (1 / 2 : ℝ) • GaussianRealPoint (-(ya - e * ya))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r I ya e hvecJ sJ hJRe hJIm
  have hre := hJRe
  have him := hJIm
  rw [hvecJ] at hre him
  change sJ.1 - F.outerSlope.1 = -1 * (1 / 2 : ℝ) *
    (((ya.re : ℤ) : ℝ) - ((ya.im : ℤ) : ℝ)) at hre
  change sJ.2 - F.outerSlope.2 = -1 * (1 / 2 : ℝ) *
    (((ya.im : ℤ) : ℝ) + ((ya.re : ℤ) : ℝ)) at him
  apply Prod.ext
  · simp [GaussianRealPoint, e, I, Zsqrtd.re_mul, Zsqrtd.im_mul] at hre ⊢
    linarith
  · simp [GaussianRealPoint, e, I, Zsqrtd.re_mul, Zsqrtd.im_mul] at him ⊢
    linarith

private theorem slopeMinusRoot :
    ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (Rminus : ProtoTile), ∀
        (Rplus : ProtoTile), ∀ (hminus : PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (F :
        P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus), ∀ (a : Fin 3),
    let r : Fin 4 → CircleCoordinates :=
      ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
    (F.q F.slot.succ = r 3) → ((F.q 0 = r 0) → (
    let I : GaussianInt := ⟨0, 1⟩
    let wa := BandVectors.2 (r 3) (r 2)
    let xa := BandVectors.2 (r 1) (r 3)
    (BandVectors.2 (r 3) (r 0) = wa + I * xa) → ((BandVectors.2 (r 0) (r 3) = -I * BandVectors.2
        (r 3) (r 0)) → (
    let e : GaussianInt := -I
    F.minusSlope - F.outerSlope =
      (1 / 2 : ℝ) • GaussianRealPoint ((wa - e * xa) - e * (wa - e * xa)))))) := by
  classical
  intro C orientation base Rminus Rplus hminus hplus F a r hparentR hzero I wa xa ain aflip' e
  have h := F.minus_difference
  change F.minusSlope - F.outerSlope = (1 / 2 : ℝ) • GaussianRealPoint
    (BandVectors.2 (F.q F.slot.succ) (F.q 0) -
      BandVectors.2 (F.q 0) (F.q F.slot.succ)) at h
  rw [hparentR, hzero, aflip', ain] at h
  simpa [e, I] using h

private theorem reverseQuarterTurn {u v : GaussianInt} (t : GaussianInt)
    (ht : t * t = -1) (h : u = t * v) : v = -t * u := by
  rw [h, ← mul_assoc, neg_mul, ht]
  simp

end FrameDiagonalProof

theorem P4536T1AFrameD
    {C : BandCircle} {orientation : Bool} {base Rminus Rplus : ProtoTile}
    {hminus hplus : PartialOdometer}
    (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus)
    (D : P4458T1RestrictionFamily F)
    (a : Fin 3) (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
    (hstep : ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] =
      ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
        p 0, p 2, p 3])
    (hslot : F.slot = a + 2)
    (hchart : C.1.1.1 = 1 → UnitOccurrenceOrientation p 2 orientation)
    (J : ProtoTile) (hfamily : J ∈ RegularTileFamily base (TilingLattice C))
    (hodo : TileOdometer C.1.1 J (D.functions F.slot false))
    (hcent : TileCentroid J = TileCentroid (D.tiles F.slot false)) :
    ∃ G : P4458T1BoundaryFrame C orientation base Rminus J
        hminus (D.functions F.slot false),
      G.q = p ∧ G.slot = 2 ∧ G.outer.1.1 = F.q a.succ ∧
      G.tile = D.tiles a true ∧ G.odometer = D.functions a true := by
-- BODY
  classical
  let r : Fin 4 → CircleCoordinates :=
    ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ]
  have hr := FrameDiagonalProof.properRotation F.q F.proper a
  have hrstep : r = ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
      2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2), p 0, p 2, p 3] := hstep
  have r1 : r 1 = p 0 := by simpa using congrFun hrstep 1
  have r3 : r 3 = p 3 := by simpa using congrFun hrstep 3
  have hparent : F.q F.slot.succ = p 3 := by
    rw [hslot]
    simpa using congrFun hstep 3
  have hparentR := hparent.trans r3.symm
  have hzero : F.q 0 = r 0 := rfl
  have hC := F.parent.symm.trans hparent
  have positiveA := (ProperBandCurvatureStructure p hp).1
  let I : GaussianInt := ⟨0, 1⟩
  let wv := BandVectors.1 (r 3) (r 2)
  let xv := BandVectors.1 (r 1) (r 3)
  let yv := BandVectors.1 (r 2) (r 1)
  let wa := BandVectors.2 (r 3) (r 2)
  let xa := BandVectors.2 (r 1) (r 3)
  let ya := BandVectors.2 (r 2) (r 1)
  have laws := VectorRecursionLaws r hr.1
  have hrr := FrameDiagonalProof.properRotation r hr 2
  have lawsR := VectorRecursionLaws _ hrr.1
  have win : BandVectors.1 (r 3) (r 0) = wv - I * xv := by
    simpa [wv, xv, I] using lawsR.2.2.1
  have ain : BandVectors.2 (r 3) (r 0) = wa + I * xa := by
    simpa [wa, xa, I] using lawsR.2.2.2.1
  have hI2 : I * I = -1 := by decide +kernel
  have hv := P4536T1EndpointAlgebra I wv xv yv hI2 laws.1
  have ha := P4536T1EndpointAlgebra (-I) wa xa ya (by decide +kernel) laws.2.1
  have vflip := (laws.2.2.2.2 hr) 2
  have vflip' : BandVectors.1 (r 0) (r 3) = I * BandVectors.1 (r 3) (r 0) := vflip.1
  have aflip' : BandVectors.2 (r 0) (r 3) = -I * BandVectors.2 (r 3) (r 0) := vflip.2
  have centMinus := FrameDiagonalProof.centMinus C orientation base Rminus Rplus hminus hplus
    F a p r3 hparent hzero win vflip'
  have centJ := FrameDiagonalProof.centJ C orientation base Rminus Rplus hminus hplus
    F D a hslot J hcent
  have centK := FrameDiagonalProof.centK C orientation base Rminus Rplus hminus hplus F D a
  have hcentR := GaussianRealPointProperties.relativeDifference (1 / 2) centMinus centK hv.2.2.2.2.1
  have hcentJ := GaussianRealPointProperties.relativeDifference (1 / 2) centJ centK hv.2.2.2.2.2.1
  let e : GaussianInt := -I
  have lawsP := VectorRecursionLaws p hp.1
  have pflip := (lawsP.2.2.2.2 hp) 2
  have hxcoordV : BandVectors.1 (p 0) (p 3) = xv := by rw [← r1, ← r3]
  have hxcoordA : BandVectors.2 (p 0) (p 3) = xa := by rw [← r1, ← r3]
  have he2 : e * e = -1 := by decide +kernel
  have hxv : xv = I * BandVectors.1 (p 3) (p 0) := by
    rw [← hxcoordV]
    exact pflip.1
  have hza := FrameDiagonalProof.reverseQuarterTurn I hI2 hxv
  have hxa : xa = e * BandVectors.2 (p 3) (p 0) := by
    rw [← hxcoordA]
    simpa [e, I] using pflip.2
  have hzaA := FrameDiagonalProof.reverseQuarterTurn e he2 hxa
  have hminusVecV : BandVectors.1 (p 3) (p 0) - BandVectors.1 (p 0) (p 3) =
      -I * xv - xv := by rw [hza, hxcoordV]
  have hplusVecV : BandVectors.1 (p 3) (p 0) + BandVectors.1 (p 0) (p 3) =
      -I * xv + xv := by rw [hza, hxcoordV]
  have hminusVecA : BandVectors.2 (p 3) (p 0) - BandVectors.2 (p 0) (p 3) =
      -e * xa - xa := by rw [hzaA, hxcoordA]
  have hplusVecA : BandVectors.2 (p 3) (p 0) + BandVectors.2 (p 0) (p 3) =
      -e * xa + xa := by rw [hzaA, hxcoordA]
  have houterA : F.q a.succ = p 0 := r1
  let A : BandCircle := ⟨⟨p 0, Or.inl positiveA, p, hp.1, 0, rfl⟩, positiveA⟩
  have hvecA : BandVectors.2 (F.q ((a + 2).succ)) (F.q ((a + 1).succ)) = wa := rfl
  have hslotplus2 : F.slot + 2 = a + 1 := by rw [hslot]; fin_cases a <;> decide
  have hslotplus1 : F.slot + 1 = a := by rw [hslot]; fin_cases a <;> decide
  have hvecJ : BandVectors.2 (F.q ((F.slot + 2).succ))
      (F.q ((F.slot + 1).succ)) = ya := by
    rw [hslotplus2, hslotplus1]
    rfl
  have hpositiveSlot : 0 < (F.q F.slot.succ).1 := by rw [F.parent]; exact C.2
  obtain hzA | ⟨rootA, sA, hrootA, hsA, hARe, hAIm⟩ := D.slopes a true
  · rw [houterA] at hzA
    omega
  have hrootAEq := Option.some.inj (hrootA.symm.trans F.slope_outer)
  subst rootA
  obtain hzJ | ⟨rootJ, sJ, hrootJ, hsJ, hJRe, hJIm⟩ := D.slopes F.slot false
  · omega
  have hrootJEq := Option.some.inj (hrootJ.symm.trans F.slope_outer)
  subst rootJ
  have slopeK := FrameDiagonalProof.slopeK C orientation base Rminus Rplus hminus hplus
    F a hvecA sA hARe hAIm
  have slopeJ := FrameDiagonalProof.slopeJ C orientation base Rminus Rplus hminus hplus
    F a hvecJ sJ hJRe hJIm
  have slopeMinusRoot := FrameDiagonalProof.slopeMinusRoot C orientation base Rminus Rplus
    hminus hplus F a hparentR hzero ain aflip'
  have slopeMinusA :=
    GaussianRealPointProperties.relativeDifference (1 / 2) slopeMinusRoot slopeK ha.2.2.2.2.1
  have slopeJminusA :=
    GaussianRealPointProperties.relativeDifference (1 / 2) slopeJ slopeK ha.2.2.2.2.2.1
  have hodoA : TileOdometer (p 0) (D.tiles a true) (D.functions a true) := by
    simpa [houterA] using D.odometers a true
  let G : P4458T1BoundaryFrame C orientation base Rminus J hminus
      (D.functions F.slot false) := {
    outer := A
    q := p
    proper := hp
    slot := 2
    child := rfl
    parent := hC.symm
    tile := D.tiles a true
    odometer := D.functions a true
    outer_odo := by
      simpa [A] using hodoA
    minus_odo := F.minus_odo
    plus_odo := hodo
    outer_band := by
      simpa [A] using TileOdometerBandPrototile _ _ _ hodoA
    base_band := F.base_band
    minus_family := F.minus_family
    plus_family := hfamily
    chart := hchart
    minus_centroid := by
      change TileCentroid Rminus - TileCentroid (D.tiles a true) =
        (1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.1 (p 3) (p 0) - BandVectors.1 (p 0) (p 3))
      rw [hminusVecV]
      exact hcentR
    plus_centroid := by
      change TileCentroid J - TileCentroid (D.tiles a true) =
        (1 / 2 : ℝ) • GaussianRealPoint
          (BandVectors.1 (p 3) (p 0) + BandVectors.1 (p 0) (p 3))
      rw [hplusVecV]
      exact hcentJ
    outerSlope := sA
    minusSlope := F.minusSlope
    plusSlope := sJ
    slope_outer := hsA
    slope_minus := F.slope_minus
    slope_plus := hsJ
    minus_difference := by
      have h : BandVectors.2 (p (2 : Fin 3).succ) (p 0) -
          BandVectors.2 (p 0) (p (2 : Fin 3).succ) = -e * xa - xa := by
        simpa [e, xa] using hminusVecA
      rw [h]
      exact slopeMinusA
    plus_difference := by
      have h : BandVectors.2 (p (2 : Fin 3).succ) (p 0) +
          BandVectors.2 (p 0) (p (2 : Fin 3).succ) = -e * xa + xa := by
        simpa [e, xa] using hplusVecA
      rw [h]
      exact slopeJminusA
  }
  refine ⟨G, rfl, rfl, ?_, rfl, rfl⟩
  exact houterA.symm

end ApollonianSuperharmonic

end
