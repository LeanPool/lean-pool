/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandPrototileNonempty

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralOdometerRowData
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileOdometerCovariance
public import LeanPool.ApollonianSuperharmonic.PartialOdometerAffineTranslateFormulas
public import LeanPool.ApollonianSuperharmonic.P5472T1AffineDifferenceTransport
public import LeanPool.ApollonianSuperharmonic.FordFareyParameter
public import LeanPool.ApollonianSuperharmonic.FordCircleCoordinate

-- [TABLET NODE: P5472T1FordSlopeDifference]

/-!
# P5472T1FordSlopeDifference

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5472T1FordSlopeDifference
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C0 : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C0 T)
    (h : PartialOdometer)
    (P : Fin 3 → Bool → ProtoTile)
    (r : Fin 3 → Bool → PartialOdometer)
    (Q S : Fin 3 → Bool → ProtoTile)
    (u v : Fin 3 → Bool → PartialOdometer)
    (g : IntegerLatticeFunction) (x : GaussianInt)
    (data : BandOrderedGeneralOdometerRowData q cfg C0 T cert h P r Q S u v g)
    (F : FordFareyParameter) (s : BandPackingSymmetry) (delta : Bool)
    (hword : ∃ z : GaussianInt, s = .shift z ∨ s = (BandPackingSymmetry.shift z).comp .negate)
    (hrootCircle : BandPackingSymmetryCircleAction s (q 1) = FordCircleCoordinate F.p F.q)
    (hA : BandVectors.2 (BandPackingSymmetryQuadrupleAction s q 3)
      (BandPackingSymmetryQuadrupleAction s q 2) = ⟨F.p₂, -F.p₁⟩)
    (hcyclic :
      let I : GaussianInt := ⟨0, 1⟩
      let W := BandVectors.1 (q 3) (q 2)
      let A := BandVectors.2 (q 3) (q 2)
      let A' := BandVectors.2 (BandPackingSymmetryQuadrupleAction s q 3)
        (BandPackingSymmetryQuadrupleAction s q 2)
      (BandPackingSymmetryAffineVectorAction s (W - I * W, A + I * A)).2 =
        if delta then -(A' + I * A') else A' + I * A') :
    let c := BandPackingSymmetryVectorAction s x
    let hp := PartialOdometerAffineTranslate
      (BandPackingSymmetryPartialOdometerAction s (r 0 (!delta))) (-c) 0 0
    let hm := PartialOdometerAffineTranslate
      (BandPackingSymmetryPartialOdometerAction s (r 0 delta)) (-c) 0 0
    ∃ sp sm : Real × Real,
      PartialOdometerSlope hp = some sp ∧ PartialOdometerSlope hm = some sm ∧
      sm.1 - sp.1 = -(F.p : Real) ∧ sm.2 - sp.2 = (F.p₁ : Real) - F.p₂ := by
-- BODY
  have hcurvSym : ∀ a C, (BandPackingSymmetryCircleAction a C).1 = C.1 := by
    intro a
    induction a <;> intro C <;>
      simp [BandPackingSymmetryCircleAction, *]
  have hq1pos : 0 < (q 1).1 := by
    have hh := congrArg Prod.fst hrootCircle
    rw [hcurvSym] at hh
    simp only [Fin.isValue, FordCircleCoordinate, Nat.cast_mul, Int.reduceNeg] at hh
    have : 0 < F.q * F.q := Nat.mul_pos F.q_pos F.q_pos
    omega
  let Wsource : GaussianInt := BandVectors.1 (q 3) (q 2)
  let Asource : GaussianInt := BandVectors.2 (q 3) (q 2)
  have hrawSlope (b : Bool) :
      ∃ p pi : Real × Real,
        PartialOdometerSlope h = some p ∧
        PartialOdometerSlope (r 0 b) = some pi ∧
        pi.1 - p.1 = (if b then (1 : Real) else -1) * (1 / 2) *
          (((Asource.re : Int) : Real) - ((Asource.im : Int) : Real)) ∧
        pi.2 - p.2 = (if b then (1 : Real) else -1) * (1 / 2) *
          (((Asource.im : Int) : Real) + ((Asource.re : Int) : Real)) := by
    rcases data.hPslope 0 b with hz | hslope
    · exact (ne_of_gt hq1pos hz).elim
    · simpa [Asource] using hslope
  let Icyc : GaussianInt := ⟨0, 1⟩
  let vcyc : GaussianInt := Wsource - Icyc * Wsource
  let acyc : GaussianInt := Asource + Icyc * Asource
  have hWreal : GaussianRealPoint vcyc = GaussianRealPoint Wsource -
      (-(GaussianRealPoint Wsource).2, (GaussianRealPoint Wsource).1) := by
    change GaussianRealPoint (Wsource - Icyc * Wsource) = _
    cases Wsource with
    | mk wr wi =>
        ext <;> simp [Icyc, GaussianRealPoint]
  have hAreal : GaussianRealPoint acyc =
      ((((Asource.re : Int) : Real) - ((Asource.im : Int) : Real)),
        (((Asource.im : Int) : Real) + ((Asource.re : Int) : Real))) := by
    change GaussianRealPoint (Asource + Icyc * Asource) = _
    cases Asource with
    | mk ar ai =>
        ext <;> simp [Icyc, GaussianRealPoint]; ring
  have hcentSource (b : Bool) :
      TileCentroid (P 0 b) - TileCentroid T =
        (if b then (1 / 2 : Real) else -(1 / 2 : Real)) •
          GaussianRealPoint vcyc := by
    have hh := data.hPcent 0 b
    have hh' : TileCentroid (P 0 b) - TileCentroid T =
        (if b then (1 : Real) else -1) • ((1 / 2 : Real) •
          (GaussianRealPoint Wsource -
            (-(GaussianRealPoint Wsource).2, (GaussianRealPoint Wsource).1))) := by
      simpa [Wsource] using hh
    rw [← hWreal] at hh'
    cases b <;> simpa [smul_smul, smul_eq_mul] using hh'
  have hslopeSource (b : Bool) :
      ∃ p pi : Real × Real,
        PartialOdometerSlope h = some p ∧
        PartialOdometerSlope (r 0 b) = some pi ∧
        pi - p = (if b then (1 / 2 : Real) else -(1 / 2 : Real)) •
          GaussianRealPoint acyc := by
    obtain ⟨p, pi, hp, hpi, hdx, hdy⟩ := hrawSlope b
    refine ⟨p, pi, hp, hpi, ?_⟩
    apply Prod.ext
    · cases b <;> simpa [hAreal, smul_eq_mul] using hdx
    · cases b <;> simpa [hAreal, smul_eq_mul] using hdy
  have positiveCells := BandPrototileNonempty.positive
  have hTne := positiveCells (q 0) T (ProperBandCurvatureStructure q cfg.proper).1
    data.hPband
  have hsigned (b : Bool) :
      ∃ p pi : Real × Real,
        PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction s h) = some p ∧
        PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction s (r 0 b)) = some pi ∧
        pi - p = (if b then (1 / 2 : Real) else -(1 / 2 : Real)) •
          GaussianRealPoint (BandPackingSymmetryAffineVectorAction s (vcyc, acyc)).2 := by
    obtain ⟨p, pi, hp, hpi, hd⟩ := hslopeSource b
    have hn := positiveCells (q 1) (P 0 b) hq1pos
      (TileOdometerBandPrototile _ _ _ (data.hP 0 b))
    have hroot := (BandPackingSymmetryTileOdometerCovariance s (q 0) T h
      data.hroot).2.2 hTne
    have hchild := (BandPackingSymmetryTileOdometerCovariance s (q 1) (P 0 b)
      (r 0 b) (data.hP 0 b)).2.2 hn
    rw [hp] at hroot
    rw [hpi] at hchild
    refine ⟨BandPackingSymmetrySlopeAction s T p,
      BandPackingSymmetrySlopeAction s (P 0 b) pi, hroot, hchild, ?_⟩
    exact (P5472T1AffineDifferenceTransport s hword T (P 0 b) pi p
      vcyc acyc _ (hcentSource b) hd).2
  obtain ⟨p, sp, hp, hsp, dp⟩ := hsigned (!delta)
  obtain ⟨p', sm, hp', hsm, dm⟩ := hsigned delta
  have ep : p' = p := Option.some.inj (hp'.symm.trans hp)
  subst p'
  refine ⟨sp, sm, ?_, ?_, ?_, ?_⟩
  · rw [(PartialOdometerAffineTranslateFormulas _ _ _ _).2.2.2.2.2, hsp]
    simp
  · rw [(PartialOdometerAffineTranslateFormulas _ _ _ _).2.2.2.2.2, hsm]
    simp
  · have hpair := hcyclic
    change (BandPackingSymmetryAffineVectorAction s (vcyc, acyc)).2 = _ at hpair
    rw [hA] at hpair
    have dp1 := congrArg Prod.fst dp
    have dm1 := congrArg Prod.fst dm
    rw [hpair] at dp1 dm1
    cases delta <;>
      simp [GaussianRealPoint] at dp1 dm1  <;>
      have hsum : (F.p : Real) = (F.p₁ : Real) + F.p₂ := by exact_mod_cast F.sum_p
    all_goals linarith
  · have hpair := hcyclic
    change (BandPackingSymmetryAffineVectorAction s (vcyc, acyc)).2 = _ at hpair
    rw [hA] at hpair
    have dp2 := congrArg Prod.snd dp
    have dm2 := congrArg Prod.snd dm
    rw [hpair] at dp2 dm2
    cases delta <;>
      simp [GaussianRealPoint] at dp2 dm2  <;>
      linarith

end ApollonianSuperharmonic

end
