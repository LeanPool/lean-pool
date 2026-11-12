/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandRegimeClassification
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryProperCovariance
public import LeanPool.ApollonianSuperharmonic.SemiProperQuadruple

-- [TABLET NODE: P4261T2PairNormalization]

/-!
# P4261T2PairNormalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4261T2PairNormalization
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (C D : BandCircle) (i : Fin 3) (e : Bool)
    (hC : q 0 = C.1.1) (hD : q i.succ = D.1.1)
    (T U : ProtoTile) (h k : PartialOdometer)
    (hh : TileOdometer C.1.1 T h) (hk : TileOdometer C.1.1 U k)
    (p r : Real × Real)
    (hp : PartialOdometerSlope h = some p) (hr : PartialOdometerSlope k = some r)
    (hc : TileCentroid U - TileCentroid T =
      (if e = true then (1 : Real) else -1) •
        GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)))
    (hs : r - p = (if e = true then (1 : Real) else -1) •
      GaussianRealPoint (BandVectors.2 (q i.succ) (q 0))) :
    ∃ (g : BandPackingSymmetry) (qn : Fin 4 → CircleCoordinates)
      (Cn Dn : BandCircle) (j : Fin 3) (en : Bool) (pn rn : Real × Real),
      ProperBandQuadruple qn ∧ qn 0 = Cn.1.1 ∧ qn j.succ = Dn.1.1 ∧
      Cn.1.1 = BandPackingSymmetryCircleAction g C.1.1 ∧
      Dn.1.1 = BandPackingSymmetryCircleAction g D.1.1 ∧
      Cn.1.1.1 = C.1.1.1 ∧ Dn.1.1.1 = D.1.1.1 ∧
      TileOdometer Cn.1.1 (BandPackingSymmetryTileAction g T)
        (BandPackingSymmetryPartialOdometerAction g h) ∧
      TileOdometer Cn.1.1 (BandPackingSymmetryTileAction g U)
        (BandPackingSymmetryPartialOdometerAction g k) ∧
      PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g h) = some pn ∧
      PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g k) = some rn ∧
      TileCentroid (BandPackingSymmetryTileAction g U) -
          TileCentroid (BandPackingSymmetryTileAction g T) =
        (if en = true then (1 : Real) else -1) •
          GaussianRealPoint (BandVectors.1 (qn j.succ) (qn 0)) ∧
      rn - pn = (if en = true then (1 : Real) else -1) •
        GaussianRealPoint (BandVectors.2 (qn j.succ) (qn 0)) ∧
      ((∃ P : FordFareyParameter, 1 < P.q ∧ qn = FordRecursiveQuadruple P) ∨
        (∃ K : DiamondParameter, 1 < K.1 ∧ qn = DiamondRecursiveQuadruple K) ∨
        Nonempty (BandOrderedGeneralConfiguration qn)) := by
-- BODY
  classical
  obtain ⟨a, g, hregime⟩ := BandRegimeClassification q hq
  let qa : Fin 4 → CircleCoordinates :=
    ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
  have hqa : ProperBandQuadruple qa := by
    fin_cases a
    · have heq : qa = q := by funext j; fin_cases j <;> rfl
      rwa [heq]
    · refine ⟨by simpa [qa] using SemiProperQuadruple.rotate hq.1, ?_⟩
      intro j
      fin_cases j
      · exact hq.2 1
      · exact hq.2 2
      · exact hq.2 0
    · refine ⟨by simpa [qa] using (SemiProperQuadruple.rotate
          (SemiProperQuadruple.rotate hq.1)), ?_⟩
      intro j
      fin_cases j
      · exact hq.2 2
      · exact hq.2 0
      · exact hq.2 1
  have hqa0 : qa 0 = C.1.1 := hC
  have hqa00 : qa 0 = q 0 := rfl
  have hqai : qa (i - a).succ = q i.succ := by
    fin_cases a <;> fin_cases i <;> rfl
  have hc' : TileCentroid U - TileCentroid T =
      (if e = true then (1 : Real) else -1) •
        GaussianRealPoint (BandVectors.1 (qa (i - a).succ) (qa 0)) := by
    simpa only [hqai, hqa00] using hc
  have hs' : r - p = (if e = true then (1 : Real) else -1) •
      GaussianRealPoint (BandVectors.2 (qa (i - a).succ) (qa 0)) := by
    simpa only [hqai, hqa00] using hs
  obtain ⟨negative, pn, rn, hphase, hTn, hUn, hpn, hrn, hcn, hsn, htn, _⟩ :=
    LeftLatticeAdjacentPackingSymmetryTransport g qa hqa (i - a) e T U h k p r
      (by simpa only [hqa0] using hh) (by simpa only [hqa0] using hk)
      hp hr hc' (congrArg Prod.fst hs') (congrArg Prod.snd hs')
  let qn := BandPackingSymmetryQuadrupleAction g qa
  let j : Fin 3 := if BandPackingSymmetryReversesOrientation g then -(i - a) else i - a
  have hqn : ProperBandQuadruple qn := BandPackingSymmetryProperCovariance g qa hqa
  have hroot : qn 0 = BandPackingSymmetryCircleAction g C.1.1 := by
    simp [qn, BandPackingSymmetryQuadrupleAction, hqa0]
  have hparent : qn j.succ = BandPackingSymmetryCircleAction g D.1.1 := by
    have hrev : ∀ n : Fin 3,
        (if BandPackingSymmetryReversesOrientation g then
            -(if BandPackingSymmetryReversesOrientation g then -n else n)
          else (if BandPackingSymmetryReversesOrientation g then -n else n)) = n := by
      intro n
      cases BandPackingSymmetryReversesOrientation g <;> simp
    have hidx : ∀ n : Fin 3, qn n.succ =
        BandPackingSymmetryCircleAction g
          (qa (if BandPackingSymmetryReversesOrientation g then -n else n).succ) := by
      intro n
      fin_cases n <;> rfl
    rw [hidx]
    dsimp only [j]
    rw [hrev, hqai, hD]
  have hrootcurv : (qn 0).1 = C.1.1.1 := by
    rw [hroot]
    exact (BandPackingSymmetryCovariance g).1 _
  have hparentcurv : (qn j.succ).1 = D.1.1.1 := by
    rw [hparent]
    exact (BandPackingSymmetryCovariance g).1 _
  have hpC : 0 < (qn 0).1 := by rw [hrootcurv]; exact C.2
  have hpD : 0 < (qn j.succ).1 := by rw [hparentcurv]; exact D.2
  let Cn : BandCircle := ⟨⟨qn 0,
    ⟨Or.inl hpC, ⟨qn, hqn.1, 0, rfl⟩⟩⟩, hpC⟩
  let Dn : BandCircle := ⟨⟨qn j.succ,
    ⟨Or.inl hpD, ⟨qn, hqn.1, j.succ, rfl⟩⟩⟩, hpD⟩
  refine ⟨g, qn, Cn, Dn, j, xor e negative, pn, rn, hqn, rfl, rfl,
    hroot, hparent, hrootcurv, hparentcurv, hTn, hUn, hpn, hrn, hcn, ?_, ?_⟩
  · apply Prod.ext
    · exact hsn
    · exact htn
  · rcases hregime with ⟨hFord, _⟩ | ⟨hother, _⟩
    · exact Or.inl hFord
    · rcases hother with ⟨hDiamond, _⟩ | ⟨hGeneral, _⟩
      · exact Or.inr (Or.inl hDiamond)
      · exact Or.inr (Or.inr hGeneral)

end ApollonianSuperharmonic

end
