/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5596T1CommonExtensionTransport
public import LeanPool.ApollonianSuperharmonic.FordTerminalWebStencilLedger
public import LeanPool.ApollonianSuperharmonic.DiamondTerminalWebStencilLedger
public import LeanPool.ApollonianSuperharmonic.RightLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryMarkedDataCovariance

-- [TABLET NODE: P5606T1RightTerminalTransport]

/-!
# P5606T1RightTerminalTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5606T1RightTerminalTransport
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (i : Fin 3) (e : Bool) (a : Fin 3) (w : BandPackingSymmetry)
    (hnormal :
      (∃ P : FordFareyParameter, 1 < P.q ∧
        BandPackingSymmetryQuadrupleAction w
          ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ] =
            FordRecursiveQuadruple P) ∨
      (∃ K : DiamondParameter, 1 < K.1 ∧
        BandPackingSymmetryQuadrupleAction w
          ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ] =
            DiamondRecursiveQuadruple K))
    (T U : ProtoTile) (h k : PartialOdometer) (p p' : ℝ × ℝ)
    (g : IntegerLatticeFunction) (x : GaussianInt)
    (hT : TileOdometer (q 0) T h) (hU : TileOdometer (q 0) U k)
    (hp : PartialOdometerSlope h = some p)
    (hp' : PartialOdometerSlope k = some p')
    (hc : TileCentroid U - TileCentroid T =
      (if e = true then (1 : ℝ) else -1) •
        GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))
    (hr : p'.1 - p.1 = (if e = true then (1 : ℝ) else -1) *
      (BandVectors.2 (q 0) (q i.succ)).re)
    (hi : p'.2 - p.2 = (if e = true then (1 : ℝ) else -1) *
      (BandVectors.2 (q 0) (q i.succ)).im)
    (hcompat : OdometerCompatibility h k)
    (hg : GlobalOdometerExtends g h) (kg : GlobalOdometerExtends g k)
    (hx : x ∈ h.domain) (kx : x ∈ k.domain)
    (hstar : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ → y ∈ h.domain ∨ y ∈ k.domain) :
    ((∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨ z = x - 1 - ⟨0, 1⟩ →
        z ∈ T.cells ∨ z ∈ U.cells) → FourNeighborLaplacian g x = 1) ∧
    (¬ (∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨ z = x - 1 - ⟨0, 1⟩ →
        z ∈ T.cells ∨ z ∈ U.cells) → FourNeighborLaplacian g x = 0) := by
-- BODY
  let r : Fin 4 → CircleCoordinates :=
    ![q 0, q a.succ, q (a + 1).succ, q (a + 2).succ]
  have hr0 : r 0 = q 0 := rfl
  have hri : r (i - a).succ = q i.succ := by
    fin_cases a <;> fin_cases i <;> rfl
  have hproper : ProperBandQuadruple r := by
    fin_cases a
    · convert hq using 1; (try funext j; fin_cases j) <;> rfl
    · refine ⟨SemiProperQuadruple.rotate hq.1, ?_⟩
      intro j
      fin_cases j
      · exact hq.2 1
      · exact hq.2 2
      · exact hq.2 0
    · refine ⟨SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1), ?_⟩
      intro j
      fin_cases j
      · exact hq.2 2
      · exact hq.2 0
      · exact hq.2 1
  obtain ⟨delta, b, b', hphase, hTn, hUn, hpn, hp'n, hcn, hrn, hin, hcompatn⟩ :=
    RightLatticeAdjacentPackingSymmetryTransport w r hproper (i - a) e T U h k p p'
      (by simpa only [hr0] using hT) (by simpa only [hr0] using hU) hp hp'
      (by simpa only [hr0, hri] using hc)
      (by simpa only [hr0, hri] using hr)
      (by simpa only [hr0, hri] using hi)
  obtain ⟨g', hgn, kgn, hlap, hxn, kxn, hstarn⟩ :=
    P5596T1CommonExtensionTransport w g h k x hg kg hx kx hstar
  have incident (y : GaussianInt) (V W : ProtoTile) :
      (∀ z, z = y ∨ z = y - 1 ∨ z = y - ⟨0, 1⟩ ∨ z = y - 1 - ⟨0, 1⟩ →
        z ∈ V.cells ∨ z ∈ W.cells) ↔
      (∀ j : Fin 4, LatticeVertexIncidentCell y j ∈ V.cells ∨
        LatticeVertexIncidentCell y j ∈ W.cells) := by
    constructor
    · intro H j
      fin_cases j <;> apply H <;> simp [LatticeVertexIncidentCell]
    · intro H z hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact H 0
      · exact H 1
      · exact H 3
      · exact H 2
  have hcells := (incident x T U).trans
    ((BandPackingSymmetryMarkedDataCovariance.2.1 w x T U).trans
      (incident (BandPackingSymmetryVectorAction w x)
        (BandPackingSymmetryTileAction w T) (BandPackingSymmetryTileAction w U)).symm)
  let j : Fin 3 := if BandPackingSymmetryReversesOrientation w then -(i - a) else i - a
  let en := xor (xor e delta) (BandPackingSymmetryReversesOrientation w)
  have terminal :
      ((∀ z, z = BandPackingSymmetryVectorAction w x ∨
          z = BandPackingSymmetryVectorAction w x - 1 ∨
          z = BandPackingSymmetryVectorAction w x - ⟨0, 1⟩ ∨
          z = BandPackingSymmetryVectorAction w x - 1 - ⟨0, 1⟩ →
        z ∈ (BandPackingSymmetryTileAction w T).cells ∨
          z ∈ (BandPackingSymmetryTileAction w U).cells) →
        FourNeighborLaplacian g' (BandPackingSymmetryVectorAction w x) = 1) ∧
      (¬ (∀ z, z = BandPackingSymmetryVectorAction w x ∨
          z = BandPackingSymmetryVectorAction w x - 1 ∨
          z = BandPackingSymmetryVectorAction w x - ⟨0, 1⟩ ∨
          z = BandPackingSymmetryVectorAction w x - 1 - ⟨0, 1⟩ →
        z ∈ (BandPackingSymmetryTileAction w T).cells ∨
          z ∈ (BandPackingSymmetryTileAction w U).cells) →
        FourNeighborLaplacian g' (BandPackingSymmetryVectorAction w x) = 0) := by
    rcases hnormal with ⟨P, hP, heq⟩ | ⟨K, hK, heq⟩
    · change BandPackingSymmetryQuadrupleAction w r = FordRecursiveQuadruple P at heq
      rw [heq] at hTn hUn hcn hrn hin
      exact (FordTerminalWebStencilLedger P hP).1 j en _ _ _ _ b b' g' _
        hTn hUn hpn hp'n hcn hrn hin (hcompatn.mpr hcompat)
        hgn kgn hxn kxn hstarn
    · change BandPackingSymmetryQuadrupleAction w r = DiamondRecursiveQuadruple K at heq
      rw [heq] at hTn hUn hcn hrn hin
      exact (DiamondTerminalWebStencilLedger K hK).1 j en _ _ _ _ b b' g' _
        hTn hUn hpn hp'n hcn hrn hin (hcompatn.mpr hcompat)
        hgn kgn hxn kxn hstarn
  exact ⟨fun H => hlap ▸ terminal.1 (hcells.mp H),
    fun H => hlap ▸ terminal.2 (fun Hn => H (hcells.mpr Hn))⟩

end ApollonianSuperharmonic

end
