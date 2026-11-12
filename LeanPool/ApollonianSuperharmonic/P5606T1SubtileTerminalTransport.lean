/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5596T1CommonExtensionTransport
public import LeanPool.ApollonianSuperharmonic.FordTerminalWebStencilLedger
public import LeanPool.ApollonianSuperharmonic.DiamondTerminalWebStencilLedger
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacentPackingSymmetryTransport
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryMarkedDataCovariance

-- [TABLET NODE: P5606T1SubtileTerminalTransport]

/-!
# P5606T1SubtileTerminalTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5606T1SubtileTerminalTransport
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (i : Fin 3) (s : Fin 4) (hpos : 0 < (q i.succ).1)
    (a : Fin 3) (w : BandPackingSymmetry)
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
    (hT : TileOdometer (q 0) T h) (hU : TileOdometer (q i.succ) U k)
    (hp : PartialOdometerSlope h = some p)
    (hp' : PartialOdometerSlope k = some p')
    (hc : TileCentroid U - TileCentroid T =
      (1 / 2 : ℝ) • GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.1 (q i.succ) (q 0) + BandVectors.1 (q 0) (q i.succ))))
    (hr : p'.1 - p.1 = ((1 / 2 : ℝ) • GaussianRealPoint
      ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
        (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ)))).1)
    (hi : p'.2 - p.2 = ((1 / 2 : ℝ) • GaussianRealPoint
      ((-⟨0, 1⟩ : GaussianInt) ^ s.val *
        (BandVectors.2 (q i.succ) (q 0) + BandVectors.2 (q 0) (q i.succ)))).2)
    (hcompat : OdometerCompatibility h k)
    (hg : GlobalOdometerExtends g h) (kg : GlobalOdometerExtends g k)
    (hx : x ∈ h.domain) (kx : x ∈ k.domain)
    (hstar : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ → y ∈ h.domain ∨ y ∈ k.domain) :
    let UR := TileTranslation T ((⟨0, 1⟩ : GaussianInt) ^ s.val *
      (if Even s.val then BandVectors.1 (q 0) (q i.succ)
        else BandVectors.1 (q i.succ) (q 0)))
    (x ∈ FootprintVertices UR → FourNeighborLaplacian g x = 0) ∧
    (x ∉ FootprintVertices UR → FourNeighborLaplacian g x = 1) := by
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
  obtain ⟨delta, b, b', sn, hphase, hsn, hTn, hUn, hpn, hp'n,
      hcn, hrn, hin, hcompatn⟩ :=
    SubtileLatticeAdjacentPackingSymmetryTransport w r hproper (i - a) s
      (by simpa only [hri] using hpos) T U h k p p'
      (by simpa only [hr0] using hT) (by simpa only [hri] using hU) hp hp'
      (by simpa only [hr0, hri] using hc)
      (by simpa only [hr0, hri] using hr)
      (by simpa only [hr0, hri] using hi)
  obtain ⟨g', hgn, kgn, hlap, hxn, kxn, hstarn⟩ :=
    P5596T1CommonExtensionTransport w g h k x hg kg hx kx hstar
  have hmark := BandPackingSymmetryMarkedDataCovariance.2.2
    w r hproper (i - a) s delta hphase T x
  dsimp only at hmark
  rw [← hsn] at hmark
  simp only [hr0, hri] at hmark
  let j : Fin 3 := if BandPackingSymmetryReversesOrientation w then -(i - a) else i - a
  have terminal :
      let URn := TileTranslation (BandPackingSymmetryTileAction w T)
        ((⟨0, 1⟩ : GaussianInt) ^ sn.val *
          (if Even sn.val then
            BandVectors.1 (BandPackingSymmetryQuadrupleAction w r 0)
              (BandPackingSymmetryQuadrupleAction w r j.succ)
          else BandVectors.1 (BandPackingSymmetryQuadrupleAction w r j.succ)
            (BandPackingSymmetryQuadrupleAction w r 0)))
      (BandPackingSymmetryVectorAction w x ∈ FootprintVertices URn →
        FourNeighborLaplacian g' (BandPackingSymmetryVectorAction w x) = 0) ∧
      (BandPackingSymmetryVectorAction w x ∉ FootprintVertices URn →
        FourNeighborLaplacian g' (BandPackingSymmetryVectorAction w x) = 1) := by
    have hposn : 0 < (BandPackingSymmetryQuadrupleAction w r j.succ).1 := by
      have heq : BandPackingSymmetryQuadrupleAction w r j.succ =
          BandPackingSymmetryCircleAction w (r (i - a).succ) := by
        have parent (l : Fin 3) :
            BandPackingSymmetryQuadrupleAction w r
                (if BandPackingSymmetryReversesOrientation w then -l else l).succ =
              BandPackingSymmetryCircleAction w (r l.succ) := by
          cases he : BandPackingSymmetryReversesOrientation w <;> fin_cases l <;>
            simp [BandPackingSymmetryQuadrupleAction, he,
              show -(1 : Fin 3) = 2 from rfl, show -(2 : Fin 3) = 1 from rfl]
        exact parent (i - a)
      rw [heq, (BandPackingSymmetryCovariance w).1, hri]
      exact hpos
    rcases hnormal with ⟨P, hP, heq⟩ | ⟨K, hK, heq⟩
    · change BandPackingSymmetryQuadrupleAction w r = FordRecursiveQuadruple P at heq
      rw [heq] at hTn hUn hcn hrn hin hposn ⊢
      exact (FordTerminalWebStencilLedger P hP).2 j sn _ _ _ _ b b' g' _
        hposn hTn hUn hpn hp'n hcn hrn hin (hcompatn.mpr hcompat)
        hgn kgn hxn kxn hstarn
    · change BandPackingSymmetryQuadrupleAction w r = DiamondRecursiveQuadruple K at heq
      rw [heq] at hTn hUn hcn hrn hin ⊢
      exact (DiamondTerminalWebStencilLedger K hK).2 j sn _ _ _ _ b b' g' _
        hTn hUn hpn hp'n hcn hrn hin (hcompatn.mpr hcompat)
        hgn kgn hxn kxn hstarn
  exact ⟨fun H => hlap ▸ terminal.1 (hmark.2.mp H),
    fun H => hlap ▸ terminal.2 (fun Hn => H (hmark.2.mpr Hn))⟩

end ApollonianSuperharmonic

end
