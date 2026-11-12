/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTilingTransport
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.BandOrientedChildParentEndpoints
public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriplePackingSymmetryCovariance
public import LeanPool.ApollonianSuperharmonic.FordOrientedChildParentIncomingEndpoint
public import LeanPool.ApollonianSuperharmonic.OrientedTouchingCovariance
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.P4055T1BandQuarterTurn
public import LeanPool.ApollonianSuperharmonic.P4085T1FordIncomingNormalization
public import LeanPool.ApollonianSuperharmonic.P4085T1MinusTouching

-- [TABLET NODE: BandOrientedChildParentIncomingEndpoint]

/-!
# BandOrientedChildParentIncomingEndpoint

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrientedChildParentIncomingEndpoint
    (r : Fin 4 → CircleCoordinates) (hproper : ProperBandQuadruple r)
    (i : Fin 3) (s : Fin 4) (U W Z : ProtoTile)
    (hU : BandPrototile (r 0) U)
    (hW : BandPrototile (r i.succ) W)
    (hZ : BandPrototile
      (r ((if Even s.val then i - 1 else i + 1).succ)) Z)
    (hUpos : 0 < (r 0).1) (hWpos : 0 < (r i.succ).1)
    (hWcent : TileCentroid W - TileCentroid U = (1 / 2 : Real) •
      GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (BandVectors.1 (r i.succ) (r 0) +
            BandVectors.1 (r 0) (r i.succ))))
    (hZcent : TileCentroid Z - TileCentroid U = (1 / 2 : Real) •
      GaussianRealPoint
        ((⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then
            BandVectors.1 (r 0) (r ((i - 1).succ)) -
              BandVectors.1 (r ((i - 1).succ)) (r 0)
          else
            BandVectors.1 (r ((i + 1).succ)) (r 0) -
              BandVectors.1 (r 0) (r ((i + 1).succ))))) :
    let uL := (⟨0, 1⟩ : GaussianInt) ^ s.val *
      (if Even s.val then BandVectors.1 (r i.succ) (r 0)
        else BandVectors.1 (r 0) (r i.succ))
    ∃ _ : ExactTileInterfaceTriple U (TileTranslation U uL) W,
      TouchingTriple U (TileTranslation U uL) W := by
-- BODY
  classical
  let ii : GaussianInt := ⟨0, 1⟩
  let x := BandVectors.1 (r i.succ) (r 0)
  let z := BandVectors.1 (r 0) (r i.succ)
  let uL := ii ^ s.val * (if Even s.val then x else z)
  change ∃ _ : ExactTileInterfaceTriple U (TileTranslation U uL) W,
    TouchingTriple U (TileTranslation U uL) W
  have curvature := ProperBandCurvatureStructure r hproper
  let j : Fin 3 := if Even s.val then i - 1 else i + 1
  have hjnonneg : 0 ≤ (r j.succ).1 := curvature.2.1 j
  by_cases hjpos : 0 < (r j.succ).1
  · obtain ⟨_, incoming, _⟩ := BandOrientedChildParentEndpoints
      r hproper i s U W Z hU hW hZ hUpos hWpos hjpos hWcent hZcent
    refine ⟨incoming, ?_⟩
    have hlarge : 1 < (r 0).1 := by
      by_contra hn
      have allzero : ∀ k : Fin 3, (r k.succ).1 = 0 := by
        intro k
        have := curvature.2.1 k
        have := hproper.2 k
        omega
      exact (by decide : (0 : Fin 3) ≠ 1)
        (curvature.2.2 0 1 (allzero 0) (allzero 1))
    have hT2 : ∀ (a : Fin 4) (V : ProtoTile),
        BandPrototile (r a) V → QuarterTurnSymmetric V := by
      intro a V hV
      exact P4055T1BandQuarterTurn _ _ hV
    have hcov := OrientedTouchingCovariance r hproper hT2
      (by
        intro A B k hA hB hc
        exact (BandTileSimultaneousInduction r hproper A hA).2.2.2.2.2.1
          hlarge k B hB hc)
      (by
        intro A B C k hA hB hC hcB hcC
        exact (BandTileSimultaneousInduction r hproper A hA).2.2.2.2.2.2.1
          k B C hB hC hcB hcC)
    have qmul (v : GaussianInt) : GaussianQuarterTurn v = ii * v := by
      ext <;> simp [ii, GaussianQuarterTurn]
    have qiter (n : ℕ) (v : GaussianInt) :
        (GaussianQuarterTurn^[n]) v = ii ^ n * v := by
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply', qmul, ih, pow_succ]
          ring
    have oriented (V : ProtoTile) (t : Fin 4)
        (hV : BandPrototile (r i.succ) V)
        (hc : TileCentroid V - TileCentroid U =
          (1 / 2 : Real) • GaussianRealPoint (ii ^ t.val * (x + z))) :
        TouchingTriple U (TileTranslation U (ii ^ t.val * x)) V := by
      have hp (a b : GaussianInt) :
          GaussianRealPoint (a + b) = GaussianRealPoint a + GaussianRealPoint b := by
        ext <;> simp [GaussianRealPoint]
      have hc' : TileCentroid V - TileCentroid U = (1 / 2 : Real) •
          (GaussianRealPoint ((GaussianQuarterTurn^[t.val]) x) +
            GaussianRealPoint ((GaussianQuarterTurn^[t.val]) z)) := by
        simpa only [qiter, ← hp, ← mul_add] using hc
      simpa only [qiter] using hcov.1 U V i t hU hV hc'
    by_cases hs : Even s.val
    · simpa only [uL, hs, ite_true] using oriented W s hW hWcent
    · let t : Fin 4 := s + 1
      let y := ii ^ t.val * x
      have hflip : z = ii * x :=
        ((VectorRecursionLaws r hproper.1).2.2.2.2 hproper i).1
      have hv : ii ^ s.val * (x + z) = y - GaussianQuarterTurn y := by
        rw [qmul, hflip]
        fin_cases s <;> dsimp [y, t, ii] <;> ext <;> simp [pow_succ] <;> ring
      have hy : uL = y := by
        simp only [uL, hs, ite_false, hflip]
        fin_cases s <;> dsimp [y, t, ii] <;> ext <;> simp [pow_succ]
      have hminus : TileCentroid W - TileCentroid U =
          (1 / 2 : Real) • GaussianRealPoint (y - GaussianQuarterTurn y) := by
        rw [← hv]
        exact hWcent
      have hqz : ii ^ t.val * z = GaussianQuarterTurn y := by
        rw [qmul, hflip]
        dsimp [y]
        ring
      have hcplus : TileCentroid (TileTranslation W (GaussianQuarterTurn y)) -
          TileCentroid U = (1 / 2 : Real) •
            GaussianRealPoint (ii ^ t.val * (x + z)) := by
        rw [mul_add, hqz]
        change TileCentroid (TileTranslation W (GaussianQuarterTurn y)) -
          TileCentroid U = (1 / 2 : Real) • GaussianRealPoint (y + GaussianQuarterTurn y)
        rw [(TileTranslationFormulas W _).2.2.2.2.1]
        have h₁ := congrArg Prod.fst hminus
        have h₂ := congrArg Prod.snd hminus
        simp? [GaussianRealPoint, GaussianQuarterTurn] at h₁ h₂ ⊢
        apply Prod.ext <;> dsimp <;> linarith
      have hp := oriented (TileTranslation W (GaussianQuarterTurn y)) t
        (BandPrototileTranslation _ _ _ hW) hcplus
      rw [hy]
      exact P4085T1MinusTouching U W y (hT2 0 U hU) (hT2 i.succ W hW) hminus hp
  · have hjzero : (r j.succ).1 = 0 := by omega
    obtain ⟨a, g, P, hP, hnormal, hlabel, hUF, hWF, hUposF, hWposF, hcF, hdF⟩ :=
      P4085T1FordIncomingNormalization r hproper ⟨j.succ, hjzero⟩
        i s U W hU hW hUpos hWpos hWcent
    obtain ⟨dataF, touchingF⟩ := FordOrientedChildParentIncomingEndpoint P hP
      (i - a) s (BandPackingSymmetryTileAction g U)
      (BandPackingSymmetryTileAction g W) hUF hWF hUposF hWposF hcF
    have hmiddle : BandPackingSymmetryTileAction g (TileTranslation U uL) =
        TileTranslation (BandPackingSymmetryTileAction g U)
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then
              BandVectors.1 (FordRecursiveQuadruple P (i - a).succ) (FordRecursiveQuadruple P 0)
            else BandVectors.1 (FordRecursiveQuadruple P 0) (FordRecursiveQuadruple P (i -
                a).succ))) := by
      rw [(BandPackingSymmetryTilingTransport g).2.2.2.2.2.2.1]
      exact congrArg (TileTranslation (BandPackingSymmetryTileAction g U)) hdF
    have dataImage : Nonempty (ExactTileInterfaceTriple
        (BandPackingSymmetryTileAction g U)
        (BandPackingSymmetryTileAction g (TileTranslation U uL))
        (BandPackingSymmetryTileAction g W)) := by
      rw [hmiddle]
      exact ⟨dataF⟩
    obtain ⟨data⟩ :=
      (ExactTileInterfaceTriplePackingSymmetryCovariance g U (TileTranslation U uL) W).mpr dataImage
    refine ⟨data, ?_⟩
    apply ((BandPackingSymmetryTilingTransport g).2.2.2.2.2.1 U (TileTranslation U uL) W).mpr
    rw [hmiddle]
    exact touchingF

end ApollonianSuperharmonic

end
