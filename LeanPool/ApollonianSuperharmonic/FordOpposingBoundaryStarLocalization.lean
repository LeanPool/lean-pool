/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.FordTileCellMembership

public import LeanPool.ApollonianSuperharmonic.P4158T1MatchedFordPair
public import LeanPool.ApollonianSuperharmonic.P4158T1LargeFirstRestrictions
public import LeanPool.ApollonianSuperharmonic.P4158T1LargeSecondRestrictions
public import LeanPool.ApollonianSuperharmonic.P4158T1AncestorCells
public import LeanPool.ApollonianSuperharmonic.P4158T1SmallerStringEdges
public import LeanPool.ApollonianSuperharmonic.P4158T1EdgeSectorSelection
public import LeanPool.ApollonianSuperharmonic.P4158T1StringSlopeTelescoping
public import LeanPool.ApollonianSuperharmonic.OpposingBoundaryOdometerStrings

-- [TABLET NODE: FordOpposingBoundaryStarLocalization]

/-!
# FordOpposingBoundaryStarLocalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FordStarGeometry

private theorem hxfoot :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (h0 : PartialOdometer), ∀ (h0' :
            PartialOdometer), ∀ (x : GaussianInt), (x ∈ h0.domain) → ((x ∈ h0'.domain) →
            (((↑h0.domain : Set GaussianInt) = FootprintVertices T0) → (((↑h0'.domain : Set
            GaussianInt) = FootprintVertices T0') → (x ∈ FootprintVertices T0 ∩ FootprintVertices
            T0')))) ) := by
  classical
  intro T0 T0' h0 h0' x hx0 hx0' hdom0 hdom0'
  constructor
  · rw [← hdom0]; exact hx0
  · rw [← hdom0']; exact hx0'

private theorem squareCell :
    (by
      classical
      exact
        ∀ (n : Nat),
          ∀ (v : GaussianInt),
            ∀ (z : GaussianInt),
              z ∈ (TileTranslation (FordTile n) v).cells ↔
                0 ≤ (z - v).re ∧
                  (z - v).re < (n : Int) ∧ 0 ≤ (z - v).im ∧ (z - v).im < (n : Int)
    ) := by
  intro n v z
  exact FordTileCellMembership.translated n v z

private theorem smaller :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (ProperBandQuadruple (FordRecursiveQuadruple P)) → (∀ (C0 :
            BandCircle), ∀ (Ci : BandCircle), ∀ (i : Fin 3), (FordRecursiveQuadruple P (0 : Fin
            (4 : ℕ)) = C0.1.1) → ((FordRecursiveQuadruple P i.succ = Ci.1.1) → (∀ (T0 :
            ProtoTile), ∀ (T0' : ProtoTile), ∀ (h0 : PartialOdometer), ∀ (h0' : PartialOdometer),
            (TileOdometer C0.1.1 T0 h0) → ((TileOdometer C0.1.1 T0' h0') → (((1 : ℤ) < Ci.1.1.1)
            → (∀ (p0 : Real × Real), ∀ (p0' : Real × Real), (PartialOdometerSlope h0 = some p0) →
            ((PartialOdometerSlope h0' = some p0') → ((TileCentroid T0' - TileCentroid T0 =
            GaussianRealPoint (BandVectors.1 (FordRecursiveQuadruple P i.succ)
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))))) → ((p0' - p0 = GaussianRealPoint
            (BandVectors.2 (FordRecursiveQuadruple P i.succ) (FordRecursiveQuadruple P (0 : Fin
            (4 : ℕ))))) → (∀ (x : GaussianInt), ((0 : ℕ) < P.q₁) → (∀ (u : GaussianInt),
            (T0.cells = (TileTranslation (FordTile P.q) u).cells) → ((T0'.cells =
            (TileTranslation (FordTile P.q) (u + if i = (0 : Fin (3 : ℕ)) then (⟨(↑P.q : ℤ),
            (↑P.q₁ : ℤ)⟩ : GaussianInt) else (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt))).cells)
            → ((Disjoint T0.cells T0'.cells) → ((∀ (x : GaussianInt), x ∈ FootprintVertices T0 ∩
            FootprintVertices T0' ↔ ((x - u).re = if i = (0 : Fin (3 : ℕ)) then (↑P.q : ℤ) else
            (0 : ℤ)) ∧ (if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) ≤ (x - u).im
            ∧ (x - u).im ≤ (↑P.q : ℤ)) → (((x - u).re = if i = (0 : Fin (3 : ℕ)) then (↑P.q : ℤ)
            else (0 : ℤ)) → (((if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) ≤ (x -
            u).im) → (((x - u).im ≤ (↑P.q : ℤ)) → (((i = 0 ∧ P.q₁ < P.q₂) ∨ (i = 1 ∧ P.q₂ <
            P.q₁)) → (∃ (U V : ProtoTile) (g k : PartialOdometer), AncestorOdometer Ci.1.1 C0.1.1
            U T0 g h0 ∧ AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0' ∧ LeftLatticeAdjacent Ci U V g
            k ∧ ((x ∈ U.cells ∧ x - 1 - ⟨0, 1⟩ ∈ V.cells) ∨ (x - 1 ∈ U.cells ∧ x - ⟨0, 1⟩ ∈
            V.cells) ∨ (x - 1 - ⟨0, 1⟩ ∈ U.cells ∧ x ∈ V.cells) ∨ (x - ⟨0, 1⟩ ∈ U.cells ∧ x - 1 ∈
            V.cells))))))))))))))))))))) ) := by
  classical
  intro P hq C0 Ci i hC0 hCi T0 T0' h0 h0' hO0 hO0' hlarge p0 p0' hs0 hs0' hcentroid hslope x
      hrpos u hc hc' hdis hsegment hxr hxl hxu hsmall
  obtain ⟨orientation, centerShift, base, Rminus, Rplus, tiles, reverseTiles,
    hs, reverseHs, hminus, hplus, pminus, pplus, a, b, bm, bp,
    hboundary, _, _, _, _, hf, hr, hh, _, _, hh', hOm, hOp,
    _, _, _, _, _, _, _, hanc, hanc'⟩ :=
    OpposingBoundaryOdometerStrings (FordRecursiveQuadruple P) hq C0 Ci i
      hC0 hCi T0 T0' h0 h0' hO0 hO0' Ci.2 p0 p0' hs0 hs0'
      hcentroid hslope
  obtain ⟨q', _, hq'0, hq'i, _, _, _, hcm, hcp⟩ := hboundary
  have hcm' : TileCentroid Rminus - TileCentroid T0 = (1 / 2 : Real) •
      GaussianRealPoint (BandVectors.1 (FordRecursiveQuadruple P i.succ)
        (FordRecursiveQuadruple P 0) - BandVectors.1 (FordRecursiveQuadruple P 0)
          (FordRecursiveQuadruple P i.succ)) := by
    simpa only [hq'0, hq'i, hC0, hCi] using hcm
  have hcp' : TileCentroid Rplus - TileCentroid T0 = (1 / 2 : Real) •
      GaussianRealPoint (BandVectors.1 (FordRecursiveQuadruple P i.succ)
        (FordRecursiveQuadruple P 0) + BandVectors.1 (FordRecursiveQuadruple P 0)
          (FordRecursiveQuadruple P i.succ)) := by
    simpa only [hq'0, hq'i, hC0, hCi] using hcp
  obtain ⟨hRm, hRp, hedges⟩ := P4158T1SmallerStringEdges P hq C0 Ci i hC0 hCi
    hlarge hsmall T0 T0' h0 h0' u hc hc' hsegment orientation base Rminus Rplus
    tiles reverseTiles hs reverseHs hf hr hminus hplus hOm hOp hcm' hcp' hanc hanc'
  obtain hunit | ⟨r, hrsemi, hr0, hrless, _⟩ := BandGenealogy Ci
  · omega
  have hrproper : ProperBandQuadruple r :=
    ⟨hrsemi, by simpa only [hr0] using hrless⟩
  obtain ⟨PP, _, htiles, hadj, _, _, _, _, ⟨chart⟩⟩ :=
    BandRegularTranslatePeriodicComplex Ci r hrproper hr0 base
      (by simpa only [hr0] using hf.1.1)
  obtain ⟨a, b, g, k, hab, hUg, hVk, hAg, hAk, hedge, hdiag⟩ :=
    P4158T1EdgeSectorSelection P C0 Ci i hsmall hrpos hlarge T0 T0' h0 h0' u
      hc hc' hdis orientation base Rminus Rplus tiles reverseTiles hs reverseHs
      hf.1 hr.1 hRm hRp
      (fun U g _ hA => P4158T1AncestorCells _ _ U T0 hA.2.1)
      (fun V k _ hA => P4158T1AncestorCells _ _ V T0' hA.2.1)
      hedges PP htiles _ chart x hxr hxl hxu
  have hUgO := List.forall₂_zip hf.2.1 hUg
  have hVkO := List.forall₂_zip hr.2.1 hVk
  obtain ⟨s, t, hsg, htk, hslr, hsli⟩ := P4158T1StringSlopeTelescoping
    Ci hlarge orientation base Rminus Rplus tiles reverseTiles hs reverseHs
      hf hr hminus hh hh' (PP.tile a) (PP.tile b) g k hUg hVk
  obtain ⟨z, _, heU, heV⟩ := hedge
  have hadjacent := ((PeriodicTileIntersectionClassification PP).1 a b hab).1.mp
    ⟨{z, z + ⟨0, 1⟩}, heU, heV⟩
  obtain ⟨j, hdisp⟩ := (hadj a b).mp hadjacent
  have hcent : TileCentroid (PP.tile b) - TileCentroid (PP.tile a) =
      GaussianRealPoint ((b : GaussianInt) - (a : GaussianInt)) := by
    rw [htiles a, htiles b, (TileTranslationFormulas base _).2.2.2.2.1,
      (TileTranslationFormulas base _).2.2.2.2.1]
    ext <;> simp [GaussianRealPoint]
  have hin := CircleMatrixIncomingVector Ci r hrsemi hr0 j
  have hin0 := congrFun hin 0
  have hin1 := congrFun hin 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hin0 hin1
  have hleft : LeftLatticeAdjacent Ci (PP.tile a) (PP.tile b) g k := by
    refine ⟨hUgO, hVkO, s, t, hsg, htk, Or.inr ?_⟩
    rcases hdisp with hdisp | hdisp
    · refine ⟨r, j, true, hrproper, hr0, ?_, ?_, ?_⟩
      · simpa [hdisp] using hcent
      · have hcr := congrArg Prod.fst (hcent.trans (congrArg GaussianRealPoint hdisp))
        have hci := congrArg Prod.snd (hcent.trans (congrArg GaussianRealPoint hdisp))
        change (TileCentroid (PP.tile b)).1 - (TileCentroid (PP.tile a)).1 =
          ((BandVectors.1 (r j.succ) (r 0)).re : Real) at hcr
        change (TileCentroid (PP.tile b)).2 - (TileCentroid (PP.tile a)).2 =
          ((BandVectors.1 (r j.succ) (r 0)).im : Real) at hci
        change t.1 - s.1 = 1 * _
        rw [one_mul, hslr, hcr, hci]
        exact hin0
      · have hcr := congrArg Prod.fst (hcent.trans (congrArg GaussianRealPoint hdisp))
        have hci := congrArg Prod.snd (hcent.trans (congrArg GaussianRealPoint hdisp))
        change (TileCentroid (PP.tile b)).1 - (TileCentroid (PP.tile a)).1 =
          ((BandVectors.1 (r j.succ) (r 0)).re : Real) at hcr
        change (TileCentroid (PP.tile b)).2 - (TileCentroid (PP.tile a)).2 =
          ((BandVectors.1 (r j.succ) (r 0)).im : Real) at hci
        change t.2 - s.2 = 1 * _
        rw [one_mul, hsli, hcr, hci]
        exact hin1
    · refine ⟨r, j, false, hrproper, hr0, ?_, ?_, ?_⟩
      · rw [hcent, hdisp]
        ext <;> simp [GaussianRealPoint]
      · have hcr := congrArg Prod.fst (hcent.trans (congrArg GaussianRealPoint hdisp))
        have hci := congrArg Prod.snd (hcent.trans (congrArg GaussianRealPoint hdisp))
        change (TileCentroid (PP.tile b)).1 - (TileCentroid (PP.tile a)).1 =
          ((-BandVectors.1 (r j.succ) (r 0)).re : Real) at hcr
        change (TileCentroid (PP.tile b)).2 - (TileCentroid (PP.tile a)).2 =
          ((-BandVectors.1 (r j.succ) (r 0)).im : Real) at hci
        change t.1 - s.1 = -1 * _
        rw [hslr, hcr, hci]
        simp only [Zsqrtd.re_neg, Zsqrtd.im_neg, Int.cast_neg]
        linear_combination -hin0
      · have hcr := congrArg Prod.fst (hcent.trans (congrArg GaussianRealPoint hdisp))
        have hci := congrArg Prod.snd (hcent.trans (congrArg GaussianRealPoint hdisp))
        change (TileCentroid (PP.tile b)).1 - (TileCentroid (PP.tile a)).1 =
          ((-BandVectors.1 (r j.succ) (r 0)).re : Real) at hcr
        change (TileCentroid (PP.tile b)).2 - (TileCentroid (PP.tile a)).2 =
          ((-BandVectors.1 (r j.succ) (r 0)).im : Real) at hci
        change t.2 - s.2 = -1 * _
        rw [hsli, hcr, hci]
        simp only [Zsqrtd.re_neg, Zsqrtd.im_neg, Int.cast_neg]
        linear_combination -hin1
  exact ⟨PP.tile a, PP.tile b, g, k, hAg, hAk, hleft, hdiag⟩

private theorem hleftAt319 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), (P.q₂ < P.q₁) → (∀ (U : ProtoTile), ∀ (V
            : ProtoTile), ∀ (g : PartialOdometer), ∀ (k : PartialOdometer), ∀ (s : ℝ × ℝ), ∀ (t :
            ℝ × ℝ), ∀ (Q : FordFareyParameter), (TileOdometer Ci.1.1 U g) → ((TileOdometer Ci.1.1
            V k) → ((PartialOdometerSlope g = some s) → ((PartialOdometerSlope k = some t) →
            ((TileCentroid V - TileCentroid U = GaussianRealPoint (⟨(↑P.q₁ : ℤ), (↑P.q₁ : ℤ) -
            (↑P.q₂ : ℤ)⟩ : GaussianInt)) → ((t - s = GaussianRealPoint (⟨P.p₁ - P.p₂, P.p₁⟩ :
            GaussianInt)) → ((Q.q = P.q₁) → ((Q.q₁ = P.q₁ - P.q₂) → ((Q.p = P.p₁) → ((Q.p₁ = P.p₁
            - P.p₂) → ((FordRecursiveQuadruple Q (0 : Fin (4 : ℕ)) = Ci.1.1) →
            ((ProperBandQuadruple (FordRecursiveQuadruple Q) ∧ BandVectors.1
            (FordRecursiveQuadruple Q (1 : Fin (4 : ℕ))) (FordRecursiveQuadruple Q (0 : Fin (4 :
            ℕ))) = (⟨(↑Q.q : ℤ), (↑Q.q₁ : ℤ)⟩ : GaussianInt) ∧ BandVectors.1
            (FordRecursiveQuadruple Q (2 : Fin (4 : ℕ))) (FordRecursiveQuadruple Q (0 : Fin (4 :
            ℕ))) = (⟨-(↑Q.q : ℤ), (↑Q.q₂ : ℤ)⟩ : GaussianInt) ∧ BandVectors.1
            (FordRecursiveQuadruple Q (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple Q (0 : Fin (4 :
            ℕ))) = (⟨(0 : ℤ), -(↑Q.q : ℤ)⟩ : GaussianInt) ∧ BandVectors.2 (FordRecursiveQuadruple
            Q (1 : Fin (4 : ℕ))) (FordRecursiveQuadruple Q (0 : Fin (4 : ℕ))) = (⟨Q.p₁, Q.p⟩ :
            GaussianInt) ∧ BandVectors.2 (FordRecursiveQuadruple Q (2 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple Q (0 : Fin (4 : ℕ))) = (⟨Q.p₂, -Q.p⟩ : GaussianInt) ∧
            BandVectors.2 (FordRecursiveQuadruple Q (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple Q
            (0 : Fin (4 : ℕ))) = (⟨-Q.p, (0 : ℤ)⟩ : GaussianInt) ∧ BandVectors.2
            (FordRecursiveQuadruple Q (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple Q (2 : Fin (4 :
            ℕ))) = (⟨-Q.p₂, (0 : ℤ)⟩ : GaussianInt) ∧ BandVectors.2 (FordRecursiveQuadruple Q (1
            : Fin (4 : ℕ))) (FordRecursiveQuadruple Q (3 : Fin (4 : ℕ))) = (⟨(0 : ℤ), Q.p₁⟩ :
            GaussianInt)) → (LeftLatticeAdjacent Ci U V g k))))))))))))) ) := by
  classical
  intro P Ci horder U V g k s t Q hUg hVk hsg htk hUV hst hQq hQr hQp hQp1 hQ0 cfg
  refine ⟨hUg, hVk, s, t, hsg, htk, Or.inr
    ⟨FordRecursiveQuadruple Q, 0, true, cfg.1, hQ0, ?_, ?_, ?_⟩⟩
  · simpa [cfg.2.1, hQq, hQr, Nat.cast_sub horder.le] using hUV
  · have hh := congrArg Prod.fst hst
    simpa [cfg.2.2.2.2.1, hQp1, hQp, GaussianRealPoint] using hh
  · have hh := congrArg Prod.snd hst
    simpa [cfg.2.2.2.2.1, hQp1, hQp, GaussianRealPoint] using hh

private theorem hleftAt345 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), (P.q₁ < P.q₂) → (∀ (U : ProtoTile), ∀ (V
            : ProtoTile), ∀ (g : PartialOdometer), ∀ (k : PartialOdometer), ∀ (s : ℝ × ℝ), ∀ (t :
            ℝ × ℝ), ∀ (Q : FordFareyParameter), (TileOdometer Ci.1.1 U g) → ((TileOdometer Ci.1.1
            V k) → ((PartialOdometerSlope g = some s) → ((PartialOdometerSlope k = some t) →
            ((TileCentroid V - TileCentroid U = GaussianRealPoint (⟨-(↑P.q₂ : ℤ), (↑P.q₂ : ℤ) -
            (↑P.q₁ : ℤ)⟩ : GaussianInt)) → ((t - s = GaussianRealPoint (⟨P.p₂ - P.p₁, -P.p₂⟩ :
            GaussianInt)) → ((Q.q = P.q₂) → ((Q.q₂ = P.q₂ - P.q₁) → ((Q.p = P.p₂) → ((Q.p₂ = P.p₂
            - P.p₁) → ((FordRecursiveQuadruple Q (0 : Fin (4 : ℕ)) = Ci.1.1) →
            ((ProperBandQuadruple (FordRecursiveQuadruple Q) ∧ BandVectors.1
            (FordRecursiveQuadruple Q (1 : Fin (4 : ℕ))) (FordRecursiveQuadruple Q (0 : Fin (4 :
            ℕ))) = (⟨(↑Q.q : ℤ), (↑Q.q₁ : ℤ)⟩ : GaussianInt) ∧ BandVectors.1
            (FordRecursiveQuadruple Q (2 : Fin (4 : ℕ))) (FordRecursiveQuadruple Q (0 : Fin (4 :
            ℕ))) = (⟨-(↑Q.q : ℤ), (↑Q.q₂ : ℤ)⟩ : GaussianInt) ∧ BandVectors.1
            (FordRecursiveQuadruple Q (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple Q (0 : Fin (4 :
            ℕ))) = (⟨(0 : ℤ), -(↑Q.q : ℤ)⟩ : GaussianInt) ∧ BandVectors.2 (FordRecursiveQuadruple
            Q (1 : Fin (4 : ℕ))) (FordRecursiveQuadruple Q (0 : Fin (4 : ℕ))) = (⟨Q.p₁, Q.p⟩ :
            GaussianInt) ∧ BandVectors.2 (FordRecursiveQuadruple Q (2 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple Q (0 : Fin (4 : ℕ))) = (⟨Q.p₂, -Q.p⟩ : GaussianInt) ∧
            BandVectors.2 (FordRecursiveQuadruple Q (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple Q
            (0 : Fin (4 : ℕ))) = (⟨-Q.p, (0 : ℤ)⟩ : GaussianInt) ∧ BandVectors.2
            (FordRecursiveQuadruple Q (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple Q (2 : Fin (4 :
            ℕ))) = (⟨-Q.p₂, (0 : ℤ)⟩ : GaussianInt) ∧ BandVectors.2 (FordRecursiveQuadruple Q (1
            : Fin (4 : ℕ))) (FordRecursiveQuadruple Q (3 : Fin (4 : ℕ))) = (⟨(0 : ℤ), Q.p₁⟩ :
            GaussianInt)) → (LeftLatticeAdjacent Ci U V g k))))))))))))) ) := by
  classical
  intro P Ci horder U V g k s t Q hUg hVk hsg htk hUV hst hQq hQs hQp hQp2 hQ0 cfg
  refine ⟨hUg, hVk, s, t, hsg, htk, Or.inr
    ⟨FordRecursiveQuadruple Q, 1, true, cfg.1, hQ0, ?_, ?_, ?_⟩⟩
  · simpa [cfg.2.2.1, hQq, hQs, Nat.cast_sub horder.le] using hUV
  · have hh := congrArg Prod.fst hst
    simpa [cfg.2.2.2.2.2.1, hQp2, hQp, GaussianRealPoint] using hh
  · have hh := congrArg Prod.snd hst
    simpa [cfg.2.2.2.2.2.1, hQp2, hQp, GaussianRealPoint] using hh

private theorem corner :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (z : GaussianInt), (z ∈ T.cells) → (∀ (y : GaussianInt), (y = z ∨ y
            = z + 1 ∨ y = z + ⟨0, 1⟩ ∨
            y = z + 1 + ⟨0, 1⟩) → (y ∈ FootprintVertices T)) ) := by
  classical
  intro T z hz y hy
  rw [FootprintVertices, ite_eq_left ⟨z, hz⟩]
  exact ⟨z, hz, hy⟩

private theorem diagonalCover :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (i : Fin 3),
            ∀ (h0 : PartialOdometer),
              ∀ (h0' : PartialOdometer),
                ∀ (x : GaussianInt),
                  (∀ (y : GaussianInt),
                      y = x ∨
                          y = x + (1 : GaussianInt) ∨
                            y = x - (1 : GaussianInt) ∨
                              y = x + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨
                                y = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) →
                        y ∈ h0.domain ∨ y ∈ h0'.domain) →
                    ∀ (u : GaussianInt),
                      ((x - u).re =
                          if i = (0 : Fin (3 : ℕ)) then (↑P.q : ℤ) else (0 : ℤ)) →
                        (if i = (0 : Fin (3 : ℕ)) then (↑P.q₁ : ℤ) else (↑P.q₂ : ℤ)) ≤
                            (x - u).im →
                          (x - u).im ≤ (↑P.q : ℤ) →
                            (∀ (T : ProtoTile),
                                ∀ (z : GaussianInt),
                                z ∈ T.cells →
                                ∀ (y : GaussianInt),
                                y = z ∨ y = z + 1 ∨ y = z + ⟨0, 1⟩ ∨ y = z + 1 + ⟨0, 1⟩ →
                                y ∈ FootprintVertices T) →
                              ∀ (A : ProtoTile),
                                ∀ (B : ProtoTile),
                                x ∈ A.cells ∧ x - 1 - ⟨0, 1⟩ ∈ B.cells ∨
                                x - 1 ∈ A.cells ∧ x - ⟨0, 1⟩ ∈ B.cells →
                                x ∈ FootprintVertices A ∧
                                x ∈ FootprintVertices B ∧
                                ∀ y,
                                y = x ∨
                                y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
                                y ∈ FootprintVertices A ∨ y ∈ FootprintVertices B
    ) := by
  classical
  intro P i h0 h0' x hstar u hxr hxl hxu corner A B
  rintro (⟨hA, hB⟩ | ⟨hA, hB⟩)
  · refine ⟨corner A x hA x (Or.inl rfl),
      corner B _ hB x (Or.inr (Or.inr (Or.inr (by abel)))), ?_⟩
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (corner A _ hA _ (Or.inl rfl))
    · exact Or.inl (corner A _ hA _ (Or.inr (Or.inl rfl)))
    · exact Or.inr (corner B _ hB _ (Or.inr (Or.inr (Or.inl (by abel)))))
    · exact Or.inl (corner A _ hA _ (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (corner B _ hB _ (Or.inr (Or.inl (by abel))))
  · refine ⟨corner A _ hA x (Or.inr (Or.inl (by abel))),
      corner B _ hB x (Or.inr (Or.inr (Or.inl (by abel)))), ?_⟩
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (corner A _ hA _ (Or.inr (Or.inl (by abel))))
    · exact Or.inr (corner B _ hB _ (Or.inr (Or.inr (Or.inr (by abel)))))
    · exact Or.inl (corner A _ hA _ (Or.inl rfl))
    · exact Or.inl (corner A _ hA _ (Or.inr (Or.inr (Or.inr (by abel)))))
    · exact Or.inr (corner B _ hB _ (Or.inl rfl))

private theorem hfootcover :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (U : ProtoTile), ∀ (V : ProtoTile), (x ∈ U.cells ∧ x - (1 :
            GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ V.cells ∨ x - (1 : GaussianInt) ∈
            U.cells ∧ x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ V.cells ∨ x - (1 : GaussianInt) -
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ U.cells ∧ x ∈ V.cells ∨ x - (⟨(0 : ℤ), (1 : ℤ)⟩
            : GaussianInt) ∈ U.cells ∧ x - (1 : GaussianInt) ∈ V.cells) → ((∀ (A : ProtoTile), ∀
            (B : ProtoTile), ((x ∈ A.cells ∧ x - 1 - ⟨0, 1⟩ ∈ B.cells) ∨ (x - 1 ∈ A.cells ∧ x -
            ⟨0, 1⟩ ∈ B.cells)) → x ∈ FootprintVertices A ∧ x ∈ FootprintVertices B ∧ ∀ y, y = x ∨
            y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ → y ∈ FootprintVertices A ∨ y
            ∈ FootprintVertices B) → (x ∈ FootprintVertices U ∧ x ∈ FootprintVertices V ∧ ∀ y, y
            = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ → y ∈ FootprintVertices
            U ∨ y ∈ FootprintVertices V)) ) := by
  classical
  intro x U V hdiag diagonalCover
  rcases hdiag with hd | hd | hd | hd
  · exact diagonalCover U V (Or.inl hd)
  · exact diagonalCover U V (Or.inr hd)
  · obtain ⟨hV, hU, hcov⟩ := diagonalCover V U (Or.inl ⟨hd.2, hd.1⟩)
    exact ⟨hU, hV, fun y hy => (hcov y hy).symm⟩
  · obtain ⟨hV, hU, hcov⟩ := diagonalCover V U (Or.inr ⟨hd.2, hd.1⟩)
    exact ⟨hU, hV, fun y hy => (hcov y hy).symm⟩

end FordStarGeometry

theorem FordOpposingBoundaryStarLocalization
    (P : FordFareyParameter)
    (hq : ProperBandQuadruple (FordRecursiveQuadruple P))
    (C0 Ci : BandCircle) (i : Fin 3)
    (hC0 : (FordRecursiveQuadruple P) 0 = C0.1.1)
    (hCi : (FordRecursiveQuadruple P) i.succ = Ci.1.1)
    (T0 T0' : ProtoTile) (h0 h0' : PartialOdometer)
    (hO0 : TileOdometer C0.1.1 T0 h0)
    (hO0' : TileOdometer C0.1.1 T0' h0')
    (hlarge : 1 < Ci.1.1.1)
    (p0 p0' : Real × Real)
    (hs0 : PartialOdometerSlope h0 = some p0)
    (hs0' : PartialOdometerSlope h0' = some p0')
    (hcentroid : TileCentroid T0' - TileCentroid T0 =
      GaussianRealPoint
        (BandVectors.1 ((FordRecursiveQuadruple P) i.succ)
          ((FordRecursiveQuadruple P) 0)))
    (hslope : p0' - p0 =
      GaussianRealPoint
        (BandVectors.2 ((FordRecursiveQuadruple P) i.succ)
          ((FordRecursiveQuadruple P) 0)))
    (x : GaussianInt) (hx0 : x ∈ h0.domain) (hx0' : x ∈ h0'.domain)
    (hstar : ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
      y ∈ h0.domain ∨ y ∈ h0'.domain) :
    ∃ (U V : ProtoTile) (g k : PartialOdometer),
      AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0 ∧
      AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0' ∧
      LeftLatticeAdjacent Ci U V g k ∧
      x ∈ g.domain ∧ x ∈ k.domain ∧
      ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ g.domain ∨ y ∈ k.domain := by
-- BODY
  classical
  obtain ⟨hi2, hroot, hrpos, hne, u, hc, hc', hdis, hsegment⟩ :=
    P4158T1MatchedFordPair P C0 Ci i hC0 hCi T0 T0' h0 h0' hO0 hO0'
      hlarge hcentroid
  have hdom0 := PositiveCurvatureTileOdometerDomain C0.1.1 T0 h0 C0.2 hO0
  have hdom0' := PositiveCurvatureTileOdometerDomain C0.1.1 T0' h0' C0.2 hO0'
  have hxfoot := FordStarGeometry.hxfoot T0 T0' h0 h0' x hx0 hx0' hdom0 hdom0'
  obtain ⟨hxr, hxl, hxu⟩ := (hsegment x).mp hxfoot
  have squareCell (n : Nat) (v z : GaussianInt) :
      z ∈ (TileTranslation (FordTile n) v).cells ↔
        0 ≤ (z - v).re ∧ (z - v).re < (n : Int) ∧
        0 ≤ (z - v).im ∧ (z - v).im < (n : Int) := FordStarGeometry.squareCell n v z
  have hsum : (P.q : Int) = (P.q₁ : Int) + P.q₂ := by exact_mod_cast P.sum_q
  have hchosen : ∃ (U V : ProtoTile) (g k : PartialOdometer),
      AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0 ∧
      AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0' ∧
      LeftLatticeAdjacent Ci U V g k ∧
      ((x ∈ U.cells ∧ x - 1 - ⟨0, 1⟩ ∈ V.cells) ∨
       (x - 1 ∈ U.cells ∧ x - ⟨0, 1⟩ ∈ V.cells) ∨
       (x - 1 - ⟨0, 1⟩ ∈ U.cells ∧ x ∈ V.cells) ∨
       (x - ⟨0, 1⟩ ∈ U.cells ∧ x - 1 ∈ V.cells)) := by
    have smaller := FordStarGeometry.smaller P hq C0 Ci i hC0 hCi T0 T0' h0 h0' hO0 hO0' hlarge
        p0 p0' hs0 hs0' hcentroid hslope x hrpos u hc hc' hdis hsegment hxr hxl hxu
    fin_cases i
    · by_cases horder : P.q₂ < P.q₁
      · obtain ⟨U, V, g, k, s, t, Q, hAg, hAk, hUg, hVk, hsg, htk,
          hUc, hVc, hUV, hst, hQq, hQr, hQp, hQp1, hQ0, hQlarge⟩ :=
          P4158T1LargeFirstRestrictions P hq C0 Ci hC0 hCi hlarge horder
            T0 T0' h0 h0' hO0 hO0' p0 p0' hs0 hs0' hslope u hc (by simpa using hc')
        have cfg := (FordCoordinateConfiguration Q).2 hQlarge
        have hleft := FordStarGeometry.hleftAt319 P Ci horder U V g k s t Q hUg hVk hsg htk hUV
            hst hQq hQr hQp hQp1 hQ0 cfg
        refine ⟨U, V, g, k, hAg, hAk, hleft, Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))⟩
        · rw [hUc, squareCell]
          simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add,
            Zsqrtd.re_one, Zsqrtd.im_one] at hxr hxl hxu ⊢
          have hspos := P.q₂_pos
          norm_num at hxr hxl hxu ⊢
          omega
        · rw [hVc, squareCell]
          simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add] at hxr hxl hxu ⊢
          norm_num at hxr hxl hxu ⊢
          omega
      · exact smaller (Or.inl ⟨rfl, by omega⟩)
    · by_cases horder : P.q₁ < P.q₂
      · obtain ⟨U, V, g, k, s, t, Q, hAg, hAk, hUg, hVk, hsg, htk,
          hUc, hVc, hUV, hst, hQq, hQs, hQp, hQp2, hQ0, hQlarge⟩ :=
          P4158T1LargeSecondRestrictions P hq C0 Ci hC0 hCi hlarge horder
            T0 T0' h0 h0' hO0 hO0' p0 p0' hs0 hs0' hslope u hc (by simpa using hc')
        have cfg := (FordCoordinateConfiguration Q).2 hQlarge
        have hleft := FordStarGeometry.hleftAt345 P Ci horder U V g k s t Q hUg hVk hsg htk hUV
            hst hQq hQs hQp hQp2 hQ0 cfg
        refine ⟨U, V, g, k, hAg, hAk, hleft, Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))⟩
        · rw [hUc, squareCell]
          simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add] at hxr hxl hxu ⊢
          norm_num at hxr hxl hxu ⊢
          omega
        · rw [hVc, squareCell]
          simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add,
            Zsqrtd.re_one, Zsqrtd.im_one] at hxr hxl hxu ⊢
          norm_num at hxr hxl hxu ⊢
          omega
      · exact smaller (Or.inr ⟨rfl, by omega⟩)
    · exact (hi2 rfl).elim
  obtain ⟨U, V, g, k, hAg, hAk, hleft, hdiag⟩ := hchosen
  have hdomU := PositiveCurvatureTileOdometerDomain Ci.1.1 U g Ci.2 hleft.1
  have hdomV := PositiveCurvatureTileOdometerDomain Ci.1.1 V k Ci.2 hleft.2.1
  have hfootcover : x ∈ FootprintVertices U ∧ x ∈ FootprintVertices V ∧
      ∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨
        y = x - ⟨0, 1⟩ → y ∈ FootprintVertices U ∨ y ∈ FootprintVertices V :=
            FordStarGeometry.hfootcover x U V hdiag (FordStarGeometry.diagonalCover P i h0
            h0' x hstar u hxr hxl hxu (FordStarGeometry.corner))
  refine ⟨U, V, g, k, hAg, hAk, hleft, ?_, ?_, ?_⟩
  · change x ∈ (g.domain : Set GaussianInt)
    rw [hdomU]
    exact hfootcover.1
  · change x ∈ (k.domain : Set GaussianInt)
    rw [hdomV]
    exact hfootcover.2.1
  · intro y hy
    rcases hfootcover.2.2 y hy with hU | hV
    · left; change y ∈ (g.domain : Set GaussianInt); rwa [hdomU]
    · right; change y ∈ (k.domain : Set GaussianInt); rwa [hdomV]

end ApollonianSuperharmonic

end
