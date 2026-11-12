/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.LatticeAdjacentPackingSymmetryFacts
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileOdometerCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryAffineVectorCovariance


-- [TABLET NODE: LeftLatticeAdjacentPackingSymmetryTransport]

/-!
# LeftLatticeAdjacentPackingSymmetryTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LeftLatticeTransportGeometry

private theorem hcAt337 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (e : Bool), ∀ (T : ProtoTile), ∀ (T'
            : ProtoTile), (TileCentroid T' - TileCentroid T = (if e = true then (1 : ℝ) else (-1
            : ℝ)) • GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) → ((e =
            true) → (TileCentroid T' - TileCentroid T = GaussianRealPoint (BandVectors.1 (q
            i.succ) (q 0)))) ) := by
  classical
  intro q i e T T' hcent he
  simpa [he] using hcent

private theorem hcAt345 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (e : Bool), ∀ (T : ProtoTile), ∀ (T'
            : ProtoTile), (TileCentroid T' - TileCentroid T = (if e = true then (1 : ℝ) else (-1
            : ℝ)) • GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) → ((¬e =
            true) → (TileCentroid T' - TileCentroid T = GaussianRealPoint (-(BandVectors.1 (q
            i.succ) (q 0))))) ) := by
  classical
  intro q i e T T' hcent he
  simpa [he, GaussianRealPoint] using hcent

private theorem hscoordAt393 :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (T :
            ProtoTile), ∀ (T' : ProtoTile), ∀ (p : ℝ × ℝ), ∀ (p' : ℝ × ℝ),
            ((BandPackingSymmetrySlopeAction g T' p').1 - (BandPackingSymmetrySlopeAction g T
            p).1 = (↑(-BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2.re : ℝ) ∧
            (BandPackingSymmetrySlopeAction g T' p').2 - (BandPackingSymmetrySlopeAction g T p).2
            = (↑(-BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin
            (4 : ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2.im : ℝ)) →
            ((BandPackingSymmetrySlopeAction g T' p').1 - (BandPackingSymmetrySlopeAction g T
            p).1 = -((BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q 0),
            BandVectors.2 (q i.succ) (q 0))).2.re : ℝ)) ) := by
  classical
  intro g q i T T' p p' hs
  simpa using hs.1

private theorem hscoordAt451 :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (T :
            ProtoTile), ∀ (T' : ProtoTile), ∀ (p : ℝ × ℝ), ∀ (p' : ℝ × ℝ),
            ((BandPackingSymmetrySlopeAction g T' p').1 - (BandPackingSymmetrySlopeAction g T
            p).1 = (↑(-BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2.re : ℝ) ∧
            (BandPackingSymmetrySlopeAction g T' p').2 - (BandPackingSymmetrySlopeAction g T p).2
            = (↑(-BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin
            (4 : ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2.im : ℝ)) →
            ((BandPackingSymmetrySlopeAction g T' p').2 - (BandPackingSymmetrySlopeAction g T
            p).2 = -((BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q 0),
            BandVectors.2 (q i.succ) (q 0))).2.im : ℝ)) ) := by
  classical
  intro g q i T T' p p' hs
  simpa using hs.2

end LeftLatticeTransportGeometry

theorem LeftLatticeAdjacentPackingSymmetryTransport
    (g : BandPackingSymmetry) (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) (i : Fin 3) (e : Bool)
    (T T' : ProtoTile) (h h' : PartialOdometer) (p p' : ℝ × ℝ)
    (hO : TileOdometer (q 0) T h) (hO' : TileOdometer (q 0) T' h')
    (hp : PartialOdometerSlope h = some p)
    (hp' : PartialOdometerSlope h' = some p')
    (hcent : TileCentroid T' - TileCentroid T =
      (if e = true then (1 : ℝ) else -1) •
        GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)))
    (hslopeRe : p'.1 - p.1 =
      (if e = true then (1 : ℝ) else -1) *
        (BandVectors.2 (q i.succ) (q 0)).re)
    (hslopeIm : p'.2 - p.2 =
      (if e = true then (1 : ℝ) else -1) *
        (BandVectors.2 (q i.succ) (q 0)).im) :
    let q' := BandPackingSymmetryQuadrupleAction g q
    let sigma : Fin 3 → Fin 3 := fun j =>
      if BandPackingSymmetryReversesOrientation g then -j else j
    ∃ negative : Bool, ∃ r r' : ℝ × ℝ,
      BandPackingSymmetryScopedPhase g q negative ∧
      TileOdometer (q' 0) (BandPackingSymmetryTileAction g T)
          (BandPackingSymmetryPartialOdometerAction g h) ∧
      TileOdometer (q' 0) (BandPackingSymmetryTileAction g T')
          (BandPackingSymmetryPartialOdometerAction g h') ∧
      PartialOdometerSlope
          (BandPackingSymmetryPartialOdometerAction g h) = some r ∧
      PartialOdometerSlope
          (BandPackingSymmetryPartialOdometerAction g h') = some r' ∧
      TileCentroid (BandPackingSymmetryTileAction g T') -
          TileCentroid (BandPackingSymmetryTileAction g T) =
        (if xor e negative = true then (1 : ℝ) else -1) •
          GaussianRealPoint
            (BandVectors.1 (q' (sigma i).succ) (q' 0)) ∧
      r'.1 - r.1 =
        (if xor e negative = true then (1 : ℝ) else -1) *
          (BandVectors.2 (q' (sigma i).succ) (q' 0)).re ∧
      r'.2 - r.2 =
        (if xor e negative = true then (1 : ℝ) else -1) *
          (BandVectors.2 (q' (sigma i).succ) (q' 0)).im ∧
      (OdometerCompatibility
          (BandPackingSymmetryPartialOdometerAction g h)
          (BandPackingSymmetryPartialOdometerAction g h') ↔
        OdometerCompatibility h h') := by
-- BODY
  classical
  dsimp
  obtain ⟨negative, hphase, hvec⟩ :=
    BandPackingSymmetryAffineVectorCovariance g q hq
  have hTne := LatticeAdjacentPackingSymmetryFacts.tileCellsNonempty (q 0) T h p hO hp
  have hT'ne := LatticeAdjacentPackingSymmetryFacts.tileCellsNonempty (q 0) T' h' p' hO' hp'
  obtain ⟨hOT, _, hST⟩ := BandPackingSymmetryTileOdometerCovariance g (q 0) T h hO
  obtain ⟨hOT', _, hST'⟩ := BandPackingSymmetryTileOdometerCovariance g (q 0) T' h' hO'
  have hsr := LatticeAdjacentPackingSymmetryFacts.slopeAction g T h p hp hTne hST
  have hsr' := LatticeAdjacentPackingSymmetryFacts.slopeAction g T' h' p' hp' hT'ne hST'
  have centroid_transport : ∀ (a : BandPackingSymmetry) (U V : ProtoTile)
      (v : GaussianInt),
      TileCentroid V - TileCentroid U = GaussianRealPoint v →
      TileCentroid (BandPackingSymmetryTileAction a V) -
          TileCentroid (BandPackingSymmetryTileAction a U) =
        GaussianRealPoint (BandPackingSymmetryVectorAction a v) :=
            LatticeAdjacentPackingSymmetryFacts.centroidTransport
  have vector_sign (j : Fin 3) :
      GaussianRealPoint (BandPackingSymmetryVectorAction g
        (BandVectors.1 (q j.succ) (q 0))) =
        (if negative then (-1 : ℝ) else 1) •
          GaussianRealPoint
            (BandVectors.1
              (BandPackingSymmetryQuadrupleAction g q
                (if BandPackingSymmetryReversesOrientation g then -j else j).succ)
              (BandPackingSymmetryQuadrupleAction g q 0)) :=
                  LatticeAdjacentPackingSymmetryFacts.vectorSign g q negative hphase j
  have vector_neg : ∀ (a : BandPackingSymmetry) (v : GaussianInt),
      BandPackingSymmetryVectorAction a (-v) =
        -BandPackingSymmetryVectorAction a v := LatticeAdjacentPackingSymmetryFacts.vectorNegation
  have affine_neg : ∀ (a : BandPackingSymmetry) (v u : GaussianInt),
      BandPackingSymmetryAffineVectorAction a (-v, -u) =
        -BandPackingSymmetryAffineVectorAction a (v, u) :=
    LatticeAdjacentPackingSymmetryFacts.affineNegation
  have real_coord (z : GaussianInt) :
      (GaussianInt.toComplex z).re = (z.re : ℝ) :=
    (GaussianInt.intCast_re z).symm
  have imag_coord (z : GaussianInt) :
      (GaussianInt.toComplex z).im = (z.im : ℝ) :=
    (GaussianInt.intCast_im z).symm
  have slope_transport := LatticeAdjacentPackingSymmetryFacts.slopeTransport
  refine ⟨negative, BandPackingSymmetrySlopeAction g T p,
    BandPackingSymmetrySlopeAction g T' p', ?_⟩
  refine ⟨hphase, ?_, ?_, hsr, hsr', ?_, ?_, ?_, ?_⟩
  · simpa [BandPackingSymmetryQuadrupleAction] using hOT
  · simpa [BandPackingSymmetryQuadrupleAction] using hOT'
  · by_cases he : e = true
    · have hc : TileCentroid T' - TileCentroid T =
          GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) :=
              LeftLatticeTransportGeometry.hcAt337 q i e T T' hcent he
      rw [centroid_transport g T T'
        (BandVectors.1 (q i.succ) (q 0)) hc]
      by_cases hn : negative
      · simpa [he, hn, GaussianRealPoint] using vector_sign i
      · simpa [he, hn, GaussianRealPoint] using vector_sign i
    · have hc : TileCentroid T' - TileCentroid T =
          GaussianRealPoint (-(BandVectors.1 (q i.succ) (q 0))) :=
              LeftLatticeTransportGeometry.hcAt345 q i e T T' hcent he
      rw [centroid_transport g T T'
        (-(BandVectors.1 (q i.succ) (q 0))) hc]
      have hs := vector_sign i
      rw [vector_neg]
      by_cases hn : negative
      · simpa [he, hn, GaussianRealPoint] using congrArg Neg.neg hs
      · simpa [he, hn, GaussianRealPoint] using congrArg Neg.neg hs
  · by_cases he : e = true
    · have hc : TileCentroid T' - TileCentroid T =
          GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) :=
              LeftLatticeTransportGeometry.hcAt337 q i e T T' hcent he
      have hs := slope_transport g T T' p' p
        (BandVectors.1 (q i.succ) (q 0))
        (BandVectors.2 (q i.succ) (q 0)) hc
        (by simpa [he] using hslopeRe)
        (by simpa [he] using hslopeIm)
      have hv := (hvec i).1
      have hvr := congrArg (fun z : GaussianInt => (z.re : ℝ)) hv
      by_cases hn : negative
      · simp only [Int.reduceNeg, Fin.isValue, GaussianInt.intCast_re, hn, ↓reduceIte,
          neg_mul, one_mul, Zsqrtd.re_neg, Int.cast_neg, he, bne_self_eq_false,
          Bool.false_eq_true] at hvr ⊢
        rw [← GaussianInt.intCast_re] at ⊢
        have hcoord := hvr
        try simp only [real_coord] at hcoord
        linarith [hs.1, hcoord]
      · simp only [Int.reduceNeg, Fin.isValue, GaussianInt.intCast_re, hn, Bool.false_eq_true,
          ↓reduceIte, one_mul, he, Bool.bne_false] at hvr ⊢
        rw [← GaussianInt.intCast_re] at ⊢
        have hcoord := hvr
        try simp only [real_coord] at hcoord
        linarith [hs.1, hcoord]
    · have hc : TileCentroid T' - TileCentroid T =
          GaussianRealPoint (-(BandVectors.1 (q i.succ) (q 0))) :=
              LeftLatticeTransportGeometry.hcAt345 q i e T T' hcent he
      have hs := slope_transport g T T' p' p
        (-(BandVectors.1 (q i.succ) (q 0)))
        (-(BandVectors.2 (q i.succ) (q 0))) hc
        (by simpa [he, GaussianRealPoint] using hslopeRe)
        (by simpa [he, GaussianRealPoint] using hslopeIm)
      rw [affine_neg] at hs
      have hv := (hvec i).1
      have hvr := congrArg (fun z : GaussianInt => (z.re : ℝ)) hv
      by_cases hn : negative
      · simp only [Int.reduceNeg, Fin.isValue, GaussianInt.intCast_re, hn, ↓reduceIte,
          neg_mul, one_mul, Zsqrtd.re_neg, Int.cast_neg, he, Bool.bne_true, Bool.not_false]
          at hvr ⊢
        try rw [← GaussianInt.intCast_re] at ⊢
        have hcoord := hvr
        try simp only [real_coord] at hcoord
        have hscoord :
            (BandPackingSymmetrySlopeAction g T' p').1 -
                (BandPackingSymmetrySlopeAction g T p).1 =
              -((BandPackingSymmetryAffineVectorAction g
                (BandVectors.1 (q i.succ) (q 0),
                  BandVectors.2 (q i.succ) (q 0))).2.re : ℝ) :=
                      LeftLatticeTransportGeometry.hscoordAt393 g q i T T' p p' hs
        linarith [hscoord, hcoord]
      · simp only [Int.reduceNeg, Fin.isValue, GaussianInt.intCast_re, hn, Bool.false_eq_true,
          ↓reduceIte, one_mul, he, bne_self_eq_false, neg_mul] at hvr ⊢
        try rw [← GaussianInt.intCast_re] at ⊢
        have hcoord := hvr
        try simp only [real_coord] at hcoord
        have hscoord :
            (BandPackingSymmetrySlopeAction g T' p').1 -
                (BandPackingSymmetrySlopeAction g T p).1 =
              -((BandPackingSymmetryAffineVectorAction g
                (BandVectors.1 (q i.succ) (q 0),
                  BandVectors.2 (q i.succ) (q 0))).2.re : ℝ) :=
                      LeftLatticeTransportGeometry.hscoordAt393 g q i T T' p p' hs
        linarith [hscoord, hcoord]
  · by_cases he : e = true
    · have hc : TileCentroid T' - TileCentroid T =
          GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) :=
              LeftLatticeTransportGeometry.hcAt337 q i e T T' hcent he
      have hs := slope_transport g T T' p' p
        (BandVectors.1 (q i.succ) (q 0))
        (BandVectors.2 (q i.succ) (q 0)) hc
        (by simpa [he] using hslopeRe)
        (by simpa [he] using hslopeIm)
      have hv := (hvec i).1
      have hvi := congrArg (fun z : GaussianInt => (z.im : ℝ)) hv
      by_cases hn : negative
      · simp only [Int.reduceNeg, Fin.isValue, GaussianInt.intCast_im, hn, ↓reduceIte,
          neg_mul, one_mul, Zsqrtd.im_neg, Int.cast_neg, he, bne_self_eq_false,
          Bool.false_eq_true] at hvi ⊢
        rw [← GaussianInt.intCast_im] at ⊢
        have hcoord := hvi
        try simp only [imag_coord] at hcoord
        linarith [hs.2, hcoord]
      · simp only [Int.reduceNeg, Fin.isValue, GaussianInt.intCast_im, hn, Bool.false_eq_true,
          ↓reduceIte, one_mul, he, Bool.bne_false] at hvi ⊢
        rw [← GaussianInt.intCast_im] at ⊢
        have hcoord := hvi
        try simp only [imag_coord] at hcoord
        linarith [hs.2, hcoord]
    · have hc : TileCentroid T' - TileCentroid T =
          GaussianRealPoint (-(BandVectors.1 (q i.succ) (q 0))) :=
              LeftLatticeTransportGeometry.hcAt345 q i e T T' hcent he
      have hs := slope_transport g T T' p' p
        (-(BandVectors.1 (q i.succ) (q 0)))
        (-(BandVectors.2 (q i.succ) (q 0))) hc
        (by simpa [he, GaussianRealPoint] using hslopeRe)
        (by simpa [he, GaussianRealPoint] using hslopeIm)
      rw [affine_neg] at hs
      have hv := (hvec i).1
      have hvi := congrArg (fun z : GaussianInt => (z.im : ℝ)) hv
      by_cases hn : negative
      · simp only [Int.reduceNeg, Fin.isValue, GaussianInt.intCast_im, hn, ↓reduceIte,
          neg_mul, one_mul, Zsqrtd.im_neg, Int.cast_neg, he, Bool.bne_true, Bool.not_false]
          at hvi ⊢
        try rw [← GaussianInt.intCast_im] at ⊢
        have hcoord := hvi
        try simp only [imag_coord] at hcoord
        have hscoord :
            (BandPackingSymmetrySlopeAction g T' p').2 -
                (BandPackingSymmetrySlopeAction g T p).2 =
              -((BandPackingSymmetryAffineVectorAction g
                (BandVectors.1 (q i.succ) (q 0),
                  BandVectors.2 (q i.succ) (q 0))).2.im : ℝ) :=
                      LeftLatticeTransportGeometry.hscoordAt451 g q i T T' p p' hs
        linarith [hscoord, hcoord]
      · simp only [Int.reduceNeg, Fin.isValue, GaussianInt.intCast_im, hn, Bool.false_eq_true,
          ↓reduceIte, one_mul, he, bne_self_eq_false, neg_mul] at hvi ⊢
        try rw [← GaussianInt.intCast_im] at ⊢
        have hcoord := hvi
        try simp only [imag_coord] at hcoord
        have hscoord :
            (BandPackingSymmetrySlopeAction g T' p').2 -
                (BandPackingSymmetrySlopeAction g T p).2 =
              -((BandPackingSymmetryAffineVectorAction g
                (BandVectors.1 (q i.succ) (q 0),
                  BandVectors.2 (q i.succ) (q 0))).2.im : ℝ) :=
                      LeftLatticeTransportGeometry.hscoordAt451 g q i T T' p p' hs
        linarith [hscoord, hcoord]
  · exact (BandPackingSymmetryPartialOdometerActionFormulas g h h').2.2.2.2.2.2.1

end ApollonianSuperharmonic

end
