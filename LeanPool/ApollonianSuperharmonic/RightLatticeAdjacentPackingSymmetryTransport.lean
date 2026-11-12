/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5625T1CentroidSlopeDifferenceCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryScopedPhase
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileOdometerCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileAction

-- [TABLET NODE: RightLatticeAdjacentPackingSymmetryTransport]

/-!
# RightLatticeAdjacentPackingSymmetryTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RightLatticeTransportGeometry

private theorem hTne :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (T : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (p : ℝ × ℝ), (TileOdometer (q (0 : Fin (4 : ℕ))) T h) →
            ((PartialOdometerSlope h = some p) → (T.cells.Nonempty))) ) := by
  classical
  intro q hq T h p hO hp
  have hd := PositiveCurvatureTileOdometerDomain (q 0) T h
    (ProperBandCurvatureStructure q hq).1 hO
  by_contra hn
  have hde : (h.domain : Set GaussianInt) = {T.anchor} := by
    rw [hd]
    simp [FootprintVertices, hn]
  have hs : (PartialOdometerSquares h).Nonempty := by
    by_contra hs
    simp [PartialOdometerSlope, hs] at hp
  rcases hs with ⟨x, hx⟩
  simp only [PartialOdometerSquares, Finset.mem_filter] at hx
  have hz : x + 1 = T.anchor := by
    apply Set.mem_singleton_iff.mp
    rw [← hde]
    exact hx.2.1
  have hz0 : x = T.anchor := by
    apply Set.mem_singleton_iff.mp
    rw [← hde]
    exact hx.1
  have hzbad : x + 1 = x := hz.trans hz0.symm
  have hzbad' := congrArg (fun z : GaussianInt => z.re) hzbad
  norm_num at hzbad'

private theorem hT'ne :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (∀ (T' : ProtoTile), ∀ (h' :
            PartialOdometer), ∀ (p' : ℝ × ℝ), (TileOdometer (q (0 : Fin (4 : ℕ))) T' h') →
            ((PartialOdometerSlope h' = some p') → (T'.cells.Nonempty))) ) := by
  classical
  intro q hq T' h' p' hO' hp'
  have hd := PositiveCurvatureTileOdometerDomain (q 0) T' h'
    (ProperBandCurvatureStructure q hq).1 hO'
  by_contra hn
  have hde : (h'.domain : Set GaussianInt) = {T'.anchor} := by
    rw [hd]
    simp [FootprintVertices, hn]
  have hs : (PartialOdometerSquares h').Nonempty := by
    by_contra hs
    simp [PartialOdometerSlope, hs] at hp'
  rcases hs with ⟨x, hx⟩
  simp only [PartialOdometerSquares, Finset.mem_filter] at hx
  have hz : x + 1 = T'.anchor := by
    apply Set.mem_singleton_iff.mp
    rw [← hde]
    exact hx.2.1
  have hz0 : x = T'.anchor := by
    apply Set.mem_singleton_iff.mp
    rw [← hde]
    exact hx.1
  have hzbad : x + 1 = x := hz.trans hz0.symm
  have hzbad' := congrArg (fun z : GaussianInt => z.re) hzbad
  norm_num at hzbad'

private theorem hsr :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (p : ℝ × ℝ),
            (PartialOdometerSlope h = some p) → ((T.cells.Nonempty) → ((Finset.Nonempty T.cells →
            PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g h) = Option.map
            (BandPackingSymmetrySlopeAction g T) (PartialOdometerSlope h)) →
            (PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g h) = some
            (BandPackingSymmetrySlopeAction g T p)))) ) := by
  classical
  intro g T h p hp hTne hST
  simpa [Option.map] using (hST hTne).trans (congrArg (Option.map
    (BandPackingSymmetrySlopeAction g T)) hp)

private theorem hsr' :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (T' : ProtoTile), ∀ (h' : PartialOdometer), ∀ (p' : ℝ ×
            ℝ), (PartialOdometerSlope h' = some p') → ((T'.cells.Nonempty) → ((Finset.Nonempty
            T'.cells → PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g h') =
            Option.map (BandPackingSymmetrySlopeAction g T') (PartialOdometerSlope h')) →
            (PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g h') = some
            (BandPackingSymmetrySlopeAction g T' p')))) ) := by
  classical
  intro g T' h' p' hp' hT'ne hST'
  simpa [Option.map] using (hST' hT'ne).trans (congrArg (Option.map
    (BandPackingSymmetrySlopeAction g T')) hp')

private theorem centroid_transport :
    (by
      classical
      exact
        ∀ (a : BandPackingSymmetry), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (v : GaussianInt),
            TileCentroid V - TileCentroid U = GaussianRealPoint v → TileCentroid
            (BandPackingSymmetryTileAction a V) - TileCentroid (BandPackingSymmetryTileAction a
            U) = GaussianRealPoint (BandPackingSymmetryVectorAction a v) ) := by
  classical
  intro a U V v hv
  have hc := (P5625T1CentroidSlopeDifferenceCovariance.2
    a U V (0, 0) (0, 0) v 0 1
    (by simpa using hv) (by ext <;> simp [GaussianRealPoint])).1
  simpa only [one_smul, P5625T1CentroidSlopeDifferenceCovariance.1] using hc

private theorem vector_signAt246 :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), ∀ (negative : Bool),
            (BandPackingSymmetryScopedPhase g q negative) → (∀ (j : Fin 3), GaussianRealPoint
            (BandPackingSymmetryVectorAction g (BandVectors.1 (q j.succ) (q 0))) = (if negative
            then (-1 : ℝ) else 1) • GaussianRealPoint (BandVectors.1
            (BandPackingSymmetryQuadrupleAction g q (if BandPackingSymmetryReversesOrientation g
            then -j else j).succ) (BandPackingSymmetryQuadrupleAction g q 0))) ) := by
  classical
  intro g q negative hphase j
  have hp := hphase j
  dsimp [BandPackingSymmetryScopedPhase] at hp
  have hv := hp.1
  by_cases hn : negative
  · have hh := congrArg Neg.neg (congrArg GaussianRealPoint hv)
    simpa [hn, GaussianRealPoint] using hh.symm
  · have hh := (congrArg GaussianRealPoint hv).symm
    simpa [hn, GaussianRealPoint] using hh

private theorem vector_neg :
    (by
      classical
      exact
        ∀ (a : BandPackingSymmetry), ∀ (v : GaussianInt), BandPackingSymmetryVectorAction a (-v)
            = -BandPackingSymmetryVectorAction a v ) := by
  classical
  intro a
  induction a with
  | identity => intro v; rfl
  | negate =>
      intro v
      rcases v with ⟨a, b⟩
      rfl
  | conjugate =>
      intro v
      rcases v with ⟨a, b⟩
      rfl
  | shift w => intro v; rfl
  | comp a b iha ihb =>
      intro v
      change BandPackingSymmetryVectorAction a
          (BandPackingSymmetryVectorAction b (-v)) =
        -BandPackingSymmetryVectorAction a
          (BandPackingSymmetryVectorAction b v)
      rw [ihb, iha]

private theorem affine_neg :
    (by
      classical
      exact
        ∀ (a : BandPackingSymmetry), ∀ (v : GaussianInt), ∀ (u : GaussianInt),
            BandPackingSymmetryAffineVectorAction a (-v, -u) =
            -BandPackingSymmetryAffineVectorAction a (v, u) ) := by
  classical
  intro a
  induction a with
  | identity => intro v u; rfl
  | shift w =>
      intro v u
      rcases v with ⟨va, vb⟩
      rcases u with ⟨ua, ub⟩
      rcases w with ⟨wa, wb⟩
      apply Prod.ext
      · simp [BandPackingSymmetryAffineVectorAction, GaussianReflection]
      · simp only [BandPackingSymmetryAffineVectorAction, Int.reduceNeg, GaussianReflection,
          Zsqrtd.re_neg, Zsqrtd.im_neg, neg_neg, Prod.neg_mk, neg_add_rev]
        have hrel : ({re := -va, im := vb} : GaussianInt) =
            -({re := va, im := -vb} : GaussianInt) := by
          ext <;> simp
        rw [hrel]
        ring
  | negate =>
      intro v u
      rcases v with ⟨va, vb⟩
      rcases u with ⟨ua, ub⟩
      rfl
  | conjugate =>
      intro v u
      rcases v with ⟨va, vb⟩
      rcases u with ⟨ua, ub⟩
      rfl
  | comp a b iha ihb =>
      intro v u
      change BandPackingSymmetryAffineVectorAction a
          (BandPackingSymmetryAffineVectorAction b (-v, -u)) = _
      rw [ihb]
      apply iha

private theorem slope_transport :
    (by
      classical
      exact
        ∀ (a : BandPackingSymmetry), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : ℝ × ℝ), ∀ (y :
            ℝ × ℝ), ∀ (v : GaussianInt), ∀ (u : GaussianInt), TileCentroid V - TileCentroid U =
            GaussianRealPoint v → x.1 - y.1 = (u.re : ℝ) → x.2 - y.2 = (u.im : ℝ) →
            (BandPackingSymmetrySlopeAction a V x).1 - (BandPackingSymmetrySlopeAction a U y).1 =
            (BandPackingSymmetryAffineVectorAction a (v, u)).2.re ∧
            (BandPackingSymmetrySlopeAction a V x).2 - (BandPackingSymmetrySlopeAction a U y).2 =
            (BandPackingSymmetryAffineVectorAction a (v, u)).2.im ) := by
  classical
  intro a U V x y v u hc hx hy
  have hp : x - y = (1 : ℝ) • GaussianRealPoint u := by
    apply Prod.ext
    · simpa [GaussianRealPoint] using hx
    · simpa [GaussianRealPoint] using hy
  have hs := (P5625T1CentroidSlopeDifferenceCovariance.2
    a U V x y v u 1 (by simpa using hc) hp).2
  constructor
  · simpa [GaussianRealPoint] using congrArg Prod.fst hs
  · simpa [GaussianRealPoint] using congrArg Prod.snd hs

private theorem vector_signAt350 :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), ∀ (negative : Bool),
            (BandPackingSymmetryScopedPhase g q negative) → (∀ (j : Fin 3), GaussianRealPoint
            (BandPackingSymmetryVectorAction g (BandVectors.1 (q 0) (q j.succ))) = (if xor
            negative (BandPackingSymmetryReversesOrientation g) = true then (-1 : ℝ) else 1) •
            GaussianRealPoint (BandVectors.1 (BandPackingSymmetryQuadrupleAction g q 0)
            (BandPackingSymmetryQuadrupleAction g q (if BandPackingSymmetryReversesOrientation g
            then -j else j).succ))) ) := by
  classical
  intro g q negative hphase j
  have hp := hphase j
  dsimp [BandPackingSymmetryScopedPhase] at hp
  have hv := hp.2.1
  by_cases hn : negative
  · by_cases hr : BandPackingSymmetryReversesOrientation g = true
    · simpa [hn, hr, GaussianRealPoint] using
        (congrArg GaussianRealPoint hv).symm
    · simpa [hn, hr, GaussianRealPoint] using
        congrArg Neg.neg (congrArg GaussianRealPoint hv).symm
  · by_cases hr : BandPackingSymmetryReversesOrientation g = true
    · simpa [hn, hr, GaussianRealPoint] using
        congrArg Neg.neg (congrArg GaussianRealPoint hv).symm
    · simpa [hn, hr, GaussianRealPoint] using
        (congrArg GaussianRealPoint hv).symm

private theorem vector_flip :
    (by
      classical
      exact
        (∀ (a : BandPackingSymmetry), ∀ (v : GaussianInt), BandPackingSymmetryVectorAction a (-v)
            = -BandPackingSymmetryVectorAction a v) → (∀ (a : BandPackingSymmetry), ∀ (v :
            GaussianInt), BandPackingSymmetryVectorAction a (GaussianQuarterTurn v) = (if
            BandPackingSymmetryReversesOrientation a then -GaussianQuarterTurn
            (BandPackingSymmetryVectorAction a v) else GaussianQuarterTurn
            (BandPackingSymmetryVectorAction a v))) ) := by
  classical
  intro vector_neg a
  induction a with
  | identity => intro v; rfl
  | shift w => intro v; rfl
  | negate => intro v; rfl
  | conjugate =>
      intro v
      rcases v with ⟨va,vb⟩
      simp [BandPackingSymmetryVectorAction,
        BandPackingSymmetryReversesOrientation, GaussianQuarterTurn,
        GaussianReflection]
  | comp a b iha ihb =>
      intro v
      change BandPackingSymmetryVectorAction a
          (BandPackingSymmetryVectorAction b (GaussianQuarterTurn v)) = _
      rw [ihb]
      by_cases ha : BandPackingSymmetryReversesOrientation a = true
      · by_cases hb : BandPackingSymmetryReversesOrientation b = true
        · simp only [ite_eq_left hb]
          rw [vector_neg, iha]
          simp [ha, hb, BandPackingSymmetryReversesOrientation,
            BandPackingSymmetryVectorAction, GaussianQuarterTurn]
        · simp only [ite_eq_right hb]
          rw [iha]
          simp [ha, hb, BandPackingSymmetryReversesOrientation,
            BandPackingSymmetryVectorAction, GaussianQuarterTurn]
      · by_cases hb : BandPackingSymmetryReversesOrientation b = true
        · simp only [ite_eq_left hb]
          rw [vector_neg, iha]
          simp [ha, hb, BandPackingSymmetryReversesOrientation,
            BandPackingSymmetryVectorAction, GaussianQuarterTurn]
        · simp only [ite_eq_right hb]
          rw [iha]
          simp [ha, hb, BandPackingSymmetryReversesOrientation,
            BandPackingSymmetryVectorAction, GaussianQuarterTurn]

private theorem affine_flip_second :
    (by
      classical
      exact
        (∀ (a : BandPackingSymmetry), ∀ (v : GaussianInt), ∀ (u : GaussianInt),
            BandPackingSymmetryAffineVectorAction a (-v, -u) =
            -BandPackingSymmetryAffineVectorAction a (v, u)) → ((∀ (a : BandPackingSymmetry), ∀
            (v : GaussianInt), ∀ (u : GaussianInt), (BandPackingSymmetryAffineVectorAction a (v,
            u)).1 = BandPackingSymmetryVectorAction a v) → ((∀ (a : BandPackingSymmetry), ∀ (v :
            GaussianInt), BandPackingSymmetryVectorAction a (GaussianQuarterTurn v) = (if
            BandPackingSymmetryReversesOrientation a then -GaussianQuarterTurn
            (BandPackingSymmetryVectorAction a v) else GaussianQuarterTurn
            (BandPackingSymmetryVectorAction a v))) → (∀ (a : BandPackingSymmetry), ∀ (v :
            GaussianInt), ∀ (u : GaussianInt), (BandPackingSymmetryAffineVectorAction a
            (GaussianQuarterTurn v, -GaussianQuarterTurn u)).2 = (if
            BandPackingSymmetryReversesOrientation a then GaussianQuarterTurn
            (BandPackingSymmetryAffineVectorAction a (v,u)).2 else -GaussianQuarterTurn
            (BandPackingSymmetryAffineVectorAction a (v,u)).2)))) ) := by
  classical
  intro affine_neg affine_first vector_flip a
  induction a with
  | identity => intro v u; rfl
  | shift w =>
      intro v u
      rcases v with ⟨va,vb⟩
      rcases u with ⟨ua,ub⟩
      rcases w with ⟨wa,wb⟩
      simp only [BandPackingSymmetryAffineVectorAction, GaussianQuarterTurn, Int.reduceNeg,
          GaussianReflection, BandPackingSymmetryReversesOrientation, Bool.false_eq_true,
          ↓reduceIte, Zsqrtd.im_add, Zsqrtd.im_mul, mul_neg, neg_add_rev, neg_neg,
          Zsqrtd.re_add, Zsqrtd.re_mul, neg_mul, one_mul]
      ext <;> simp; ring
  | negate =>
      intro v u
      rcases v with ⟨va,vb⟩
      rcases u with ⟨ua,ub⟩
      rfl
  | conjugate =>
      intro v u
      rcases v with ⟨va,vb⟩
      rcases u with ⟨ua,ub⟩
      simp only [BandPackingSymmetryAffineVectorAction, GaussianReflection, Int.reduceNeg,
          GaussianQuarterTurn, Zsqrtd.re_neg, neg_neg, Zsqrtd.im_neg,
          BandPackingSymmetryReversesOrientation, ↓reduceIte]
      ext <;> simp
  | comp a b iha ihb =>
      intro v u
      change (BandPackingSymmetryAffineVectorAction a
          (BandPackingSymmetryAffineVectorAction b
            (GaussianQuarterTurn v, -GaussianQuarterTurn u))).2 = _
      have hb1 := vector_flip b v
      have hb2 := ihb v u
      have hpair : BandPackingSymmetryAffineVectorAction b
          (GaussianQuarterTurn v, -GaussianQuarterTurn u) =
          (BandPackingSymmetryVectorAction b (GaussianQuarterTurn v),
            (BandPackingSymmetryAffineVectorAction b
              (GaussianQuarterTurn v, -GaussianQuarterTurn u)).2) := by
        apply Prod.ext
        · exact affine_first b (GaussianQuarterTurn v) (-GaussianQuarterTurn u)
        · rfl
      rw [hpair]
      rw [hb1, hb2]
      by_cases ha : BandPackingSymmetryReversesOrientation a = true
      · by_cases hb : BandPackingSymmetryReversesOrientation b = true
        · have hp : (-GaussianQuarterTurn (BandPackingSymmetryVectorAction b v),
              GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction b (v,u)).2) =
              -(GaussianQuarterTurn (BandPackingSymmetryVectorAction b v),
                -GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction b (v,u)).2) := by
            ext <;> simp
          simp only [ite_eq_left hb]
          change (BandPackingSymmetryAffineVectorAction a
            (-GaussianQuarterTurn (BandPackingSymmetryVectorAction b v),
             GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction b (v,u)).2)).2 = _
          have hn : (-GaussianQuarterTurn (BandPackingSymmetryVectorAction b v),
              GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction b (v,u)).2) =
              (-GaussianQuarterTurn (BandPackingSymmetryVectorAction b v),
               -(-GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction b (v,u)).2)) := by
            ext <;> simp
          rw [hn, affine_neg]
          change -((BandPackingSymmetryAffineVectorAction a
            (GaussianQuarterTurn (BandPackingSymmetryVectorAction b v),
             -GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction b (v,u)).2)).2) = _
          rw [iha]
          have hpair2 : (BandPackingSymmetryVectorAction b v,
              (BandPackingSymmetryAffineVectorAction b (v,u)).2) =
              BandPackingSymmetryAffineVectorAction b (v,u) := by
            apply Prod.ext
            · exact (affine_first b v u).symm
            · rfl
          rw [hpair2]
          simp [ha, hb, BandPackingSymmetryReversesOrientation,
            BandPackingSymmetryAffineVectorAction, GaussianQuarterTurn]
        · simp only [ite_eq_right hb]
          change (BandPackingSymmetryAffineVectorAction a
            (GaussianQuarterTurn (BandPackingSymmetryVectorAction b v),
             -GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction b (v,u)).2)).2 = _
          rw [iha]
          have hpair2 : (BandPackingSymmetryVectorAction b v,
              (BandPackingSymmetryAffineVectorAction b (v,u)).2) =
              BandPackingSymmetryAffineVectorAction b (v,u) := by
            apply Prod.ext
            · exact (affine_first b v u).symm
            · rfl
          rw [hpair2]
          simp [ha, hb, BandPackingSymmetryReversesOrientation,
            BandPackingSymmetryAffineVectorAction, GaussianQuarterTurn]
      · by_cases hb : BandPackingSymmetryReversesOrientation b = true
        · have hp : (-GaussianQuarterTurn (BandPackingSymmetryVectorAction b v),
              GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction b (v,u)).2) =
              -(GaussianQuarterTurn (BandPackingSymmetryVectorAction b v),
                -GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction b (v,u)).2) := by
            ext <;> simp
          simp only [ite_eq_left hb]
          change (BandPackingSymmetryAffineVectorAction a
            (-GaussianQuarterTurn (BandPackingSymmetryVectorAction b v),
             GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction b (v,u)).2)).2 = _
          have hn : (-GaussianQuarterTurn (BandPackingSymmetryVectorAction b v),
              GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction b (v,u)).2) =
              (-GaussianQuarterTurn (BandPackingSymmetryVectorAction b v),
               -(-GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction b (v,u)).2)) := by
            ext <;> simp
          rw [hn, affine_neg]
          change -((BandPackingSymmetryAffineVectorAction a
            (GaussianQuarterTurn (BandPackingSymmetryVectorAction b v),
             -GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction b (v,u)).2)).2) = _
          rw [iha]
          have hpair2 : (BandPackingSymmetryVectorAction b v,
              (BandPackingSymmetryAffineVectorAction b (v,u)).2) =
              BandPackingSymmetryAffineVectorAction b (v,u) := by
            apply Prod.ext
            · exact (affine_first b v u).symm
            · rfl
          rw [hpair2]
          simp [ha, hb, BandPackingSymmetryReversesOrientation,
            BandPackingSymmetryAffineVectorAction, GaussianQuarterTurn]
        · simp only [ite_eq_right hb]
          change (BandPackingSymmetryAffineVectorAction a
            (GaussianQuarterTurn (BandPackingSymmetryVectorAction b v),
             -GaussianQuarterTurn (BandPackingSymmetryAffineVectorAction b (v,u)).2)).2 = _
          rw [iha]
          have hpair2 : (BandPackingSymmetryVectorAction b v,
              (BandPackingSymmetryAffineVectorAction b (v,u)).2) =
              BandPackingSymmetryAffineVectorAction b (v,u) := by
            apply Prod.ext
            · exact (affine_first b v u).symm
            · rfl
          rw [hpair2]
          simp [ha, hb, BandPackingSymmetryReversesOrientation,
            BandPackingSymmetryAffineVectorAction, GaussianQuarterTurn]

private theorem newIndex_eq :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (i : Fin 3),
        let newIndex : Fin 3 :=
          if BandPackingSymmetryReversesOrientation g then -i else i
        newIndex = (if BandPackingSymmetryReversesOrientation g = true then -i else i) ) := by
  classical
  intro g i newIndex
  simp [newIndex]

private theorem turn_mul :
    (by
      classical
      exact
        ∀ (z : GaussianInt), (⟨0, 1⟩ : GaussianInt) * z = GaussianQuarterTurn z ) := by
  classical
  intro z
  rcases z with ⟨a, b⟩
  ext <;> simp [GaussianQuarterTurn]

private theorem neg_turn_mul :
    (by
      classical
      exact
        (∀ (z : GaussianInt), (⟨0, 1⟩ : GaussianInt) * z = GaussianQuarterTurn z) → (∀ (z :
            GaussianInt), -((⟨0, 1⟩ : GaussianInt) * z) = -GaussianQuarterTurn z) ) := by
  classical
  intro turn_mul z
  rw [turn_mul]

private theorem neg_turn_mul' :
    (by
      classical
      exact
        ∀ (z : GaussianInt), (-(⟨0, 1⟩ : GaussianInt)) * z = -GaussianQuarterTurn z ) := by
  classical
  intro z
  rcases z with ⟨a, b⟩
  ext <;> simp [GaussianQuarterTurn]

private theorem oldPair :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), (BandVectors.2 (q (0 : Fin (4 : ℕ))) (q
            i.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (q i.succ) (q (0 : Fin
            (4 : ℕ)))) → ((BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) * BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) → ((∀ (z :
            GaussianInt), (⟨0, 1⟩ : GaussianInt) * z = GaussianQuarterTurn z) → ((∀ (z :
            GaussianInt), (-(⟨0, 1⟩ : GaussianInt)) * z = -GaussianQuarterTurn z) →
            ((BandVectors.1 (q 0) (q i.succ), BandVectors.2 (q 0) (q i.succ)) =
            (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0)), -GaussianQuarterTurn
            (BandVectors.2 (q i.succ) (q 0))))))) ) := by
  classical
  intro q i oldFlip oldFlipVec turn_mul neg_turn_mul'
  apply Prod.ext
  · rw [turn_mul] at oldFlipVec
    exact oldFlipVec
  · rw [neg_turn_mul'] at oldFlip
    exact oldFlip

private theorem hcAt631 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (e : Bool), ∀ (T : ProtoTile), ∀ (T'
            : ProtoTile), (TileCentroid T' - TileCentroid T = (if e = true then (1 : ℝ) else (-1
            : ℝ)) • GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → ((e =
            true) → (TileCentroid T' - TileCentroid T = GaussianRealPoint (BandVectors.1 (q 0) (q
            i.succ)))) ) := by
  classical
  intro q i e T T' hcent he
  simpa [he] using hcent

private theorem hcAt637 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (e : Bool), ∀ (T : ProtoTile), ∀ (T'
            : ProtoTile), (TileCentroid T' - TileCentroid T = (if e = true then (1 : ℝ) else (-1
            : ℝ)) • GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → ((¬e =
            true) → (TileCentroid T' - TileCentroid T = GaussianRealPoint (-(BandVectors.1 (q 0)
            (q i.succ))))) ) := by
  classical
  intro q i e T T' hcent he
  simpa [he, GaussianRealPoint] using hcent

private theorem hcAt647 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (e : Bool), ∀ (T : ProtoTile), ∀ (T'
            : ProtoTile), (TileCentroid T' - TileCentroid T = (if e = true then (1 : ℝ) else (-1
            : ℝ)) • GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → ((e =
            true) → (TileCentroid T' - TileCentroid T = GaussianRealPoint (BandVectors.1 (q 0) (q
            i.succ)))) ) := by
  classical
  intro q i e T T' hcent he
  simpa [he] using hcent

private theorem hcAt695 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (e : Bool), ∀ (T : ProtoTile), ∀ (T'
            : ProtoTile), (TileCentroid T' - TileCentroid T = (if e = true then (1 : ℝ) else (-1
            : ℝ)) • GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → ((¬e =
            true) → (TileCentroid T' - TileCentroid T = GaussianRealPoint (-(BandVectors.1 (q 0)
            (q i.succ))))) ) := by
  classical
  intro q i e T T' hcent he
  simpa [he, GaussianRealPoint] using hcent

private theorem hcAt742 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (e : Bool), ∀ (T : ProtoTile), ∀ (T'
            : ProtoTile), (TileCentroid T' - TileCentroid T = (if e = true then (1 : ℝ) else (-1
            : ℝ)) • GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → ((e =
            true) → (TileCentroid T' - TileCentroid T = GaussianRealPoint (BandVectors.1 (q 0) (q
            i.succ)))) ) := by
  classical
  intro q i e T T' hcent he
  simpa [he] using hcent

private theorem hcAt785 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (e : Bool), ∀ (T : ProtoTile), ∀ (T'
            : ProtoTile), (TileCentroid T' - TileCentroid T = (if e = true then (1 : ℝ) else (-1
            : ℝ)) • GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → ((¬e =
            true) → (TileCentroid T' - TileCentroid T = GaussianRealPoint (-(BandVectors.1 (q 0)
            (q i.succ))))) ) := by
  classical
  intro q i e T T' hcent he
  simpa [he, GaussianRealPoint] using hcent

end RightLatticeTransportGeometry

namespace RightAdjacencyAssembly

private theorem transportedAdjacency :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates), ∀ (i : Fin 3), ∀ (e :
            Bool), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (h : PartialOdometer), ∀ (h' :
            PartialOdometer), ∀ (p : ℝ × ℝ), ∀ (p' : ℝ × ℝ), (TileCentroid T' - TileCentroid T =
            (if e = true then (1 : ℝ) else (-1 : ℝ)) • GaussianRealPoint (BandVectors.1 (q (0 :
            Fin (4 : ℕ))) (q i.succ))) → ((p'.1 - p.1 = (if e = true then (1 : ℝ) else (-1 : ℝ))
            * (↑(BandVectors.2 (q (0 : Fin (4 : ℕ))) (q i.succ)).re : ℝ)) → ((p'.2 - p.2 = (if e
            = true then (1 : ℝ) else (-1 : ℝ)) * (↑(BandVectors.2 (q (0 : Fin (4 : ℕ))) (q
            i.succ)).im : ℝ)) → (∀ (negative : Bool), (BandPackingSymmetryScopedPhase g q
            negative) → ((∀ (i : Fin (3 : ℕ)),
        let e := if negative = true then (-1 : GaussianInt) else (1 : GaussianInt);
        let incoming := BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))));
        let cyclic := BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q (i + (2 : Fin (3
            : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ), BandVectors.2 (q (i + (2 : Fin (3 :
            ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ)); BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q ((fun (i : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -i else i) i).succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ))) = e * incoming.2 ∧
            BandVectors.2 (BandPackingSymmetryQuadrupleAction g q ((fun (i : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -i else i) i + (2 : Fin (3 :
            ℕ))).succ) (BandPackingSymmetryQuadrupleAction g q ((fun (i : Fin (3 : ℕ)) => if
            BandPackingSymmetryReversesOrientation g = true then -i else i) i + (1 : Fin (3 :
            ℕ))).succ) = e * if BandPackingSymmetryReversesOrientation g = true then
            -GaussianQuarterTurn cyclic.2 else cyclic.2) → ((TileOdometer
            (BandPackingSymmetryCircleAction g (q (0 : Fin (4 : ℕ))))
            (BandPackingSymmetryTileAction g T) (BandPackingSymmetryPartialOdometerAction g h)) →
            ((TileOdometer (BandPackingSymmetryCircleAction g (q (0 : Fin (4 : ℕ))))
            (BandPackingSymmetryTileAction g T') (BandPackingSymmetryPartialOdometerAction g h'))
            → ((PartialOdometerSlope (BandPackingSymmetryPartialOdometerAction g h) = some
            (BandPackingSymmetrySlopeAction g T p)) → ((PartialOdometerSlope
            (BandPackingSymmetryPartialOdometerAction g h') = some
            (BandPackingSymmetrySlopeAction g T' p')) → ((∀ (a : BandPackingSymmetry), ∀ (U :
            ProtoTile), ∀ (V : ProtoTile), ∀ (v : GaussianInt), TileCentroid V - TileCentroid U =
            GaussianRealPoint v → TileCentroid (BandPackingSymmetryTileAction a V) - TileCentroid
            (BandPackingSymmetryTileAction a U) = GaussianRealPoint
            (BandPackingSymmetryVectorAction a v)) → ((∀ (j : Fin 3), GaussianRealPoint
            (BandPackingSymmetryVectorAction g (BandVectors.1 (q 0) (q j.succ))) = (if xor
            negative (BandPackingSymmetryReversesOrientation g) = true then (-1 : ℝ) else 1) •
            GaussianRealPoint (BandVectors.1 (BandPackingSymmetryQuadrupleAction g q 0)
            (BandPackingSymmetryQuadrupleAction g q (if BandPackingSymmetryReversesOrientation g
            then -j else j).succ))) → ((∀ (a : BandPackingSymmetry), ∀ (v : GaussianInt),
            BandPackingSymmetryVectorAction a (-v) = -BandPackingSymmetryVectorAction a v) → ((∀
            (a : BandPackingSymmetry), ∀ (v : GaussianInt), ∀ (u : GaussianInt),
            BandPackingSymmetryAffineVectorAction a (-v, -u) =
            -BandPackingSymmetryAffineVectorAction a (v, u)) → ((∀ (z : GaussianInt),
            (GaussianInt.toComplex z).re = (z.re : ℝ)) → ((∀ (z : GaussianInt),
            (GaussianInt.toComplex z).im = (z.im : ℝ)) → ((∀ (a : BandPackingSymmetry), ∀ (U :
            ProtoTile), ∀ (V : ProtoTile), ∀ (x : ℝ × ℝ), ∀ (y : ℝ × ℝ), ∀ (v : GaussianInt), ∀
            (u : GaussianInt), TileCentroid V - TileCentroid U = GaussianRealPoint v → x.1 - y.1
            = (↑u.re : ℝ) → x.2 - y.2 = (↑u.im : ℝ) → (BandPackingSymmetrySlopeAction a V x).1 -
            (BandPackingSymmetrySlopeAction a U y).1 = (↑(BandPackingSymmetryAffineVectorAction a
            (v, u)).2.re : ℝ) ∧ (BandPackingSymmetrySlopeAction a V x).2 -
            (BandPackingSymmetrySlopeAction a U y).2 = (↑(BandPackingSymmetryAffineVectorAction a
            (v, u)).2.im : ℝ)) → (
        let newIndex : Fin 3 :=
          if BandPackingSymmetryReversesOrientation g then -i else i
        (newIndex = (if BandPackingSymmetryReversesOrientation g = true then -i else i)) →
            (((BandVectors.1 (q 0) (q i.succ), BandVectors.2 (q 0) (q i.succ)) =
            (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0)), -GaussianQuarterTurn
            (BandVectors.2 (q i.succ) (q 0)))) → (((↑(BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g q newIndex.succ)).re : ℝ) = (↑(BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q newIndex.succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ)))).im : ℝ)) →
            (((↑(BandVectors.2 (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ)))
            (BandPackingSymmetryQuadrupleAction g q newIndex.succ)).im : ℝ) = -(↑(BandVectors.2
            (BandPackingSymmetryQuadrupleAction g q newIndex.succ)
            (BandPackingSymmetryQuadrupleAction g q (0 : Fin (4 : ℕ)))).re : ℝ)) →
            (((↑(BandPackingSymmetryAffineVectorAction g ((⟨-(BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)))).im, (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))).re⟩ :
            GaussianInt), -(⟨-(BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ)))).im, (BandVectors.2
            (q i.succ) (q (0 : Fin (4 : ℕ)))).re⟩ : GaussianInt))).2.re : ℝ) =
            ((GaussianInt.toComplex : GaussianInt → ℂ) (if BandPackingSymmetryReversesOrientation
            g = true then (⟨-(BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ)
            (q (0 : Fin (4 : ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2.im,
            (BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin (4 :
            ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2.re⟩ : GaussianInt) else
            -(⟨-(BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin (4
            : ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2.im,
            (BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin (4 :
            ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2.re⟩ : GaussianInt))).re) →
            (((↑(BandPackingSymmetryAffineVectorAction g ((⟨-(BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)))).im, (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))).re⟩ :
            GaussianInt), -(⟨-(BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ)))).im, (BandVectors.2
            (q i.succ) (q (0 : Fin (4 : ℕ)))).re⟩ : GaussianInt))).2.im : ℝ) =
            ((GaussianInt.toComplex : GaussianInt → ℂ) (if BandPackingSymmetryReversesOrientation
            g = true then (⟨-(BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ)
            (q (0 : Fin (4 : ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2.im,
            (BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin (4 :
            ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2.re⟩ : GaussianInt) else
            -(⟨-(BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin (4
            : ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2.im,
            (BandPackingSymmetryAffineVectorAction g (BandVectors.1 (q i.succ) (q (0 : Fin (4 :
            ℕ))), BandVectors.2 (q i.succ) (q (0 : Fin (4 : ℕ))))).2.re⟩ : GaussianInt))).im) → (
        let q' := BandPackingSymmetryQuadrupleAction g q
        let sigma : Fin 3 → Fin 3 := fun j =>
          if BandPackingSymmetryReversesOrientation g then -j else j
        let reverses := BandPackingSymmetryReversesOrientation g
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
            (if xor (xor e negative) reverses = true then (1 : ℝ) else -1) •
              GaussianRealPoint
                (BandVectors.1 (q' 0) (q' (sigma i).succ)) ∧
          r'.1 - r.1 =
            (if xor (xor e negative) reverses = true then (1 : ℝ) else -1) *
              (BandVectors.2 (q' 0) (q' (sigma i).succ)).re ∧
          r'.2 - r.2 =
            (if xor (xor e negative) reverses = true then (1 : ℝ) else -1) *
              (BandVectors.2 (q' 0) (q' (sigma i).succ)).im ∧
          (OdometerCompatibility
              (BandPackingSymmetryPartialOdometerAction g h)
              (BandPackingSymmetryPartialOdometerAction g h') ↔
            OdometerCompatibility h h'))))))))))))))))))))))) ) := by
  classical
  intro g q i e T T' h h' p p' hcent hslopeRe hslopeIm negative hphase hvec hOT hOT' hsr hsr'
      centroid_transport vector_sign vector_neg affine_neg real_coord imag_coord slope_transport
      newIndex newIndex_eq oldPair newFlipRe newFlipIm affineRightRe affineRightIm
  have hv := (hvec i).1
  have hvr := congrArg (fun z : GaussianInt => (z.re : ℝ)) hv
  have hvi := congrArg (fun z : GaussianInt => (z.im : ℝ)) hv
  refine ⟨negative, BandPackingSymmetrySlopeAction g T p,
    BandPackingSymmetrySlopeAction g T' p', ?_⟩
  refine ⟨hphase, ?_, ?_, hsr, hsr', ?_, ?_, ?_, ?_⟩
  · simpa [BandPackingSymmetryQuadrupleAction] using hOT
  · simpa [BandPackingSymmetryQuadrupleAction] using hOT'
  · by_cases he : e = true
    · have hc : TileCentroid T' - TileCentroid T =
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)) :=
              RightLatticeTransportGeometry.hcAt631 q i e T T' hcent he
      rw [centroid_transport g T T'
        (BandVectors.1 (q 0) (q i.succ)) hc]
      simpa [he] using vector_sign i
    · have hc : TileCentroid T' - TileCentroid T =
          GaussianRealPoint (-(BandVectors.1 (q 0) (q i.succ))) :=
              RightLatticeTransportGeometry.hcAt637 q i e T T' hcent he
      rw [centroid_transport g T T'
        (-(BandVectors.1 (q 0) (q i.succ))) hc, vector_neg]
      have hh := congrArg Neg.neg (vector_sign i)
      by_cases hn : negative <;>
        by_cases hr : BandPackingSymmetryReversesOrientation g = true
      all_goals simpa [he, hn, hr, GaussianRealPoint] using hh
  · by_cases he : e = true
    · have hc : TileCentroid T' - TileCentroid T =
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)) :=
              RightLatticeTransportGeometry.hcAt647 q i e T T' hcent he
      have hs := slope_transport g T T' p' p
        (BandVectors.1 (q 0) (q i.succ))
        (BandVectors.2 (q 0) (q i.succ)) hc
        (by simpa [he] using hslopeRe) (by simpa [he] using hslopeIm)
      rw [oldPair] at hs
      by_cases hn : negative <;>
        by_cases hr : BandPackingSymmetryReversesOrientation g = true
      all_goals simp only [he, hn, Bool.bne_false, hr, bne_self_eq_false, Bool.false_eq_true,
          ↓reduceIte, Int.reduceNeg, Fin.isValue, GaussianInt.intCast_re, neg_mul, one_mul,
          Bool.bne_true, Bool.not_false] at ⊢
      all_goals simp only [Int.reduceNeg, Fin.isValue, newIndex_eq, hr, Bool.false_eq_true,
          ↓reduceIte, GaussianInt.intCast_re, GaussianInt.intCast_im] at newFlipRe newFlipIm
      all_goals try rw [real_coord] at newFlipRe
      all_goals try rw [imag_coord] at newFlipIm
      all_goals simp only [hn, hr] at hvr hvi
      all_goals norm_num at hvr hvi
      all_goals rw [← GaussianInt.intCast_re] at hvr ⊢
      all_goals rw [← GaussianInt.intCast_im] at hvi
      all_goals simp only [Int.reduceNeg, Fin.isValue, GaussianInt.intCast_re, hr,
          Bool.false_eq_true, ↓reduceIte, map_neg, Complex.neg_re, GaussianInt.re_toComplex,
          Int.cast_neg, GaussianInt.intCast_im, neg_neg, Complex.neg_im,
          GaussianInt.im_toComplex] at affineRightRe affineRightIm
      all_goals rw [← GaussianInt.intCast_re] at affineRightRe
      all_goals rw [← GaussianInt.intCast_im] at affineRightIm
      all_goals rw [real_coord] at hvr affineRightIm
      all_goals rw [imag_coord] at hvi affineRightRe
      all_goals simp only [Int.reduceNeg, GaussianQuarterTurn, Fin.isValue,
          GaussianInt.intCast_re, GaussianInt.intCast_im] at hs
      all_goals rw [real_coord] at hs
      all_goals rw [imag_coord] at hs
      all_goals ring_nf at hs ⊢
      all_goals simp only [real_coord, imag_coord] at newFlipRe newFlipIm
      all_goals linarith only [hs.1, hvr, hvi, newFlipRe, newFlipIm,
          affineRightRe,
        affineRightIm]
    · have hc : TileCentroid T' - TileCentroid T =
          GaussianRealPoint (-(BandVectors.1 (q 0) (q i.succ))) :=
              RightLatticeTransportGeometry.hcAt695 q i e T T' hcent he
      have hs := slope_transport g T T' p' p
        (-(BandVectors.1 (q 0) (q i.succ)))
        (-(BandVectors.2 (q 0) (q i.succ))) hc
        (by simpa [he, GaussianRealPoint] using hslopeRe)
        (by simpa [he, GaussianRealPoint] using hslopeIm)
      rw [affine_neg] at hs
      rw [oldPair] at hs
      norm_num at hs
      by_cases hn : negative <;>
        by_cases hr : BandPackingSymmetryReversesOrientation g = true
      all_goals simp only [he, hn, Bool.bne_true, Bool.not_false, hr, Bool.bne_false,
          ↓reduceIte, Int.reduceNeg, Fin.isValue, Bool.false_eq_true, GaussianInt.intCast_re,
          one_mul, bne_self_eq_false, neg_mul] at ⊢
      all_goals simp only [Int.reduceNeg, Fin.isValue, newIndex_eq, hr, Bool.false_eq_true,
          ↓reduceIte, GaussianInt.intCast_re, GaussianInt.intCast_im] at newFlipRe newFlipIm
      all_goals try rw [real_coord] at newFlipRe
      all_goals try rw [imag_coord] at newFlipIm
      all_goals simp only [hn, hr] at hvr hvi
      all_goals norm_num at hvr hvi
      all_goals rw [← GaussianInt.intCast_re] at hvr ⊢
      all_goals rw [← GaussianInt.intCast_im] at hvi
      all_goals simp only [Int.reduceNeg, Fin.isValue, GaussianInt.intCast_re, hr,
          Bool.false_eq_true, ↓reduceIte, map_neg, Complex.neg_re, GaussianInt.re_toComplex,
          Int.cast_neg, GaussianInt.intCast_im, neg_neg, Complex.neg_im,
          GaussianInt.im_toComplex] at affineRightRe affineRightIm
      all_goals rw [← GaussianInt.intCast_re] at affineRightRe
      all_goals rw [← GaussianInt.intCast_im] at affineRightIm
      all_goals rw [real_coord] at hvr affineRightIm
      all_goals rw [imag_coord] at hvi affineRightRe
      all_goals simp only [GaussianQuarterTurn, Int.reduceNeg, Fin.isValue] at hs
      all_goals rw [real_coord] at hs
      all_goals rw [imag_coord] at hs
      all_goals ring_nf at hs ⊢
      all_goals simp only [real_coord, imag_coord] at newFlipRe newFlipIm
      all_goals linarith only [hs.1, hvr, hvi, newFlipRe, newFlipIm,
          affineRightRe,
        affineRightIm]
  · by_cases he : e = true
    · have hc : TileCentroid T' - TileCentroid T =
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)) :=
              RightLatticeTransportGeometry.hcAt742 q i e T T' hcent he
      have hs := slope_transport g T T' p' p
        (BandVectors.1 (q 0) (q i.succ)) (BandVectors.2 (q 0) (q i.succ)) hc
        (by simpa [he] using hslopeRe) (by simpa [he] using hslopeIm)
      rw [oldPair] at hs
      by_cases hn : negative <;>
        by_cases hr : BandPackingSymmetryReversesOrientation g = true
      all_goals simp only [he, hn, Bool.bne_false, hr, bne_self_eq_false, Bool.false_eq_true,
          ↓reduceIte, Int.reduceNeg, Fin.isValue, GaussianInt.intCast_im, neg_mul, one_mul,
          Bool.bne_true, Bool.not_false] at ⊢
      all_goals simp only [Int.reduceNeg, Fin.isValue, newIndex_eq, hr, Bool.false_eq_true,
          ↓reduceIte, GaussianInt.intCast_re, GaussianInt.intCast_im] at newFlipRe newFlipIm
      all_goals try rw [real_coord] at newFlipRe
      all_goals try rw [imag_coord] at newFlipIm
      all_goals simp only [hn, hr] at hvi
      all_goals simp only [hn, hr] at hvr
      all_goals norm_num at hvi
      all_goals norm_num at hvr
      all_goals rw [← GaussianInt.intCast_im] at ⊢
      all_goals rw [← GaussianInt.intCast_im] at hvi
      all_goals rw [← GaussianInt.intCast_re] at hvr
      all_goals simp only [Int.reduceNeg, Fin.isValue, GaussianInt.intCast_re, hr,
          Bool.false_eq_true, ↓reduceIte, map_neg, Complex.neg_re, GaussianInt.re_toComplex,
          Int.cast_neg, GaussianInt.intCast_im, neg_neg, Complex.neg_im,
          GaussianInt.im_toComplex] at affineRightRe affineRightIm
      all_goals rw [← GaussianInt.intCast_re] at affineRightRe
      all_goals rw [← GaussianInt.intCast_im] at affineRightIm
      all_goals rw [imag_coord] at hvi affineRightRe
      all_goals rw [real_coord] at hvr
      all_goals rw [real_coord] at affineRightIm
      all_goals simp only [Int.reduceNeg, GaussianQuarterTurn, Fin.isValue,
          GaussianInt.intCast_re, GaussianInt.intCast_im] at hs
      all_goals rw [real_coord] at hs
      all_goals rw [imag_coord] at hs
      all_goals ring_nf at hs ⊢
      all_goals simp only [real_coord, imag_coord] at newFlipRe newFlipIm
      all_goals linarith only [hs.2, hvi, hvr, newFlipRe, newFlipIm,
          affineRightRe,
        affineRightIm]
    · have hc : TileCentroid T' - TileCentroid T =
          GaussianRealPoint (-(BandVectors.1 (q 0) (q i.succ))) :=
              RightLatticeTransportGeometry.hcAt785 q i e T T' hcent he
      have hs := slope_transport g T T' p' p
        (-(BandVectors.1 (q 0) (q i.succ)))
        (-(BandVectors.2 (q 0) (q i.succ))) hc
        (by simpa [he, GaussianRealPoint] using hslopeRe)
        (by simpa [he, GaussianRealPoint] using hslopeIm)
      rw [affine_neg] at hs
      rw [oldPair] at hs
      norm_num at hs
      by_cases hn : negative <;>
        by_cases hr : BandPackingSymmetryReversesOrientation g = true
      all_goals simp only [he, hn, Bool.bne_true, Bool.not_false, hr, Bool.bne_false,
          ↓reduceIte, Int.reduceNeg, Fin.isValue, Bool.false_eq_true, GaussianInt.intCast_im,
          one_mul, bne_self_eq_false, neg_mul] at ⊢
      all_goals simp only [Int.reduceNeg, Fin.isValue, newIndex_eq, hr, Bool.false_eq_true,
          ↓reduceIte, GaussianInt.intCast_re, GaussianInt.intCast_im] at newFlipRe newFlipIm
      all_goals try rw [real_coord] at newFlipRe
      all_goals try rw [imag_coord] at newFlipIm
      all_goals simp only [hn, hr] at hvi
      all_goals simp only [hn, hr] at hvr
      all_goals norm_num at hvi
      all_goals norm_num at hvr
      all_goals rw [← GaussianInt.intCast_im] at ⊢
      all_goals rw [← GaussianInt.intCast_im] at hvi
      all_goals rw [← GaussianInt.intCast_re] at hvr
      all_goals simp only [Int.reduceNeg, Fin.isValue, GaussianInt.intCast_re, hr,
          Bool.false_eq_true, ↓reduceIte, map_neg, Complex.neg_re, GaussianInt.re_toComplex,
          Int.cast_neg, GaussianInt.intCast_im, neg_neg, Complex.neg_im,
          GaussianInt.im_toComplex] at affineRightRe affineRightIm
      all_goals rw [← GaussianInt.intCast_re] at affineRightRe
      all_goals rw [← GaussianInt.intCast_im] at affineRightIm
      all_goals rw [imag_coord] at hvi affineRightRe
      all_goals rw [real_coord] at hvr
      all_goals rw [real_coord] at affineRightIm
      all_goals simp only [GaussianQuarterTurn, Int.reduceNeg, Fin.isValue] at hs
      all_goals rw [real_coord] at hs
      all_goals rw [imag_coord] at hs
      all_goals ring_nf at hs ⊢
      all_goals simp only [real_coord, imag_coord] at newFlipRe newFlipIm
      all_goals linarith only [hs.2, hvi, hvr, newFlipRe, newFlipIm,
          affineRightRe,
        affineRightIm]
  · exact (BandPackingSymmetryPartialOdometerActionFormulas g h h').2.2.2.2.2.2.1

end RightAdjacencyAssembly

theorem RightLatticeAdjacentPackingSymmetryTransport
    (g : BandPackingSymmetry) (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) (i : Fin 3) (e : Bool)
    (T T' : ProtoTile) (h h' : PartialOdometer) (p p' : ℝ × ℝ)
    (hO : TileOdometer (q 0) T h) (hO' : TileOdometer (q 0) T' h')
    (hp : PartialOdometerSlope h = some p)
    (hp' : PartialOdometerSlope h' = some p')
    (hcent : TileCentroid T' - TileCentroid T =
      (if e = true then (1 : ℝ) else -1) •
        GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))
    (hslopeRe : p'.1 - p.1 =
      (if e = true then (1 : ℝ) else -1) *
        (BandVectors.2 (q 0) (q i.succ)).re)
    (hslopeIm : p'.2 - p.2 =
      (if e = true then (1 : ℝ) else -1) *
        (BandVectors.2 (q 0) (q i.succ)).im) :
    let q' := BandPackingSymmetryQuadrupleAction g q
    let sigma : Fin 3 → Fin 3 := fun j =>
      if BandPackingSymmetryReversesOrientation g then -j else j
    let reverses := BandPackingSymmetryReversesOrientation g
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
        (if xor (xor e negative) reverses = true then (1 : ℝ) else -1) •
          GaussianRealPoint
            (BandVectors.1 (q' 0) (q' (sigma i).succ)) ∧
      r'.1 - r.1 =
        (if xor (xor e negative) reverses = true then (1 : ℝ) else -1) *
          (BandVectors.2 (q' 0) (q' (sigma i).succ)).re ∧
      r'.2 - r.2 =
        (if xor (xor e negative) reverses = true then (1 : ℝ) else -1) *
          (BandVectors.2 (q' 0) (q' (sigma i).succ)).im ∧
      (OdometerCompatibility
          (BandPackingSymmetryPartialOdometerAction g h)
          (BandPackingSymmetryPartialOdometerAction g h') ↔
        OdometerCompatibility h h') := by
-- BODY
  classical
  dsimp
  obtain ⟨negative, hphase, hvec⟩ :=
    BandPackingSymmetryAffineVectorCovariance g q hq
  have hTne := RightLatticeTransportGeometry.hTne q hq T h p hO hp
  have hT'ne := RightLatticeTransportGeometry.hT'ne q hq T' h' p' hO' hp'
  obtain ⟨hOT, _, hST⟩ := BandPackingSymmetryTileOdometerCovariance g (q 0) T h hO
  obtain ⟨hOT', _, hST'⟩ := BandPackingSymmetryTileOdometerCovariance g (q 0) T' h' hO'
  have hsr := RightLatticeTransportGeometry.hsr g T h p hp hTne hST
  have hsr' := RightLatticeTransportGeometry.hsr' g T' h' p' hp' hT'ne hST'
  have centroid_transport := RightLatticeTransportGeometry.centroid_transport
  have vector_sign (j : Fin 3) := RightLatticeTransportGeometry.vector_signAt246 g q negative
      hphase j
  have vector_neg := RightLatticeTransportGeometry.vector_neg
  have affine_neg := RightLatticeTransportGeometry.affine_neg
  have affine_first (a : BandPackingSymmetry) (v u : GaussianInt) :
      (BandPackingSymmetryAffineVectorAction a (v, u)).1 =
        BandPackingSymmetryVectorAction a v :=
    P5625T1CentroidSlopeDifferenceCovariance.1 a (v, u)
  have real_coord (z : GaussianInt) :
      (GaussianInt.toComplex z).re = (z.re : ℝ) :=
    (GaussianInt.intCast_re z).symm
  have imag_coord (z : GaussianInt) :
      (GaussianInt.toComplex z).im = (z.im : ℝ) :=
    (GaussianInt.intCast_im z).symm
  have slope_transport := RightLatticeTransportGeometry.slope_transport
  have vector_sign (j : Fin 3) := RightLatticeTransportGeometry.vector_signAt350 g q negative
      hphase j
  have vector_flip := RightLatticeTransportGeometry.vector_flip vector_neg
  have affine_flip_second := RightLatticeTransportGeometry.affine_flip_second affine_neg
      affine_first vector_flip
  have hrec := VectorRecursionLaws q hq.1
  have hrec' := VectorRecursionLaws
    (BandPackingSymmetryQuadrupleAction g q)
    (BandPackingSymmetryProperCovariance g q hq).1
  have oldFlip := (hrec.2.2.2.2 hq i).2
  let newIndex : Fin 3 :=
    if BandPackingSymmetryReversesOrientation g then -i else i
  have newIndex_eq := RightLatticeTransportGeometry.newIndex_eq g i
  have newFlip := (hrec'.2.2.2.2
    (BandPackingSymmetryProperCovariance g q hq) newIndex).2
  have oldFlipVec := (hrec.2.2.2.2 hq i).1
  have newFlipVec := (hrec'.2.2.2.2
    (BandPackingSymmetryProperCovariance g q hq) newIndex).1
  have affineRight := affine_flip_second g
    (BandVectors.1 (q i.succ) (q 0))
    (BandVectors.2 (q i.succ) (q 0))
  have oldFlipRe := congrArg (fun z : GaussianInt => (z.re : ℝ)) oldFlip
  have oldFlipIm := congrArg (fun z : GaussianInt => (z.im : ℝ)) oldFlip
  have newFlipRe := congrArg (fun z : GaussianInt => (z.re : ℝ)) newFlip
  have newFlipIm := congrArg (fun z : GaussianInt => (z.im : ℝ)) newFlip
  have turn_mul (z : GaussianInt) := RightLatticeTransportGeometry.turn_mul z
  have neg_turn_mul (z : GaussianInt) := RightLatticeTransportGeometry.neg_turn_mul turn_mul z
  have neg_turn_mul' (z : GaussianInt) := RightLatticeTransportGeometry.neg_turn_mul' z
  have oldPair := RightLatticeTransportGeometry.oldPair q i oldFlip oldFlipVec turn_mul
      neg_turn_mul'
  have oldFlipVecRe := congrArg (fun z : GaussianInt => (z.re : ℝ)) oldFlipVec
  have oldFlipVecIm := congrArg (fun z : GaussianInt => (z.im : ℝ)) oldFlipVec
  have newFlipVecRe := congrArg (fun z : GaussianInt => (z.re : ℝ)) newFlipVec
  have newFlipVecIm := congrArg (fun z : GaussianInt => (z.im : ℝ)) newFlipVec
  have affineRightRe := congrArg (fun z : GaussianInt => (z.re : ℝ)) affineRight
  have affineRightIm := congrArg (fun z : GaussianInt => (z.im : ℝ)) affineRight
  have phaseSlope := (hvec i).2
  have phaseSlopeRe := congrArg (fun z : GaussianInt => (z.re : ℝ)) phaseSlope
  have phaseSlopeIm := congrArg (fun z : GaussianInt => (z.im : ℝ)) phaseSlope
  simp only [Int.reduceNeg, Fin.isValue, GaussianInt.intCast_re, neg_mul, Zsqrtd.re_neg,
      Zsqrtd.re_mul, zero_mul, mul_one, one_mul, zero_add, neg_neg, GaussianInt.intCast_im,
      Zsqrtd.im_neg, Zsqrtd.im_mul, Int.cast_neg] at oldFlipRe oldFlipIm newFlipRe newFlipIm
  simp only [Int.reduceNeg, Fin.isValue, GaussianInt.intCast_re, Zsqrtd.re_mul, zero_mul,
      mul_one, neg_mul, one_mul, zero_add, Int.cast_neg, GaussianInt.intCast_im,
      Zsqrtd.im_mul] at oldFlipVecRe oldFlipVecIm newFlipVecRe newFlipVecIm
  simp only [real_coord, imag_coord] at newFlipRe newFlipIm
  try
  try
  rw [real_coord] at oldFlipVecRe newFlipVecRe
  rw [imag_coord] at oldFlipVecIm newFlipVecIm
  rw [imag_coord] at oldFlipVecRe newFlipVecRe
  rw [real_coord] at oldFlipVecIm newFlipVecIm
  simp only [Int.reduceNeg, GaussianQuarterTurn, Fin.isValue, GaussianInt.intCast_re,
      GaussianInt.intCast_im, mul_ite, mul_neg, ite_mul, neg_mul, one_mul]
      at affineRightRe affineRightIm phaseSlopeRe phaseSlopeIm
  try rw [← GaussianInt.intCast_re] at oldFlipRe
  try
  try rw [← GaussianInt.intCast_re] at affineRightRe
  try rw [← GaussianInt.intCast_re] at phaseSlopeRe
  try rw [← GaussianInt.intCast_im] at oldFlipIm
  try
  try rw [← GaussianInt.intCast_im] at affineRightIm
  try rw [← GaussianInt.intCast_im] at phaseSlopeIm
  try rw [← GaussianInt.intCast_im] at oldFlipRe
  try
  try rw [← GaussianInt.intCast_re] at oldFlipIm
  try
  have transportedAdjacency := RightAdjacencyAssembly.transportedAdjacency g q i e T T' h h' p p'
      hcent hslopeRe hslopeIm negative hphase hvec hOT hOT' hsr hsr' centroid_transport
      vector_sign vector_neg affine_neg real_coord imag_coord slope_transport newIndex_eq oldPair
      newFlipRe newFlipIm affineRightRe affineRightIm
  exact transportedAdjacency


end ApollonianSuperharmonic

end
