/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5625T1CentroidSlopeDifferenceCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryAffineVectorCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerActionFormulas
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetrySlopeAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileOdometerCovariance
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.OdometerCompatibility
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain

-- [TABLET NODE: LeftLatticeAdjacentPackingSymmetryTransport]

/-!
# LeftLatticeAdjacentPackingSymmetryTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LeftLatticeTransportGeometry

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

private theorem vector_sign :
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
      · simp? [BandPackingSymmetryAffineVectorAction, GaussianReflection]
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

private theorem hcAt356 :
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

private theorem hcAt377 :
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

private theorem hscoordAt405 :
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

private theorem hcAt414 :
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

private theorem hcAt435 :
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

private theorem hscoordAt463 :
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
  have hTne := LeftLatticeTransportGeometry.hTne q hq T h p hO hp
  have hT'ne := LeftLatticeTransportGeometry.hT'ne q hq T' h' p' hO' hp'
  obtain ⟨hOT, _, hST⟩ := BandPackingSymmetryTileOdometerCovariance g (q 0) T h hO
  obtain ⟨hOT', _, hST'⟩ := BandPackingSymmetryTileOdometerCovariance g (q 0) T' h' hO'
  have hsr := LeftLatticeTransportGeometry.hsr g T h p hp hTne hST
  have hsr' := LeftLatticeTransportGeometry.hsr' g T' h' p' hp' hT'ne hST'
  have centroid_transport : ∀ (a : BandPackingSymmetry) (U V : ProtoTile)
      (v : GaussianInt),
      TileCentroid V - TileCentroid U = GaussianRealPoint v →
      TileCentroid (BandPackingSymmetryTileAction a V) -
          TileCentroid (BandPackingSymmetryTileAction a U) =
        GaussianRealPoint (BandPackingSymmetryVectorAction a v) :=
            LeftLatticeTransportGeometry.centroid_transport
  have vector_sign (j : Fin 3) :
      GaussianRealPoint (BandPackingSymmetryVectorAction g
        (BandVectors.1 (q j.succ) (q 0))) =
        (if negative then (-1 : ℝ) else 1) •
          GaussianRealPoint
            (BandVectors.1
              (BandPackingSymmetryQuadrupleAction g q
                (if BandPackingSymmetryReversesOrientation g then -j else j).succ)
              (BandPackingSymmetryQuadrupleAction g q 0)) :=
                  LeftLatticeTransportGeometry.vector_sign g q negative hphase j
  have vector_neg : ∀ (a : BandPackingSymmetry) (v : GaussianInt),
      BandPackingSymmetryVectorAction a (-v) =
        -BandPackingSymmetryVectorAction a v := LeftLatticeTransportGeometry.vector_neg
  have affine_neg : ∀ (a : BandPackingSymmetry) (v u : GaussianInt),
      BandPackingSymmetryAffineVectorAction a (-v, -u) =
        -BandPackingSymmetryAffineVectorAction a (v, u) := LeftLatticeTransportGeometry.affine_neg
  have real_coord (z : GaussianInt) :
      (GaussianInt.toComplex z).re = (z.re : ℝ) :=
    (GaussianInt.intCast_re z).symm
  have imag_coord (z : GaussianInt) :
      (GaussianInt.toComplex z).im = (z.im : ℝ) :=
    (GaussianInt.intCast_im z).symm
  have slope_transport := LeftLatticeTransportGeometry.slope_transport
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
              LeftLatticeTransportGeometry.hcAt356 q i e T T' hcent he
      have hs := slope_transport g T T' p' p
        (BandVectors.1 (q i.succ) (q 0))
        (BandVectors.2 (q i.succ) (q 0)) hc
        (by simpa [he] using hslopeRe)
        (by simpa [he] using hslopeIm)
      have hv := (hvec i).1
      have hvr := congrArg (fun z : GaussianInt => (z.re : ℝ)) hv
      by_cases hn : negative
      · simp? [he, hn] at hvr ⊢
        rw [← GaussianInt.intCast_re] at ⊢
        have hcoord := hvr
        try simp only [real_coord] at hcoord
        linarith [hs.1, hcoord]
      · simp? [he, hn] at hvr ⊢
        rw [← GaussianInt.intCast_re] at ⊢
        have hcoord := hvr
        try simp only [real_coord] at hcoord
        linarith [hs.1, hcoord]
    · have hc : TileCentroid T' - TileCentroid T =
          GaussianRealPoint (-(BandVectors.1 (q i.succ) (q 0))) :=
              LeftLatticeTransportGeometry.hcAt377 q i e T T' hcent he
      have hs := slope_transport g T T' p' p
        (-(BandVectors.1 (q i.succ) (q 0)))
        (-(BandVectors.2 (q i.succ) (q 0))) hc
        (by simpa [he, GaussianRealPoint] using hslopeRe)
        (by simpa [he, GaussianRealPoint] using hslopeIm)
      rw [affine_neg] at hs
      have hv := (hvec i).1
      have hvr := congrArg (fun z : GaussianInt => (z.re : ℝ)) hv
      by_cases hn : negative
      · simp? [he, hn] at hvr ⊢
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
      · simp? [he, hn] at hvr ⊢
        try rw [← GaussianInt.intCast_re] at ⊢
        have hcoord := hvr
        try simp only [real_coord] at hcoord
        have hscoord :
            (BandPackingSymmetrySlopeAction g T' p').1 -
                (BandPackingSymmetrySlopeAction g T p).1 =
              -((BandPackingSymmetryAffineVectorAction g
                (BandVectors.1 (q i.succ) (q 0),
                  BandVectors.2 (q i.succ) (q 0))).2.re : ℝ) :=
                      LeftLatticeTransportGeometry.hscoordAt405 g q i T T' p p' hs
        linarith [hscoord, hcoord]
  · by_cases he : e = true
    · have hc : TileCentroid T' - TileCentroid T =
          GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) :=
              LeftLatticeTransportGeometry.hcAt414 q i e T T' hcent he
      have hs := slope_transport g T T' p' p
        (BandVectors.1 (q i.succ) (q 0))
        (BandVectors.2 (q i.succ) (q 0)) hc
        (by simpa [he] using hslopeRe)
        (by simpa [he] using hslopeIm)
      have hv := (hvec i).1
      have hvi := congrArg (fun z : GaussianInt => (z.im : ℝ)) hv
      by_cases hn : negative
      · simp? [he, hn] at hvi ⊢
        rw [← GaussianInt.intCast_im] at ⊢
        have hcoord := hvi
        try simp only [imag_coord] at hcoord
        linarith [hs.2, hcoord]
      · simp? [he, hn] at hvi ⊢
        rw [← GaussianInt.intCast_im] at ⊢
        have hcoord := hvi
        try simp only [imag_coord] at hcoord
        linarith [hs.2, hcoord]
    · have hc : TileCentroid T' - TileCentroid T =
          GaussianRealPoint (-(BandVectors.1 (q i.succ) (q 0))) :=
              LeftLatticeTransportGeometry.hcAt435 q i e T T' hcent he
      have hs := slope_transport g T T' p' p
        (-(BandVectors.1 (q i.succ) (q 0)))
        (-(BandVectors.2 (q i.succ) (q 0))) hc
        (by simpa [he, GaussianRealPoint] using hslopeRe)
        (by simpa [he, GaussianRealPoint] using hslopeIm)
      rw [affine_neg] at hs
      have hv := (hvec i).1
      have hvi := congrArg (fun z : GaussianInt => (z.im : ℝ)) hv
      by_cases hn : negative
      · simp? [he, hn] at hvi ⊢
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
      · simp? [he, hn] at hvi ⊢
        try rw [← GaussianInt.intCast_im] at ⊢
        have hcoord := hvi
        try simp only [imag_coord] at hcoord
        have hscoord :
            (BandPackingSymmetrySlopeAction g T' p').2 -
                (BandPackingSymmetrySlopeAction g T p).2 =
              -((BandPackingSymmetryAffineVectorAction g
                (BandVectors.1 (q i.succ) (q 0),
                  BandVectors.2 (q i.succ) (q 0))).2.im : ℝ) :=
                      LeftLatticeTransportGeometry.hscoordAt463 g q i T T' p p' hs
        linarith [hscoord, hcoord]
  · exact (BandPackingSymmetryPartialOdometerActionFormulas g h h').2.2.2.2.2.2.1

end ApollonianSuperharmonic

end
