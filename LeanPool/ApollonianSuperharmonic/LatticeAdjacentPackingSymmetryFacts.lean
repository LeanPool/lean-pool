/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.P5625T1CentroidSlopeDifferenceCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileOdometerCovariance
public import LeanPool.ApollonianSuperharmonic.TileOdometerDomain

/-!
# Shared packing-symmetry transport facts

Adapted from Wesley Pegden's Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LatticeAdjacentPackingSymmetryFacts

/-- A tile odometer with a defined slope has a nonempty tile. -/
theorem tileCellsNonempty (c : CircleCoordinates) (T : ProtoTile)
    (h : PartialOdometer) (p : ℝ × ℝ) (hO : TileOdometer c T h)
    (hp : PartialOdometerSlope h = some p) : T.cells.Nonempty := by
  classical
  have hd := TileOdometerDomain c T h hO
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


/-- The slope action preserves a specified slope on a nonempty tile. -/
theorem slopeAction :
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

/-- Packing symmetry transports a centroid difference. -/
theorem centroidTransport :
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

/-- Scoped phase determines the transported parent vector. -/
theorem vectorSign :
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

/-- The vector action commutes with negation. -/
theorem vectorNegation :
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

/-- The affine vector action commutes with simultaneous negation. -/
theorem affineNegation :
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

/-- Packing symmetry transports a slope difference. -/
theorem slopeTransport :
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

end LatticeAdjacentPackingSymmetryFacts

end ApollonianSuperharmonic

end
