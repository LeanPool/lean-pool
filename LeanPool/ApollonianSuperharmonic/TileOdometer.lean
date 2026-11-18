/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.CurvatureOneOdometer
public import LeanPool.ApollonianSuperharmonic.OdometerCompatibility
public import LeanPool.ApollonianSuperharmonic.OdometerTranslation
public import LeanPool.ApollonianSuperharmonic.PartialOdometerSlope

-- [TABLET NODE: TileOdometer]

/-!
# TileOdometer

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
A partial odometer $h_0$ with domain the footprint of a band prototile
$T_0$ is a tile odometer for $C_0$ when it belongs to the following
recursive family.

If $C_0=(0,\pm1)$, then $T_0$ is the empty prototile with an assigned
anchor $x$, the domain of $h_0$ is the singleton $\{x\}$, and its sole
value is arbitrary.  No slope is assigned in this case.

If $C_0=(1,1+2z)$, then $T_0$ is a single unit cell (with arbitrary
auxiliary anchor) and $h_0$ is an
odometer translation, in the sense of `OdometerTranslation`, of
the standard four-vertex function `CurvatureOneOdometer`.

Finally, suppose $(C_0,C_1,C_2,C_3)$ is proper and $T_0$ is a
`BandPrototile` for $C_0$.  Choose the six recursively constructed
parent prototiles and tile odometers $h_i^\pm$ appearing in its six-piece
decomposition.  Their footprints
cover the footprint of $T_0$, their values agree with $h_0$ wherever they
are defined, and they are pairwise compatible in the sense of
`OdometerCompatibility`.  For every cyclic ordering $(i,j,k)$ of
$(1,2,3)$ their centroids satisfy
$$
 \operatorname{cent}(T_i^\pm)-\operatorname{cent}(T_0)
 =\pm\tfrac12(v_{kj}-iv_{kj}).
$$
When $c_i>0$, both slopes are defined and
$$
 \operatorname{slope}(h_i^\pm)-\operatorname{slope}(h_0)
 =\pm\tfrac12(a_{kj}+ia_{kj}).
$$
When $c_i=0$ this slope clause is replaced by the zero-curvature
alternative, so it never extracts a slope from a singleton.  The six
$h_i^\pm$ are the immediate subodometers of this displayed decomposition.
-/
inductive TileOdometer : CircleCoordinates → ProtoTile → PartialOdometer → Prop where
-- BODY
  | line (w x : GaussianInt) (hw : w = 1 ∨ w = -1)
      (h : PartialOdometer) (hdom : h.domain = {x}) :
      TileOdometer (0, w) ⟨∅, x⟩ h
  | unit (z x : GaussianInt) (T : ProtoTile) (h : PartialOdometer)
      (hT : T.cells = {x})
      (hdom : (h.domain : Set GaussianInt) = FootprintVertices T)
      (htrans : OdometerTranslation h (CurvatureOneOdometer z)) :
      TileOdometer (1, 1 + 2 * z) T h
  | decompose {q : Fin 4 → CircleCoordinates} (hq : ProperBandQuadruple q)
      {S : Fin 3 → Bool → ProtoTile} {T : ProtoTile}
      {hs : Fin 3 → Bool → PartialOdometer} {h : PartialOdometer}
      (hT : BandPrototile (q 0) T)
      (hsub : ∀ i s, TileOdometer (q i.succ) (S i s) (hs i s))
      (hcells : ∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (S i s).cells)
      (hfoot : ∀ i s, FootprintVertices (S i s) ⊆ FootprintVertices T)
      (hcentroid : ∀ i s,
        TileCentroid (S i s) - TileCentroid T =
          (if s = true then (1 : Real) else -1) •
            ((1 / 2 : Real) •
              (GaussianRealPoint
                  (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
                (-((GaussianRealPoint
                    (BandVectors.1 (q ((i + 2).succ))
                      (q ((i + 1).succ)))).2),
                  (GaussianRealPoint
                    (BandVectors.1 (q ((i + 2).succ))
                      (q ((i + 1).succ)))).1))))
      (hdom : ∀ x, x ∈ h.domain ↔ ∃ i s, x ∈ (hs i s).domain)
      (hvalue : ∀ i s x, x ∈ (hs i s).domain → h.value x = (hs i s).value x)
      (hcompat : ∀ i s j t, OdometerCompatibility (hs i s) (hs j t))
      (hslope : ∀ i s, (q i.succ).1 = 0 ∨
        ∃ p p_i : ℝ × ℝ,
          PartialOdometerSlope h = some p ∧
          PartialOdometerSlope (hs i s) = some p_i ∧
          p_i.1 - p.1 =
            (if s = true then (1 : ℝ) else -1) * (1 / 2) *
              (((BandVectors.2 (q ((i + 2).succ))
                (q ((i + 1).succ))).re : ℤ) -
               ((BandVectors.2 (q ((i + 2).succ))
                (q ((i + 1).succ))).im : ℤ)) ∧
          p_i.2 - p.2 =
            (if s = true then (1 : ℝ) else -1) * (1 / 2) *
              (((BandVectors.2 (q ((i + 2).succ))
                (q ((i + 1).succ))).im : ℤ) +
               ((BandVectors.2 (q ((i + 2).succ))
                (q ((i + 1).succ))).re : ℤ))) :
      TileOdometer (q 0) T h

end ApollonianSuperharmonic

end
