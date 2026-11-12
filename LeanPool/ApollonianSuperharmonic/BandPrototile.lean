/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.TileCentroid

-- [TABLET NODE: BandPrototile]

/-!
# BandPrototile

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/--
The relation “$T$ is a band prototile for $C$” is generated recursively as
follows.  A line $(0,\pm1)$ has the empty prototile with any chosen singleton
anchor.  A curvature-one root $(1,1+2z)$ has any singleton cell $\{s_x\}$;
as for every nonempty prototile, its stored anchor is auxiliary and
unrestricted.
For a proper quadruple $(C_0,C_1,C_2,C_3)$, choose two prototiles
$T_i^\pm$ for every parent.  Their union is a prototile $T_0$ when every
parent footprint is contained in the child footprint and, for every cyclic
ordering $(i,j,k)$ of $(1,2,3)$,
$$
 \operatorname{cent}(T_i^\pm)-\operatorname{cent}(T_0)
 =\pm\tfrac12\bigl([v_{kj}]-[iv_{kj}]\bigr).
$$
No disk, symmetry, touching, or tiling conclusion is part of this recursive
definition.
-/
inductive BandPrototile : CircleCoordinates → ProtoTile → Prop where
-- BODY
  | line (w x : GaussianInt) (hw : w = 1 ∨ w = -1) :
      BandPrototile (0, w) ⟨∅, x⟩
  | unit (z x anchor : GaussianInt) :
      BandPrototile (1, 1 + 2 * z) ⟨{x}, anchor⟩
  | decompose {q : Fin 4 → CircleCoordinates} (hq : ProperBandQuadruple q)
      {S : Fin 3 → Bool → ProtoTile} {T : ProtoTile}
      (hS : ∀ i s, BandPrototile (q i.succ) (S i s))
      (hcells : ∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (S i s).cells)
      (hfoot : ∀ i s, FootprintVertices (S i s) ⊆ FootprintVertices T)
      (hcentroid : ∀ i s,
        TileCentroid (S i s) - TileCentroid T =
          (if s = true then (1 : Real) else -1) •
            ((1 / 2 : Real) •
              ((GaussianRealPoint
                  (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
                (-((GaussianRealPoint
                    (BandVectors.1 (q ((i + 2).succ))
                      (q ((i + 1).succ)))).2),
                  (GaussianRealPoint
                    (BandVectors.1 (q ((i + 2).succ))
                      (q ((i + 1).succ)))).1))))) :
      BandPrototile (q 0) T

end ApollonianSuperharmonic

end
